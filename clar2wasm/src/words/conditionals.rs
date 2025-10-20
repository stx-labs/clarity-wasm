use clarity::vm::types::{FixedFunction, FunctionType, TypeSignature};
use clarity::vm::{ClarityName, SymbolicExpression};
use walrus::ir::{self, Block, IfElse, Loop, UnaryOp};
use walrus::{InstrSeqBuilder, LocalId, ValType};

use super::{ComplexWord, SimpleWord, Word};
use crate::cost::WordCharge;
use crate::error_mapping::ErrorMap;
use crate::wasm_generator::{
    add_placeholder_for_clarity_type, drop_value, ArgumentsExt, GeneratorError,
    SequenceElementType, WasmGenerator,
};
use crate::wasm_utils::{check_argument_count, ArgumentCountCheck};
use crate::{check_args, words};

/// Handles Wasm values that can be short-returned in functions such as
/// `try!`, `asserts!`, or `unwrap!`.
enum ShortReturnable<'a> {
    /// Inner value of a wasm optional
    Optional {
        inner_type: &'a TypeSignature,
        value: Vec<LocalId>,
    },
    /// Inner values of a wasm response
    Response {
        err_type: &'a TypeSignature,
        ok_value: Vec<LocalId>,
        err_value: Vec<LocalId>,
    },
    /// Any kind of value in Wasm
    Any {
        ty: &'a TypeSignature,
        value: Vec<LocalId>,
        err_kind: ErrorMap,
    },
}

impl<'a> ShortReturnable<'a> {
    /// Creates a handler for an optional or a response that could be short-returned.
    ///
    /// Returns the local containing the variant of the optional or response.
    fn new(
        generator: &mut WasmGenerator,
        builder: &mut InstrSeqBuilder,
        ty: &'a TypeSignature,
    ) -> Result<(Self, LocalId), GeneratorError> {
        match ty {
            TypeSignature::OptionalType(opt) => {
                let value = generator.save_to_locals(builder, opt, true);
                let variant = generator.module.locals.add(ValType::I32);
                builder.local_set(variant);
                Ok((
                    Self::Optional {
                        inner_type: opt,
                        value,
                    },
                    variant,
                ))
            }
            TypeSignature::ResponseType(resp) => {
                let (ok_type, err_type) = resp.as_ref();
                let err_value = generator.save_to_locals(builder, err_type, true);
                let ok_value = generator.save_to_locals(builder, ok_type, true);
                let variant = generator.module.locals.add(ValType::I32);
                builder.local_set(variant);
                Ok((
                    Self::Response {
                        err_type,
                        ok_value,
                        err_value,
                    },
                    variant,
                ))
            }
            _ => Err(GeneratorError::TypeError(format!(
                "Invalid type for assertion: {ty}"
            ))),
        }
    }

    /// Creates a handler for any value that could be short-returned.
    ///
    /// Takes as an argument the kind of [ErrorMap] that should be returned at short-return.
    /// It should be one of [ErrorMap::ShortReturnAssertionFailure],
    /// [ErrorMap::ShortReturnExpectedValue], [ErrorMap::ShortReturnExpectedValueResponse]
    /// or [ErrorMap::ShortReturnExpectedValueOptional].
    fn new_any(
        generator: &mut WasmGenerator,
        builder: &mut InstrSeqBuilder,
        ty: &'a TypeSignature,
        err_kind: ErrorMap,
    ) -> Self {
        let value = generator.save_to_locals(builder, ty, true);
        Self::Any {
            ty,
            value,
            err_kind,
        }
    }

    /// Push a value onto the stack:
    ///
    /// - the value inside `some` for an optional
    /// - the value inside `ok` for a response
    /// - the whole value otherwise
    fn push_success_value(&self, builder: &mut InstrSeqBuilder) {
        match self {
            ShortReturnable::Optional { value, .. } => value.iter().for_each(|&l| {
                builder.local_get(l);
            }),
            ShortReturnable::Response { ok_value, .. } => ok_value.iter().for_each(|&l| {
                builder.local_get(l);
            }),
            ShortReturnable::Any { value, .. } => value.iter().for_each(|&l| {
                builder.local_get(l);
            }),
        }
    }

    /// Push the value contained inside the `err` of a response.
    ///
    /// Can fail if we don't have a response.
    fn push_err_value(&self, builder: &mut InstrSeqBuilder) -> Result<(), GeneratorError> {
        if let ShortReturnable::Response { err_value, .. } = self {
            err_value.iter().for_each(|&l| {
                builder.local_get(l);
            });
            Ok(())
        } else {
            Err(GeneratorError::TypeError("Expected a response".to_owned()))
        }
    }

    /// Generates the handling of a ShortReturn error.
    fn handle_short_return(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut InstrSeqBuilder,
        condition: impl FnMut(&mut InstrSeqBuilder),
    ) -> Result<(), GeneratorError> {
        match generator.get_current_function_return_type() {
            Some(return_ty) => {
                self.handle_short_return_function(generator, builder, return_ty, condition)
            }
            None => self.handle_short_return_top_level(generator, builder, condition),
        }
    }

    /// Generates the handling of a ShortReturn error when we are not in a function.
    ///
    /// This is part of [ShortReturnable::handle_short_return] and shouldn't be used directly.
    fn handle_short_return_top_level(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut InstrSeqBuilder,
        mut condition: impl FnMut(&mut InstrSeqBuilder),
    ) -> Result<(), GeneratorError> {
        let short_return_id = {
            let mut sr = builder.dangling_instr_seq(None);
            match self {
                // for an optional, nothing to do but short-return.
                ShortReturnable::Optional { inner_type, .. } => {
                    generator.short_return_error(
                        &mut sr,
                        inner_type,
                        ErrorMap::ShortReturnExpectedValueOptional,
                    )?;
                }
                // for a response, we need to push the value inside `err` to the stack then short-return.
                ShortReturnable::Response {
                    err_type,
                    err_value,
                    ..
                } => {
                    for &l in err_value {
                        sr.local_get(l);
                    }
                    generator.short_return_error(
                        &mut sr,
                        err_type,
                        ErrorMap::ShortReturnExpectedValueResponse,
                    )?;
                }
                // for any other value, we push it to the stack then short-return.
                ShortReturnable::Any {
                    ty,
                    value,
                    err_kind,
                } => {
                    for &l in value {
                        sr.local_get(l);
                    }
                    generator.short_return_error(&mut sr, ty, *err_kind)?;
                }
            }
            sr.id()
        };

        let empty_id = builder.dangling_instr_seq(None).id();

        condition(builder);
        builder.instr(IfElse {
            consequent: short_return_id,
            alternative: empty_id,
        });

        Ok(())
    }

    /// Generates the handling of a ShortReturn error when we are in a function.
    ///
    /// This is part of [ShortReturnable::handle_short_return] and shouldn't be used directly.
    fn handle_short_return_function(
        &self,
        generator: &WasmGenerator,
        builder: &mut InstrSeqBuilder,
        expected_type: &TypeSignature,
        mut condition: impl FnMut(&mut InstrSeqBuilder),
    ) -> Result<(), GeneratorError> {
        match self {
            // for an optional, we need to push the full value to the stack
            ShortReturnable::Optional { inner_type, .. } => {
                builder.i32_const(0);
                add_placeholder_for_clarity_type(builder, inner_type);
            }
            // for a response, we need to create the full value:
            // - 0 for err
            // - a placeholder for the ok value with the type of the function return type
            // - the err value
            ShortReturnable::Response { err_value, .. } => {
                builder.i32_const(0);
                let TypeSignature::ResponseType(expected_resp) = expected_type else {
                    return Err(GeneratorError::TypeError(format!(
                        "Expected Response type in assertion, got {expected_type}"
                    )));
                };
                let (expected_ok_type, _expected_err_type) = expected_resp.as_ref();
                add_placeholder_for_clarity_type(builder, expected_ok_type);
                for &l in err_value {
                    builder.local_get(l);
                }
            }
            // for any value, we just push the value on the stack
            Self::Any { value, .. } => {
                for &l in value {
                    builder.local_get(l);
                }
            }
        }

        let early_return_block_id = generator.early_return_block_id.ok_or_else(|| {
            GeneratorError::InternalError(
                "Expected a block id for returning after an assertion".to_owned(),
            )
        })?;

        // we check if we should short-return, and if yes we br_if to the current early-return block id.
        condition(builder);
        builder.br_if(early_return_block_id);

        // if we didn't short return, we need to drop the value that was pushed to the stack.
        drop_value(builder, expected_type);

        Ok(())
    }
}

#[derive(Debug)]
pub struct If;

impl Word for If {
    fn name(&self) -> ClarityName {
        "if".into()
    }
}

impl ComplexWord for If {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 3, args.len(), ArgumentCountCheck::Exact);

        self.charge(generator, builder, 0)?;

        let conditional = args.get_expr(0)?;
        let true_branch = args.get_expr(1)?;
        let false_branch = args.get_expr(2)?;

        // WORKAROUND: have to set the expression result type to the true and false branch
        let expr_ty = generator
            .get_expr_type(expr)
            .ok_or_else(|| GeneratorError::TypeError("if expression must be typed".to_owned()))?
            .clone();
        generator.set_expr_type(true_branch, expr_ty.clone())?;
        generator.set_expr_type(false_branch, expr_ty)?;

        let id_true = generator.block_from_expr(builder, true_branch)?;
        let id_false = generator.block_from_expr(builder, false_branch)?;

        generator.traverse_expr(builder, conditional)?;

        builder.instr(ir::IfElse {
            consequent: id_true,
            alternative: id_false,
        });

        Ok(())
    }
}

#[derive(Debug)]
pub struct Match;

impl Word for Match {
    fn name(&self) -> ClarityName {
        "match".into()
    }
}

impl ComplexWord for Match {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        self.charge(generator, builder, 0)?;

        // WORKAROUND: we'll have to set the types of arguments to the type of expression,
        //             since the typechecker didn't do it for us
        let expr_ty = generator
            .get_expr_type(_expr)
            .ok_or_else(|| {
                GeneratorError::TypeError("match expression should have a type".to_owned())
            })?
            .clone();

        let match_on = args.get_expr(0)?;
        let success_binding = args.get_name(1)?;

        if generator.is_reserved_name(success_binding) {
            return Err(GeneratorError::InternalError(format!(
                "Name already used {success_binding:?}"
            )));
        }

        let success_body = args.get_expr(2)?;
        // WORKAROND: type set on some/ok body
        generator.set_expr_type(success_body, expr_ty.clone())?;

        // save the current set of named locals, for later restoration
        let saved_bindings = generator.bindings.clone();

        generator.traverse_expr(builder, match_on)?;

        match generator.get_expr_type(match_on).cloned() {
            Some(TypeSignature::OptionalType(inner_type)) => {
                check_args!(generator, builder, 4, args.len(), ArgumentCountCheck::Exact);

                let none_body = args.get_expr(3)?;

                // WORKAROUND: set type on none body
                generator.set_expr_type(none_body, expr_ty)?;

                let some_locals = generator.save_to_locals(builder, &inner_type, true);

                generator
                    .bindings
                    .insert(success_binding.clone(), *inner_type, some_locals);

                let some_block = generator.block_from_expr(builder, success_body)?;

                // we can restore early, since the none branch does not bind anything
                generator.bindings = saved_bindings;

                let none_block = generator.block_from_expr(builder, none_body)?;

                builder.instr(ir::IfElse {
                    consequent: some_block,
                    alternative: none_block,
                });

                Ok(())
            }
            Some(TypeSignature::ResponseType(inner_types)) => {
                check_args!(generator, builder, 5, args.len(), ArgumentCountCheck::Exact);

                let (ok_ty, err_ty) = &*inner_types;

                let err_binding = args.get_name(3)?;

                if generator.is_reserved_name(err_binding) {
                    return Err(GeneratorError::InternalError(format!(
                        "Name already used {err_binding:?}"
                    )));
                }

                let err_body = args.get_expr(4)?;
                // Workaround: set type on err body
                generator.set_expr_type(err_body, expr_ty)?;

                let err_locals = generator.save_to_locals(builder, err_ty, true);
                let ok_locals = generator.save_to_locals(builder, ok_ty, true);

                generator
                    .bindings
                    .insert(success_binding.clone(), ok_ty.clone(), ok_locals);
                let ok_block = generator.block_from_expr(builder, success_body)?;

                // restore named locals
                generator.bindings.clone_from(&saved_bindings);

                // bind err branch local
                generator
                    .bindings
                    .insert(err_binding.clone(), err_ty.clone(), err_locals);

                let err_block = generator.block_from_expr(builder, err_body)?;

                // restore named locals again
                generator.bindings = saved_bindings;

                builder.instr(ir::IfElse {
                    consequent: ok_block,
                    alternative: err_block,
                });

                Ok(())
            }
            _ => Err(GeneratorError::TypeError("Invalid type for match".into())),
        }
    }
}

#[derive(Debug)]
pub struct Filter;

impl Word for Filter {
    fn name(&self) -> ClarityName {
        "filter".into()
    }
}

impl ComplexWord for Filter {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 2, args.len(), ArgumentCountCheck::Exact);
        self.charge(generator, builder, 0)?;

        let memory = generator.get_memory()?;

        let discriminator = args.get_name(0)?;
        let sequence = args.get_expr(1)?;

        let expr_ty = generator
            .get_expr_type(expr)
            .ok_or_else(|| GeneratorError::TypeError("filter expression must be typed".to_owned()))?
            .clone();
        generator.set_expr_type(sequence, expr_ty)?;

        generator.traverse_expr(builder, sequence)?;

        // Get the type of the sequence
        let ty = generator
            .get_expr_type(sequence)
            .ok_or_else(|| {
                GeneratorError::TypeError("sequence expression must be typed".to_owned())
            })?
            .clone();

        let elem_ty = generator.get_sequence_element_type(sequence)?;

        // Setup neccesary locals for the operations.
        let input_len = generator.module.locals.add(ValType::I32);
        let input_offset = generator.module.locals.add(ValType::I32);
        let output_len = generator.module.locals.add(ValType::I32);

        // save list (offset, length) to locals
        builder.local_set(input_len).local_set(input_offset);

        // reserve space for the output list
        let (output_offset, _) = generator.create_call_stack_local(builder, &ty, false, true);

        let mut loop_ = builder.dangling_instr_seq(None);
        let loop_id = loop_.id();

        // Load an element from the sequence
        let elem_size = match &elem_ty {
            SequenceElementType::Other(elem_ty) => {
                generator.read_from_memory(&mut loop_, input_offset, 0, elem_ty)?
            }
            SequenceElementType::Byte => {
                // The element type is a byte, so we can just push the
                // offset and length (1) to the stack.
                loop_.local_get(input_offset).i32_const(1);
                1
            }
            SequenceElementType::UnicodeScalar => {
                // The element type is a 32-bit unicode scalar, so we can just push the
                // offset and length (4) to the stack.
                loop_.local_get(input_offset).i32_const(4);
                4
            }
        };

        if let Some(simple) = words::lookup_simple(discriminator) {
            // Call simple builtin
            simple.visit(
                generator,
                &mut loop_,
                &[TypeSignature::BoolType],
                &TypeSignature::BoolType,
            )?;
        } else {
            // In the case of a user defined function for a list element, we need to support the case where
            // the discriminant argument is more complete than the type of the list elements.
            // e.g:
            // ```
            // (define-private (foo (a (response int bool))) (and (is-ok a) (< (unwrap-panic a) 100)))
            // (filter foo (list (ok 1) (ok 2)))
            // ```
            // The function expects a `response int bool` but the type of the element is `response int UNKNOWN`.
            // This is something we can't fix with a regulare "workaround" since the type of the expression is identical
            // to the type of the sequence.
            if let SequenceElementType::Other(list_elem_ty) = &elem_ty {
                let arg_ty = match generator
                    .get_function_type(discriminator.as_str())
                    .ok_or_else(|| {
                        GeneratorError::InternalError(format!(
                            "Couldn't find discriminant function {discriminator} for filter"
                        ))
                    })? {
                    FunctionType::Fixed(FixedFunction { args, .. }) if args.len() == 1 => {
                        args[0].signature.clone()
                    }
                    _ => {
                        return Err(GeneratorError::TypeError(
                            "Invalid function type for a filter discriminant".to_owned(),
                        ))
                    }
                };
                generator.duck_type(&mut loop_, list_elem_ty, &arg_ty)?;
            }
            loop_.call(generator.func_by_name(discriminator.as_str()));
        }
        // [ Discriminator result (bool) ]

        loop_.if_else(
            None,
            |then| {
                // copy value to result sequence
                then.local_get(output_offset)
                    .local_get(output_len)
                    .binop(ir::BinaryOp::I32Add)
                    .local_get(input_offset)
                    .i32_const(elem_size)
                    .memory_copy(memory, memory);

                // increment the size of result sequence
                then.local_get(output_len)
                    .i32_const(elem_size)
                    .binop(ir::BinaryOp::I32Add)
                    .local_set(output_len);
            },
            |_else| {},
        );

        // increment offset, leaving the new offset on the stack for the end check
        loop_
            .local_get(input_offset)
            .i32_const(elem_size)
            .binop(ir::BinaryOp::I32Add)
            .local_set(input_offset);

        // Loop if we haven't reached the end of the sequence
        loop_
            .local_get(input_len)
            .i32_const(elem_size)
            .binop(ir::BinaryOp::I32Sub)
            .local_tee(input_len)
            .br_if(loop_id);

        builder.instr(Loop { seq: loop_id });

        builder.local_get(output_offset);
        builder.local_get(output_len);

        Ok(())
    }
}

/// Default implementation for `and` that handles the evaluation of its arguments.
#[derive(Debug)]
pub struct And;

impl Word for And {
    fn name(&self) -> ClarityName {
        "and".into()
    }
}

impl ComplexWord for And {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        let args_len = args.len();

        check_args!(generator, builder, 1, args_len, ArgumentCountCheck::AtLeast);

        self.charge(generator, builder, args_len as u32)?;

        let block_id = {
            let mut block = builder.dangling_instr_seq(ValType::I32);
            let block_id = block.id();

            // we push a false on the stack for the case where we break early
            block.i32_const(0);

            for arg in args {
                generator.traverse_expr(&mut block, arg)?;
                // if argument is false, we break early
                block.unop(UnaryOp::I32Eqz).br_if(block_id);
            }

            // if we reach this point, result is true, so we drop the current false on the stack and push true.
            block.drop().i32_const(1);

            block_id
        };

        builder.instr(Block { seq: block_id });

        Ok(())
    }
}

/// Implementation of `and` that doesn't evaluate its arguments.
/// This version of `and` is a variadic word.
///
/// An example of usage would be in `(map and (list true) (list false))`.
/// Since both lists are already evaluated, the `and` cannot re-evaluate its arguments.
#[derive(Debug)]
pub struct SimpleAnd;

impl Word for SimpleAnd {
    fn name(&self) -> ClarityName {
        "and".into()
    }
}

impl SimpleWord for SimpleAnd {
    fn visit(
        &self,
        _generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        arg_types: &[TypeSignature],
        _return_type: &TypeSignature,
    ) -> Result<(), GeneratorError> {
        if arg_types.len() > 1 {
            builder.binop(ir::BinaryOp::I32And);
        }

        Ok(())
    }
}

/// Default implementation for `or` that handles the evaluation of its arguments.
#[derive(Debug)]
pub struct Or;

impl Word for Or {
    fn name(&self) -> ClarityName {
        "or".into()
    }
}

impl ComplexWord for Or {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        let args_len = args.len();

        check_args!(generator, builder, 1, args_len, ArgumentCountCheck::AtLeast);

        self.charge(generator, builder, args_len as u32)?;

        let block_id = {
            let mut block = builder.dangling_instr_seq(ValType::I32);
            let block_id = block.id();

            // we push a true on the stack for the case where we break early
            block.i32_const(1);

            for arg in args {
                generator.traverse_expr(&mut block, arg)?;
                // if argument is true, we break early
                block.br_if(block_id);
            }

            // if we reach this point, result is false, so we drop the current true on the stack and push true.
            block.drop().i32_const(0);

            block_id
        };

        builder.instr(Block { seq: block_id });

        Ok(())
    }
}

/// Implementation of `or` that doesn't evaluate its arguments.
/// This version of `or` is a variadic word.
///
/// An example of usage would be in `(map or (list true) (list false))`.
/// Since both lists are already evaluated, the `or` cannot re-evaluate its arguments.
#[derive(Debug)]
pub struct SimpleOr;

impl Word for SimpleOr {
    fn name(&self) -> ClarityName {
        "or".into()
    }
}

impl SimpleWord for SimpleOr {
    fn visit(
        &self,
        _generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        arg_types: &[TypeSignature],
        _return_type: &TypeSignature,
    ) -> Result<(), GeneratorError> {
        if arg_types.len() > 1 {
            builder.binop(ir::BinaryOp::I32Or);
        }

        Ok(())
    }
}

#[derive(Debug)]
pub struct Unwrap;

impl Word for Unwrap {
    fn name(&self) -> ClarityName {
        "unwrap!".into()
    }
}

impl ComplexWord for Unwrap {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 2, args.len(), ArgumentCountCheck::Exact);

        self.charge(generator, builder, 0)?;

        let expr_ty = generator
            .get_expr_type(expr)
            .ok_or_else(|| {
                GeneratorError::TypeError("Unwrap expression should have a type".to_owned())
            })
            .cloned()?;

        let input = args.get_expr(0)?;
        let throw = args.get_expr(1)?;

        // we need a workaround for the input: we need to make sure that the `some` or `ok` value
        // will have the same type as the type of the whole expression.
        let input_ty = match generator.get_expr_type(input).ok_or_else(|| {
            GeneratorError::TypeError("Input value for unwrap! should be typed".to_owned())
        })? {
            TypeSignature::OptionalType(_) => TypeSignature::OptionalType(Box::new(expr_ty)),
            TypeSignature::ResponseType(resp) => {
                TypeSignature::ResponseType(Box::new((expr_ty, resp.as_ref().1.clone())))
            }
            _ => {
                return Err(GeneratorError::TypeError(
                    "Unwrap expects an optional or response input".to_owned(),
                ))
            }
        };
        generator.set_expr_type(input, input_ty.clone())?;

        // if we are in a function, we should make sure the thrown value is the same type as the return type.
        if let Some(ty) = generator.get_current_function_return_type().cloned() {
            generator.set_expr_type(throw, ty)?;
        }
        let throw_ty = generator
            .get_expr_type(throw)
            .ok_or_else(|| {
                GeneratorError::TypeError("Thrown value for unwrap! should be typed".to_owned())
            })
            .cloned()?;

        generator.traverse_expr(builder, input)?;

        // we save the input as a short-returnable by convenience: we have accesse to [ShortReturnable::push_success_value]
        let (short_returnable_input, variant) =
            ShortReturnable::new(generator, builder, &input_ty)?;

        generator.traverse_expr(builder, throw)?;

        // we save the thrown value as a short returnable and handle a short-return
        let short_returnable_throw = ShortReturnable::new_any(
            generator,
            builder,
            &throw_ty,
            ErrorMap::ShortReturnExpectedValue,
        );

        short_returnable_throw.handle_short_return(generator, builder, |instrs| {
            // we need to short-return if the variant is `none` or `err`
            instrs.local_get(variant).unop(UnaryOp::I32Eqz);
        })?;

        // if we didn't short-return, we push the inner value of the input.
        short_returnable_input.push_success_value(builder);

        Ok(())
    }
}

#[derive(Debug)]
pub struct UnwrapErr;

impl Word for UnwrapErr {
    fn name(&self) -> ClarityName {
        "unwrap-err!".into()
    }
}

impl ComplexWord for UnwrapErr {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 2, args.len(), ArgumentCountCheck::Exact);

        self.charge(generator, builder, 0)?;

        let expr_ty = generator
            .get_expr_type(expr)
            .ok_or_else(|| {
                GeneratorError::TypeError("Unwrap-err expression should have a type".to_owned())
            })
            .cloned()?;

        let input = args.get_expr(0)?;
        let throw = args.get_expr(1)?;

        // we need a workaround for the input: we need to make sure that the `err` value
        // will have the same type as the type of the whole expression.
        let input_ty = match generator.get_expr_type(input).ok_or_else(|| {
            GeneratorError::TypeError("Input value for unwrap-err! should be typed".to_owned())
        })? {
            TypeSignature::ResponseType(resp) => {
                TypeSignature::ResponseType(Box::new((resp.as_ref().0.clone(), expr_ty)))
            }
            _ => {
                return Err(GeneratorError::TypeError(
                    "Unwrap-err expects a response input".to_owned(),
                ))
            }
        };
        generator.set_expr_type(input, input_ty.clone())?;

        // if we are in a function, we should make sure the thrown value is the same type as the return type.
        if let Some(ty) = generator.get_current_function_return_type().cloned() {
            generator.set_expr_type(throw, ty)?;
        }
        let throw_ty = generator
            .get_expr_type(throw)
            .ok_or_else(|| {
                GeneratorError::TypeError("Thrown value for unwrap-err! should be typed".to_owned())
            })
            .cloned()?;

        generator.traverse_expr(builder, input)?;

        // we save the input as a short-returnable by convenience: we have accesse to [ShortReturnable::push_err_value]
        let (short_returnable_input, variant) =
            ShortReturnable::new(generator, builder, &input_ty)?;

        generator.traverse_expr(builder, throw)?;

        // we save the thrown value as a short returnable and handle a short-return
        let short_returnable_throw = ShortReturnable::new_any(
            generator,
            builder,
            &throw_ty,
            ErrorMap::ShortReturnExpectedValue,
        );

        short_returnable_throw.handle_short_return(generator, builder, |instrs| {
            // we need to short-return if the variant is `ok`
            instrs.local_get(variant);
        })?;

        // if we didn't short-return, we push the `err` value of the input.
        short_returnable_input.push_err_value(builder)?;

        Ok(())
    }
}

#[derive(Debug)]
pub struct Asserts;

impl Word for Asserts {
    fn name(&self) -> ClarityName {
        "asserts!".into()
    }
}

impl ComplexWord for Asserts {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 2, args.len(), ArgumentCountCheck::Exact);

        self.charge(generator, builder, 0)?;

        let predicate_expr = args.get_expr(0)?;
        let thrown = args.get_expr(1)?;

        generator.traverse_expr(builder, predicate_expr)?;
        let predicate = generator.module.locals.add(ValType::I32);
        builder.local_set(predicate);

        let thrown_type = generator
            .get_current_function_return_type()
            .or_else(|| generator.get_expr_type(thrown))
            .ok_or_else(|| {
                GeneratorError::TypeError("Thrown value in an asserts! should be typed".to_owned())
            })
            .cloned()?;
        generator.set_expr_type(thrown, thrown_type.clone())?;
        generator.traverse_expr(builder, thrown)?;

        // we save the thrown as a short-returnable, and we handle its short-return.
        let short_returnable_thrown = ShortReturnable::new_any(
            generator,
            builder,
            &thrown_type,
            ErrorMap::ShortReturnAssertionFailure,
        );

        short_returnable_thrown.handle_short_return(generator, builder, |instrs| {
            // we need to short return if predicate is false.
            instrs.local_get(predicate).unop(UnaryOp::I32Eqz);
        })?;

        // if we didn't short-return, the result is always `true`
        builder.i32_const(1);

        Ok(())
    }
}

#[derive(Debug)]
pub struct Try;

impl Word for Try {
    fn name(&self) -> ClarityName {
        "try!".into()
    }
}

impl ComplexWord for Try {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 1, args.len(), ArgumentCountCheck::Exact);

        self.charge(generator, builder, 0)?;

        let input = args.get_expr(0)?;
        let input_ty = generator.get_expr_type(input).cloned().ok_or_else(|| {
            GeneratorError::TypeError("The argument in try! should be typed".to_owned())
        })?;

        generator.traverse_expr(builder, input)?;

        // we save the input as a short-returnable and handle the short-return
        let (short_returnable_value, variant) =
            ShortReturnable::new(generator, builder, &input_ty)?;

        short_returnable_value.handle_short_return(generator, builder, |instrs| {
            // we need to short-return if the variant is `none` or `err`
            instrs.local_get(variant).unop(UnaryOp::I32Eqz);
        })?;

        // if no short-return, we push the success value to the stack.
        short_returnable_value.push_success_value(builder);

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use clarity::vm::errors::{Error, ShortReturnType};
    use clarity::vm::types::ResponseData;
    use clarity::vm::Value;

    use crate::tools::{crosscheck, crosscheck_expect_failure, evaluate};

    #[test]
    fn trivial() {
        crosscheck("true", Ok(Some(Value::Bool(true))));
    }

    #[test]
    fn if_less_than_three_args() {
        let result = evaluate("(if true true)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 3 arguments, got 2"));
    }

    #[test]
    fn if_more_than_three_args() {
        let result = evaluate("(if true true true true)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 3 arguments, got 4"));
    }

    #[test]
    fn what_if() {
        crosscheck("(if true true false)", Ok(Some(Value::Bool(true))));
    }

    #[test]
    fn what_if_complex() {
        crosscheck("(if true (+ 1 1) (+ 2 2))", Ok(Some(Value::Int(2))));
        crosscheck("(if false (+ 1 1) (+ 2 2))", Ok(Some(Value::Int(4))));
    }

    #[test]
    fn what_if_extensive_condition() {
        crosscheck(
            "(if (> 9001 9000) (+ 1 1) (+ 2 2))",
            Ok(Some(Value::Int(2))),
        );
    }

    #[test]
    fn filter_less_than_two_args() {
        let result = evaluate("(filter (x int))");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 1"));
    }

    #[test]
    fn filter_more_than_two_args() {
        let result = evaluate("(filter (x int) (list 1 2 3 4) (list 1 2 3 4))");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 3"));
    }

    #[test]
    fn filter() {
        crosscheck(
            "
(define-private (is-great (number int))
  (> number 2))

(filter is-great (list 1 2 3 4))
",
            evaluate("(list 3 4)"),
        );
    }

    #[test]
    fn filter_builtin() {
        crosscheck(
            "(filter not (list false false true false true true false))",
            evaluate("(list false false false false)"),
        );
    }

    #[test]
    fn filter_responses() {
        let snippet = "
(define-private (is-great (x (response int int)))
  (match x
    number (> number 2)
    number (> number 2)))

(filter is-great
  (list
    (ok 2)
    (ok 3)
    (err 4)
    (err 0)
    (ok -3)))";
        crosscheck(snippet, evaluate("(list (ok 3) (err 4))"));
    }

    #[test]
    fn filter_result_read_only_double_workaround() {
        let snippet = "
(define-read-only (is-even? (x int))
        (is-eq (* (/ x 2) 2) x))

(define-private (grob (x (response int int)))
  (match x
    a (is-even? a)
    b (not (is-even? b))))

(default-to
    (list)
    (some (filter grob (list (err 1) (err 1))))
)";

        crosscheck(snippet, evaluate("(list (err 1) (err 1))"));
    }

    #[test]
    fn filter_buff() {
        crosscheck(
            "
(define-private (is-dash (char (buff 1)))
    (is-eq char 0x2d) ;; -
)
(filter is-dash 0x612d62)",
            Ok(Some(Value::buff_from_byte(0x2d))),
        );
    }

    #[test]
    fn filter_with_different_types_for_predicates() {
        crosscheck(
            "
            (define-private (foo (a (response int bool))) (and (is-ok a) (< (unwrap-panic a) 100)))
            (define-private (bar (a (response int uint))) (and (is-ok a) (> (unwrap-panic a) 42)))

            (filter bar (filter foo (list (ok 1) (ok 50))))
        ",
            Ok(Some(
                Value::cons_list_unsanitized(vec![Value::okay(Value::Int(50)).unwrap()]).unwrap(),
            )),
        );
    }

    #[test]
    fn nested_logical() {
        crosscheck(
            r#"
 (begin (not (or (and true true true) (or true true false false))))
                "#,
            Ok(Some(Value::Bool(false))),
        );
    }

    #[test]
    fn and_less_than_one_arg() {
        let result = evaluate("(and)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting >= 1 arguments, got 0"));
    }

    #[test]
    fn and() {
        crosscheck(
            r#"
(define-data-var cursor int 6)
(and
  (var-set cursor (+ (var-get cursor) 1))
  true
  (var-set cursor (+ (var-get cursor) 1))
  false
  (var-set cursor (+ (var-get cursor) 1)))
(var-get cursor)
                "#,
            evaluate("8"),
        );
    }

    #[test]
    fn or_less_than_one_arg() {
        let result = evaluate("(or)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting >= 1 arguments, got 0"));
    }

    #[test]
    fn or() {
        crosscheck(
            r#"
(define-data-var cursor int 6)
(or
  (begin
    (var-set cursor (+ (var-get cursor) 1))
    false)
  false
  (var-set cursor (+ (var-get cursor) 1))
  (var-set cursor (+ (var-get cursor) 1)))
(var-get cursor)
                "#,
            evaluate("8"),
        );
    }

    #[test]
    fn match_less_than_two_args() {
        crosscheck_expect_failure(
            "
(define-private (add-10 (x (response int int)))
 (match x
   val (+ val 10)
    ))",
        );
    }

    #[test]
    fn match_more_than_five_args() {
        crosscheck_expect_failure(
            "
(define-private (add-10 (x (response int int)))
 (match x
   val (+ val 10)
   error (+ error 107)
   error2
   ))",
        );
    }

    #[test]
    fn clar_match_a() {
        const ADD_10: &str = "
(define-private (add-10 (x (response int int)))
 (match x
   val (+ val 10)
   error (+ error 107)))";

        crosscheck(
            &format!("{ADD_10} (add-10 (ok 115))"),
            Ok(Some(Value::Int(125))),
        );
        crosscheck(
            &format!("{ADD_10} (add-10 (err 18))"),
            Ok(Some(Value::Int(125))),
        );
    }

    #[test]
    fn clar_match_disallow_builtin_names() {
        // It's not allowed to use names of user-defined functions as bindings
        const ERR: &str = "
(define-private (test (x (response int int)))
 (match x
   val (+ val 10)
   err (+ err 107)))";

        crosscheck_expect_failure(&format!("{ERR} (test (err 18))"));
    }

    #[test]
    fn clar_match_cursed() {
        // It's not allowed to use names of user-defined functions as bindings
        const CURSED: &str = "
(define-private (cursed (x (response int int)))
 (match x
   val (+ val 10)
   cursed (+ cursed 107)))";

        crosscheck_expect_failure(&format!("{CURSED} (cursed (err 18))"));
    }

    #[test]
    fn match_optional_less_than_four_args() {
        let result = evaluate("(define-private (add-10 (x (optional int))) (match x val val))");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 4 arguments, got 3"));
    }

    #[test]
    fn match_optional_more_than_four_args() {
        let result =
            evaluate("(define-private (add-10 (x (optional int))) (match x val val 1001 1010))");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 4 arguments, got 5"));
    }

    #[test]
    fn clar_match_b() {
        const ADD_10: &str = "
(define-private (add-10 (x (optional int)))
 (match x
   val val
   1001))";

        crosscheck(
            &format!("{ADD_10} (add-10 none)"),
            Ok(Some(Value::Int(1001))),
        );

        crosscheck(
            &format!("{ADD_10} (add-10 (some 10))"),
            Ok(Some(Value::Int(10))),
        );
    }

    #[test]
    fn unwrap_less_than_two_args() {
        let result = evaluate("(define-private (unwrapper (x (optional int))) (+ (unwrap! x) 10))");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 1"));
    }

    #[test]
    fn unwrap_more_than_two_args() {
        let result =
            evaluate("(define-private (unwrapper (x (optional int))) (+ (unwrap! x 23 23) 10))");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 3"));
    }

    #[test]
    fn unwrap_a() {
        const FN: &str = "
(define-private (unwrapper (x (optional int)))
  (+ (unwrap! x 23) 10))";

        crosscheck(&format!("{FN} (unwrapper none)"), Ok(Some(Value::Int(23))));

        crosscheck(
            &format!("{FN} (unwrapper (some 10))"),
            Ok(Some(Value::Int(20))),
        );
    }

    #[test]
    fn unwrap_b() {
        const FN: &str = "
(define-private (unwrapper (x (response int int)))
  (+ (unwrap! x 23) 10))";

        crosscheck(
            &format!("{FN} (unwrapper (err 9999))"),
            Ok(Some(Value::Int(23))),
        );

        crosscheck(
            &format!("{FN} (unwrapper (ok 10))"),
            Ok(Some(Value::Int(20))),
        );
    }

    #[test]
    fn unwrap_err_less_than_two_args() {
        let result =
            evaluate("(define-private (unwrapper (x (response int int))) (+ (unwrap-err! x) 10))");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 1"));
    }

    #[test]
    fn unwrap_err_more_than_two_args() {
        let result = evaluate(
            "(define-private (unwrapper (x (response int int))) (+ (unwrap-err! x 23 23) 10))",
        );
        assert!(result.is_err());
        let error = result.unwrap_err();
        assert!(error.to_string().contains("expecting 2 arguments, got 3"));
    }

    #[test]
    fn unwrap_err() {
        const FN: &str = "
(define-private (unwrapper (x (response int int)))
  (+ (unwrap-err! x 23) 10))";

        crosscheck(
            &format!("{FN} (unwrapper (err 9999))"),
            Ok(Some(Value::Int(10009))),
        );

        crosscheck(
            &format!("{FN} (unwrapper (ok 10))"),
            Ok(Some(Value::Int(23))),
        );
    }

    /// Verify that the full response type is set correctly for the throw
    /// expression.
    #[test]
    fn response_type_bug() {
        crosscheck(
            "
(define-private (foo)
    (ok u1)
)
(define-read-only (get-count-at-block (block uint))
    (ok (unwrap! (foo) (err u100)))
)
            ",
            Ok(None),
        )
    }

    /// Verify that the full response type is set correctly for the throw
    /// expression.
    #[test]
    fn response_type_err_bug() {
        crosscheck(
            "
(define-private (foo)
    (err u1)
)

(define-read-only (get-count-at-block (block uint))
    (ok (unwrap-err! (foo) (err u100)))
)
            ",
            Ok(None),
        )
    }

    const TRY_FN: &str = "
(define-private (tryhard (x (response int int)))
  (ok (+ (try! x) 10)))";

    #[test]
    fn try_a() {
        assert_eq!(
            evaluate(&format!("{TRY_FN} (tryhard (ok 1))")),
            evaluate("(ok 11)"),
        );
    }

    #[test]
    fn try_b() {
        assert_eq!(
            evaluate(&format!("{TRY_FN} (tryhard (err 1))")),
            evaluate("(err 1)"),
        );
    }

    const TRY_FN2: &str = "
(define-private (tryhard (x (response bool int)))
  (ok (if (try! x) u1 u2))
)";

    #[test]
    fn try_2a() {
        assert_eq!(
            evaluate(&format!("{TRY_FN2} (tryhard (ok true))")),
            evaluate("(ok u1)"),
        );
    }

    #[test]
    fn try_2b() {
        assert_eq!(
            evaluate(&format!("{TRY_FN2} (tryhard (err 1))")),
            evaluate("(err 1)"),
        );
    }

    const TRY_FN_OPT: &str = "
(define-private (tryharder (x (optional int)))
  (some (+ (try! x) 10)))";

    #[test]
    fn try_c() {
        assert_eq!(
            evaluate(&format!("{TRY_FN_OPT} (tryharder (some 1))")),
            evaluate("(some 11)"),
        );
    }

    #[test]
    fn try_d() {
        crosscheck(
            &format!("{TRY_FN_OPT} (tryharder none)"),
            Ok(Some(Value::none())),
        );
    }

    #[test]
    fn try_less_than_one_arg() {
        let result =
            evaluate("(define-private (tryharder (x (optional int))) (some (+ (try!) 10)))");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 1 arguments, got 0"));
    }

    #[test]
    fn try_more_than_one_arg() {
        let result =
            evaluate("(define-private (tryharder (x (optional int))) (some (+ (try! x 23) 10)))");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 1 arguments, got 2"));
    }

    const ASSERT: &str = "
      (define-private (is-even (x int))
        (is-eq (* (/ x 2) 2) x))

      (define-private (assert-even (x int))
        (begin
          (asserts! (is-even x) (+ x 10))
          99))
    ";

    #[test]
    fn asserts_a() {
        crosscheck(
            &format!("{ASSERT} (assert-even 2)"),
            Ok(Some(Value::Int(99))),
        );
    }

    #[test]
    fn asserts_b() {
        crosscheck(
            &format!("{ASSERT} (assert-even 1)"),
            Ok(Some(Value::Int(11))),
        );
    }

    #[test]
    fn asserts_top_level_true() {
        crosscheck("(asserts! true (err u1))", Ok(Some(Value::Bool(true))));
    }

    #[test]
    fn asserts_top_level_false() {
        crosscheck(
            "(asserts! false (err u1))",
            Err(Error::ShortReturn(ShortReturnType::AssertionFailed(
                Box::new(Value::Response(ResponseData {
                    committed: false,
                    data: Box::new(Value::UInt(1)),
                })),
            ))),
        )
    }

    #[test]
    fn asserts_less_than_two_args() {
        let result = evaluate("(asserts! true)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 1"));
    }

    #[test]
    fn asserts_more_than_two_args_false() {
        let result = evaluate("(asserts! true true true)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 3"));
    }

    #[test]
    fn try_response_false() {
        crosscheck(
            "(try! (if false (ok u1) (err u42)))",
            Err(Error::ShortReturn(ShortReturnType::ExpectedValue(
                Box::new(Value::Response(ResponseData {
                    committed: false,
                    data: Box::new(Value::UInt(42)),
                })),
            ))),
        )
    }

    #[test]
    fn try_optional_false() {
        crosscheck(
            "(try! (if false (some u1) none))",
            Err(Error::ShortReturn(ShortReturnType::ExpectedValue(
                Box::new(Value::Optional(clarity::vm::types::OptionalData {
                    data: None,
                })),
            ))),
        )
    }

    #[test]
    fn try_something() {
        let snippet = "(ok (try! (if true (ok true) (err u3))))";

        crosscheck(snippet, Ok(Some(Value::okay_true())));
    }

    #[test]
    fn try_something_begin() {
        let snippet = "(begin (ok (try! (if true (ok true) (err u3)))))";

        crosscheck(snippet, Ok(Some(Value::okay_true())));
    }

    #[test]
    fn try_something_in_fn_ok() {
        let snippet = "
        (define-public (foo)
            (ok (try! (if true (ok true) (err u3))))
        )

        (foo)
        ";

        crosscheck(snippet, Ok(Some(Value::okay_true())));
    }

    #[test]
    fn try_something_in_fn_err() {
        let snippet = "
        (define-public (foo)
            (ok (try! (if false (ok true) (err u3))))
        )

        (foo)
        ";

        crosscheck(snippet, Ok(Some(Value::err_uint(3))));
    }

    #[test]
    fn try_reponse_true() {
        crosscheck(
            "(try! (if true (ok true) (err u3)))",
            Ok(Some(Value::Bool(true))),
        )
    }

    #[test]
    fn try_stx_transfer() {
        crosscheck(
            "(try! (stx-transfer? u100 'S1G2081040G2081040G2081040G208105NK8PE5 'ST1PQHQKV0RJXZFY1DGX8MNSNYVE3VGZJSRTPGZGM))",
            Ok(Some(Value::Bool(true))),
        )
    }

    #[test]
    fn try_nested_response_true() {
        crosscheck(
            "(try! (if true (ok (try! (if true (ok true) (err u3)))) (err false)))",
            Ok(Some(Value::Bool(true))),
        )
    }

    #[test]
    fn try_begin_nested() {
        crosscheck(
            "(begin (try! (if true (ok (try! (if true (ok true) (err u3)))) (err false))))",
            Ok(Some(Value::Bool(true))),
        )
    }

    #[test]
    fn try_reponse_inside_funtion() {
        crosscheck(
            "(define-public (foo) (ok (try! (if true (ok true) (err u3))))) (foo)",
            Ok(Some(Value::okay_true())),
        )
    }

    #[test]
    fn try_begin_response_inside_function() {
        crosscheck(
            "(define-public (foo) (begin (+ 1 2) (ok (try! (if true (ok true) (err u3)))))) (foo)",
            Ok(Some(Value::okay_true())),
        )
    }

    #[test]
    fn try_mint_ft() {
        crosscheck(
            "(define-fungible-token wasm-token) (try! (ft-mint? wasm-token u1000 'ST1PQHQKV0RJXZFY1DGX8MNSNYVE3VGZJSRTPGZGM))",
            Ok(Some(Value::Bool(true))),
        )
    }

    #[test]
    fn unwrap_needs_workaround_optional() {
        let snippet = "
            (define-private (foo)
                (unwrap! (if true none (some none)) (some (err u1)))
            )
            (foo)
        ";

        crosscheck(snippet, Ok(Some(Value::some(Value::err_uint(1)).unwrap())));
    }

    #[test]
    fn unwrap_needs_workaround_response() {
        let snippet = "
            (define-private (foo)
                (unwrap! (if true (err none) (ok none)) (some (err u1)))
            )
            (foo)
        ";

        crosscheck(snippet, Ok(Some(Value::some(Value::err_uint(1)).unwrap())));
    }

    #[test]
    fn unwrap_err_needs_workaround() {
        let snippet = "
            (define-private (foo)
                (unwrap-err! (if true (ok none) (err none)) (some (err u1)))
            )
            (foo)
        ";

        crosscheck(snippet, Ok(Some(Value::some(Value::err_uint(1)).unwrap())));
    }

    #[test]
    fn nested_begin_with_try() {
        let snippet = r#"
            (define-private (foo)
                (begin
                    (begin
                        (try! (if false (ok "hello") (err u5555)))
                    )
                    (ok true)
                )
            )
            (foo)
        "#;

        crosscheck(snippet, Ok(Some(Value::err_uint(5555))));
    }
}
