use clarity::vm::clarity_wasm::get_type_size;
use clarity::vm::types::{
    FixedFunction, FunctionType, ListTypeData, SequenceSubtype, StringSubtype, TypeSignature,
};
use clarity::vm::{ClarityName, SymbolicExpression};
use walrus::ir::{self, BinaryOp, IfElse, InstrSeqType, Loop, UnaryOp};
use walrus::ValType;

use crate::check_args;
use crate::cost::WordCharge;
use crate::error_mapping::ErrorMap;
use crate::wasm_generator::{
    add_placeholder_for_clarity_type, clar2wasm_ty, drop_value, has_in_memory_type,
    type_from_sequence_element, ArgumentsExt, BorrowedLocal, GeneratorError, SequenceElementType,
    WasmGenerator,
};
use crate::wasm_utils::{check_argument_count, ArgumentCountCheck};
use crate::words::{self, ComplexWord, Word};

#[derive(Debug)]
pub struct ListCons;

impl Word for ListCons {
    fn name(&self) -> ClarityName {
        "list".into()
    }
}

impl ComplexWord for ListCons {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        expr: &SymbolicExpression,
        list: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        let ty = generator
            .get_expr_type(expr)
            .ok_or_else(|| GeneratorError::TypeError("list expression must be typed".to_owned()))?
            .clone();
        let (elem_ty, _num_elem) =
            if let TypeSignature::SequenceType(SequenceSubtype::ListType(list_type)) = &ty {
                (list_type.get_list_item_type(), list_type.get_max_len())
            } else {
                return Err(GeneratorError::TypeError(format!(
                    "Expected list type for list expression, but found: {ty:?}"
                )));
            };

        self.charge(generator, builder, list.len() as u32)?;

        // Allocate space on the data stack for the entire list
        let (offset, _size) = generator.create_call_stack_local(builder, &ty, false, true);

        // Loop through the expressions in the list and store them onto the
        // data stack.
        let mut total_size = 0;
        for expr in list.iter() {
            // WORKAROUND: if you have a list like `(list (some 1) none)`, even if the list elements have type
            // `optional int`, the typechecker will give NoType to `none`.
            // This means that the placeholder will be represented with a different number of `ValType`, and will
            // cause errors (example: function called with wrong number of arguments).
            // While we wait for a real fix in the typechecker, here is a workaround to set all the elements types.
            generator.set_expr_type(expr, elem_ty.clone())?;

            generator.traverse_expr(builder, expr)?;
            // Write this element to memory
            let elem_size = generator.write_to_memory(builder, offset, total_size, elem_ty)?;
            total_size += elem_size;
        }

        // Push the offset and size to the data stack
        builder.local_get(offset).i32_const(total_size as i32);

        Ok(())
    }
}

#[derive(Debug)]
pub struct Fold;

impl Word for Fold {
    fn name(&self) -> ClarityName {
        "fold".into()
    }
}

impl ComplexWord for Fold {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 3, args.len(), ArgumentCountCheck::Exact);

        self.charge(generator, builder, 0)?;

        let func = args.get_name(0)?;
        let sequence = args.get_expr(1)?;
        let initial = args.get_expr(2)?;

        // Fold takes an initial value, and a sequence, and applies a function
        // to the output of the previous call, or the initial value in the case
        // of the first call, and each element of the sequence.
        // ```
        // (fold - (list 2 4 6) 0)
        // ```
        // is equivalent to
        // ```
        // (- 6 (- 4 (- 2 0)))
        // ```

        // We allocate some space for the return value
        let expr_ty = generator.get_expr_type(expr).cloned().ok_or_else(|| {
            GeneratorError::TypeError("Fold expression should be typed".to_owned())
        })?;
        // the `include_repr` argument should be false here, but with our current implementation, we need the full size of the
        // type without (offset, len), which is a behavior we don't have for now. We are allocating 8 bytes too many.
        let (return_offset, _) = generator.create_call_stack_local(builder, &expr_ty, true, true);

        // We need to find the correct types expected by the function `func` and the result type of the fold expression
        // to make sure everything will be coherent in the end.
        // This is only needed if we are folding a list and the function is user-defined.
        struct FoldFuncTy {
            elem_ty: TypeSignature,
            acc_ty: TypeSignature,
            return_ty: TypeSignature,
        }
        let fold_func_ty = {
            match generator.get_expr_type(sequence).ok_or_else(|| {
                GeneratorError::TypeError("Folded sequence should be typed".to_owned())
            })? {
                TypeSignature::SequenceType(SequenceSubtype::ListType(ltd)) => {
                    match generator.get_function_type(func) {
                        Some(FunctionType::Fixed(FixedFunction { args, returns }))
                            if args.len() == 2 =>
                        {
                            let fold_func_ty = FoldFuncTy {
                                elem_ty: args[0].signature.clone(),
                                acc_ty: args[1].signature.clone(),
                                return_ty: returns.clone(),
                            };
                            // Set the type of the list elements
                            generator.set_expr_type(
                                sequence,
                                TypeSignature::SequenceType(SequenceSubtype::ListType(
                                    ListTypeData::new_list(
                                        fold_func_ty.elem_ty.clone(),
                                        ltd.get_max_len(),
                                    )
                                    .map_err(|e| GeneratorError::TypeError(e.to_string()))?,
                                )),
                            )?;
                            // set the accumulator type
                            generator.set_expr_type(initial, fold_func_ty.acc_ty.clone())?;
                            Some(fold_func_ty)
                        }
                        _ => None,
                    }
                }
                _ => None,
            }
        };

        // The result type must match the type of the initial value
        let result_clar_ty = generator
            .get_expr_type(initial)
            .ok_or_else(|| {
                GeneratorError::TypeError(
                    "fold's initial value expression must be typed".to_owned(),
                )
            })?
            .clone();
        let result_wasm_types = clar2wasm_ty(&result_clar_ty);

        // Get the type of the sequence
        let elem_ty = generator.get_sequence_element_type(sequence)?;

        // Evaluate the sequence, which will load it into the call stack,
        // leaving the offset and size on the data stack.
        generator.traverse_expr(builder, sequence)?;
        // STACK: [offset, length]

        let length = generator.module.locals.add(ValType::I32);
        let offset = generator.module.locals.add(ValType::I32);
        let end_offset = generator.module.locals.add(ValType::I32);

        // Store the length and offset into locals.
        builder.local_set(length).local_tee(offset);
        // STACK: [offset]

        // Compute the ending offset of the sequence.
        builder
            .local_get(length)
            .binop(BinaryOp::I32Add)
            .local_set(end_offset);
        // STACK: []

        // Evaluate the initial value, so that its result is on the data stack
        generator.traverse_expr(builder, initial)?;
        // STACK: [initial_val]

        // If the length of the sequence is 0, then just return the initial
        // value which is already on the stack. Else, loop over the sequence
        // and apply the function.
        let then = builder.dangling_instr_seq(InstrSeqType::new(
            &mut generator.module.types,
            &result_wasm_types,
            &result_wasm_types,
        ));
        let then_id = then.id();

        let mut else_ = builder.dangling_instr_seq(InstrSeqType::new(
            &mut generator.module.types,
            &result_wasm_types,
            &result_wasm_types,
        ));
        let else_id = else_.id();

        // Define local(s) to hold the intermediate result, and initialize them
        // with the initial value. Note that we are looping in reverse order,
        // to pop values from the top of the stack.
        let result_locals = generator.save_to_locals(&mut else_, &result_clar_ty, true);

        // Define the body of a loop, to loop over the sequence and make the
        // function call.
        let mut loop_ = else_.dangling_instr_seq(None);
        let loop_id = loop_.id();

        // Load the element from the sequence
        let elem_size = match &elem_ty {
            SequenceElementType::Other(elem_ty) => {
                generator.read_from_memory(&mut loop_, offset, 0, elem_ty)?
            }
            SequenceElementType::Byte => {
                // The element type is a byte, so we can just push the
                // offset and length (1) to the stack.
                loop_.local_get(offset).i32_const(1);
                1
            }
            SequenceElementType::UnicodeScalar => {
                // The element type is a 32-bit unicode scalar, so we can just push the
                // offset and length (4) to the stack.
                loop_.local_get(offset).i32_const(4);
                4
            }
        };

        // Push the locals to the stack
        for result_local in &result_locals {
            loop_.local_get(*result_local);
        }

        if let Some(simple) = words::lookup_simple(func).or(words::lookup_variadic_simple(func)) {
            // Call simple builtin

            let arg_a_ty = type_from_sequence_element(&elem_ty);
            let arg_types = &[arg_a_ty, result_clar_ty.clone()];

            simple.visit(generator, &mut loop_, arg_types, &result_clar_ty)?;
        } else {
            // Call user defined function
            generator.visit_call_user_defined(
                &mut loop_,
                func,
                &result_clar_ty,
                fold_func_ty.as_ref().map(|func_ty| &func_ty.acc_ty),
                Some(return_offset),
            )?;
            // since the accumulator and the return type of the function could have different types, we need to duck-type.
            if let Some(tys) = &fold_func_ty {
                generator.duck_type(&mut loop_, &tys.return_ty, &tys.acc_ty)?;
            }
        }
        // Save the result into the locals (in reverse order as we pop)
        for result_local in result_locals.iter().rev() {
            loop_.local_set(*result_local);
        }

        // Increment the offset by the size of the element, leaving the
        // offset on the top of the stack
        loop_
            .local_get(offset)
            .i32_const(elem_size)
            .binop(BinaryOp::I32Add)
            .local_tee(offset);

        // Loop if we haven't reached the end of the sequence
        loop_
            .local_get(end_offset)
            .binop(BinaryOp::I32LtU)
            .br_if(loop_id);

        else_.instr(Loop { seq: loop_id });

        // Push the locals to the stack
        for result_local in result_locals {
            else_.local_get(result_local);
        }

        builder
            .local_get(length)
            .unop(UnaryOp::I32Eqz)
            .instr(IfElse {
                consequent: then_id,
                alternative: else_id,
            });

        // since the return type of the function and the accumulator could have different types, we need to duck-type.
        if let Some(tys) = &fold_func_ty {
            generator.duck_type(builder, &tys.acc_ty, &tys.return_ty)?;
        }

        Ok(())
    }
}

#[derive(Debug)]
pub struct Append;

impl Word for Append {
    fn name(&self) -> ClarityName {
        "append".into()
    }
}

impl ComplexWord for Append {
    fn traverse(
        &self,
        generator: &mut crate::wasm_generator::WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        expr: &SymbolicExpression,
        args: &[clarity::vm::SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 2, args.len(), ArgumentCountCheck::Exact);

        let ty = generator
            .get_expr_type(expr)
            .ok_or_else(|| GeneratorError::TypeError("append result must be typed".to_string()))?
            .clone();

        let list = args.get_expr(0)?;
        let elem = args.get_expr(1)?;

        // WORKAROUND: setting correct types for arguments
        let elem_ty = match &ty {
            TypeSignature::SequenceType(SequenceSubtype::ListType(ltd)) => {
                let elem_ty = ltd.get_list_item_type();
                generator.set_expr_type(
                    list,
                    #[allow(clippy::expect_used)]
                    ListTypeData::new_list(elem_ty.clone(), ltd.get_max_len() - 1)
                        .expect("Argument type should be correct as it is the same as the expression type with a smaller max_len")
                        .into(),
                )?;
                generator.set_expr_type(elem, elem_ty.clone())?;
                elem_ty.clone()
            }
            _ => {
                return Err(GeneratorError::TypeError(
                    "append result should be a list".to_owned(),
                ))
            }
        };

        let memory = generator.get_memory()?;

        // Allocate stack space for the new list.
        let (write_ptr, _) = generator.create_call_stack_local(builder, &ty, false, true);

        // Push the offset and length of this list to the stack to be returned.
        builder.local_get(write_ptr);

        // Push the write pointer onto the stack for `memory.copy`.
        builder.local_get(write_ptr);

        // Traverse the list to append to, leaving the offset and length on
        // top of the stack.
        generator.traverse_expr(builder, list)?;

        // The stack now has the destination, source and length arguments in
        // right order for `memory.copy` to copy the source list into the new
        // list. Save a copy of the length for later.
        let src_length = generator.module.locals.add(ValType::I32);
        builder.local_tee(src_length);

        // Increment the write pointer by the length of the source list.
        builder
            .local_get(write_ptr)
            .local_get(src_length)
            .binop(BinaryOp::I32Add)
            .local_set(write_ptr);

        // At this point, we can compute the cost which depends on the actual number of elements in the list:
        // ((number of elements in the list) * (element type size) + (1 element type size)) / (element type size)
        let elem_size = get_type_size(&elem_ty);
        let number_of_elements = generator.module.locals.add(ValType::I32);
        builder
            .local_get(src_length)
            .i32_const(elem_size)
            .binop(BinaryOp::I32Add)
            // we save this result since it will be the result length
            .local_tee(src_length)
            .i32_const(elem_size)
            .binop(BinaryOp::I32DivU)
            .local_set(number_of_elements);
        self.charge(generator, builder, number_of_elements)?;

        // We use the values on the stack to copy the list to its destination
        builder.memory_copy(memory, memory);

        // Traverse the element that we're appending to the list.
        generator.traverse_expr(builder, elem)?;

        // Store the element at the write pointer.
        generator.write_to_memory(builder, write_ptr, 0, &elem_ty)?;

        // For the result, we already pushed the offset previously, so here is the length.
        builder.local_get(src_length);

        Ok(())
    }
}

#[derive(Debug)]
pub struct AsMaxLen;

impl Word for AsMaxLen {
    fn name(&self) -> ClarityName {
        "as-max-len?".into()
    }
}

impl ComplexWord for AsMaxLen {
    fn traverse(
        &self,
        generator: &mut crate::wasm_generator::WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[clarity::vm::SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 2, args.len(), ArgumentCountCheck::Exact);

        // Push a `0` and a `1` to the stack, to be used by the `select`
        // instruction later.
        builder.i32_const(0).i32_const(1);

        // Traverse the input list, leaving the offset and length on top of
        // the stack.
        let seq = args.get_expr(0)?;
        generator.traverse_expr(builder, seq)?;

        // Save the offset and length to locals for later. Leave the length on
        // top of the stack.
        let length_local = generator.module.locals.add(ValType::I32);
        builder.local_set(length_local);
        let offset_local = generator.module.locals.add(ValType::I32);
        builder.local_set(offset_local);
        builder.local_get(length_local);

        self.charge(generator, builder, 0)?;

        // We need to check if the list is longer than the second argument.
        // If it is, then return `none`, otherwise, return `(some input)`.
        // Push the length of the value onto the stack.

        // Get the length.
        generator
            .get_expr_type(seq)
            .ok_or_else(|| GeneratorError::TypeError("append result must be typed".to_string()))
            .and_then(|ty| match ty {
                TypeSignature::SequenceType(SequenceSubtype::ListType(list)) => {
                    // The length of the list in bytes is on the top of the stack. If we
                    // divide that by the length of each element, then we'll have the
                    // length of the list in elements.
                    let element_length = get_type_size(list.get_list_item_type());
                    builder.i32_const(element_length);

                    // Divide the length of the list by the length of each element to get
                    // the number of elements in the list.
                    builder.binop(BinaryOp::I32DivU);

                    Ok(())
                }
                TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(
                    _,
                ))) => {
                    // UTF8 is represented as 32-bit (4 bytes) unicode scalars values.
                    // Compute the number of elements in the list by dividing the total byte length by 4
                    // (i.e., each element is 4 bytes). This division is equivalent to performing an unsigned
                    // bitwise right shift by 2 bits.
                    builder.i32_const(2);
                    builder.binop(BinaryOp::I32ShrU);

                    Ok(())
                }
                // The byte length of buffers and ASCII strings is the same as
                // the value length, so just leave it as-is.
                TypeSignature::SequenceType(SequenceSubtype::BufferType(_))
                | TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(
                    _,
                ))) => Ok(()),
                _ => Err(GeneratorError::TypeError(
                    "expected sequence type".to_string(),
                )),
            })?;

        // Convert this 32-bit length to a 64-bit value, for comparison.
        builder.unop(UnaryOp::I64ExtendUI32);

        // Traverse the second argument, the desired length, leaving the low
        // and high parts on the stack, then drop the high part.
        generator.traverse_expr(builder, args.get_expr(1)?)?;
        builder.drop();

        // Compare the length of the list to the desired length.
        builder.binop(BinaryOp::I64GtU);

        // Select from the `0` and `1` that we pushed to the stack earlier,
        // based on the result of the comparison.
        builder.select(Some(ValType::I32));

        // Now, put the original offset and length back on the stack. In the
        // case where the result is `none`, these will be ignored, but it
        // doesn't hurt to have them there.
        builder.local_get(offset_local).local_get(length_local);

        Ok(())
    }
}

#[derive(Debug)]
pub struct Concat;

impl Word for Concat {
    fn name(&self) -> ClarityName {
        "concat".into()
    }
}

impl ComplexWord for Concat {
    fn traverse(
        &self,
        generator: &mut crate::wasm_generator::WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        expr: &SymbolicExpression,
        args: &[clarity::vm::SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 2, args.len(), ArgumentCountCheck::Exact);

        let memory = generator.get_memory()?;

        // Create a new sequence to hold the result in the stack frame
        let ty = generator
            .get_expr_type(expr)
            .ok_or_else(|| GeneratorError::TypeError("concat expression must be typed".to_owned()))?
            .clone();
        let (offset, _) = generator.create_call_stack_local(builder, &ty, false, true);

        builder.local_get(offset);

        // Traverse the lhs, leaving it on the data stack (offset, size)
        let lhs = args.get_expr(0)?;
        // WORKAROUND: typechecker issue for lists
        generator.set_expr_type(lhs, ty.clone())?;
        generator.traverse_expr(builder, lhs)?;

        // Save the length of the lhs
        let lhs_length = generator.module.locals.add(ValType::I32);
        builder.local_tee(lhs_length);

        // Copy the lhs to the new sequence
        builder.memory_copy(memory, memory);

        // Load the adjusted destination offset
        builder
            .local_get(offset)
            .local_get(lhs_length)
            .binop(BinaryOp::I32Add);

        // Traverse the rhs, leaving it on the data stack (offset, size)
        let rhs = args.get_expr(1)?;
        // WORKAROUND: typechecker issue for lists
        generator.set_expr_type(rhs, ty.clone())?;
        generator.traverse_expr(builder, rhs)?;

        // Save the length of the rhs
        let rhs_length = generator.module.locals.add(ValType::I32);
        builder.local_tee(rhs_length);

        // Copy the rhs to the new sequence
        builder.memory_copy(memory, memory);

        // Load the offset of the new sequence
        builder.local_get(offset);

        // Total size = lhs_length + rhs_length
        builder
            .local_get(lhs_length)
            .local_get(rhs_length)
            .binop(BinaryOp::I32Add);

        // we charge after the operation since that's the only time we have the
        // length of the resulting list
        let length = generator.module.locals.add(ValType::I32);
        builder.local_tee(length);
        self.charge(generator, builder, length)?;

        Ok(())
    }
}

#[derive(Debug)]
pub struct Map;

impl Word for Map {
    fn name(&self) -> ClarityName {
        "map".into()
    }
}

impl ComplexWord for Map {
    fn traverse(
        &self,
        generator: &mut crate::wasm_generator::WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        expr: &SymbolicExpression,
        args: &[clarity::vm::SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(
            generator,
            builder,
            2,
            args.len(),
            ArgumentCountCheck::AtLeast
        );

        struct MapArg {
            element_type: SequenceElementType,
            element_size: i32,
            offset: BorrowedLocal,
            length: BorrowedLocal,
        }

        let fname = args.get_name(0)?;

        if let Some(FunctionType::Fixed(fixed)) = generator.get_function_type(fname) {
            for (function_arg, arg) in fixed.args.clone().into_iter().zip(&args[1..]) {
                if let TypeSignature::SequenceType(SequenceSubtype::ListType(ltd)) =
                    generator.get_expr_type(arg).cloned().ok_or_else(|| {
                        GeneratorError::TypeError("map argument should be typed".to_owned())
                    })?
                {
                    let workaround_ty =
                        TypeSignature::list_of(function_arg.signature, ltd.get_max_len()).map_err(
                            |e| {
                                GeneratorError::TypeError(format!(
                                    "could not create a list type for an argument in map: {e}"
                                ))
                            },
                        )?;
                    generator.set_expr_type(arg, workaround_ty)?;
                }
            }
        }

        let ty = generator
            .get_expr_type(expr)
            .ok_or_else(|| GeneratorError::TypeError("list expression must be typed".to_owned()))?
            .clone();

        eprintln!("TY: {ty:?}");

        let (return_element_type, return_list_max_size) =
            if let TypeSignature::SequenceType(SequenceSubtype::ListType(list_type)) = &ty {
                (list_type.get_list_item_type(), list_type.get_max_len())
            } else {
                return Err(GeneratorError::TypeError(format!(
                    "Expected list type for list expression, but found: {ty:?}"
                )));
            };

        let (result_offset, _len) = generator.create_call_stack_local(builder, &ty, true, true);
        eprintln!("LEN: {_len}");

        let result_length = generator.borrow_local(ValType::I32);
        builder.i32_const(0).local_set(*result_length);

        let current_result_offset = generator.borrow_local(ValType::I32);

        // if result needs to be copied back to result_offset, we will copy at the offset in this local
        let in_memory_offset = has_in_memory_type(return_element_type).then(|| {
            let l = generator.module.locals.add(ValType::I32);
            builder
                .local_get(result_offset)
                .i32_const(dbg!(
                    (get_type_size(return_element_type) * return_list_max_size as i32)
                ))
                .binop(BinaryOp::I32Add)
                .local_set(l);
            l
        });

        // Evaluating all arguments and assigning the results to each maparg
        let mapargs: Vec<MapArg> = args
            .iter()
            .skip(1)
            .map(|arg| {
                let element_type: SequenceElementType = generator
                    .get_expr_type(arg)
                    .ok_or_else(|| {
                        GeneratorError::TypeError("sequence expression must be typed".to_owned())
                    })?
                    .try_into()?;
                let element_size = element_type.type_size();

                let offset = generator.borrow_local(ValType::I32);
                let length = generator.borrow_local(ValType::I32);

                generator.traverse_expr(builder, arg)?;
                builder.local_set(*length).local_set(*offset);

                Ok(MapArg {
                    element_type,
                    element_size,
                    offset,
                    length,
                })
            })
            .collect::<Result<_, _>>()?;

        // We need the resulting number of elements for the cost tracking (and since we will compute it, we can use it for looping later)
        let num_elements = generator.borrow_local(ValType::I32);
        match mapargs.as_slice() {
            [single_arg] => {
                builder
                    .local_get(*single_arg.length)
                    .i32_const(single_arg.element_size)
                    .binop(BinaryOp::I32DivU)
                    .local_set(*num_elements);
            }
            [first_arg, rest_args @ ..] => {
                builder
                    .local_get(*first_arg.length)
                    .i32_const(first_arg.element_size)
                    .binop(BinaryOp::I32DivU)
                    .local_set(*num_elements);

                let tmp = generator.borrow_local(ValType::I32);
                for MapArg {
                    element_size,
                    length,
                    ..
                } in rest_args
                {
                    // putting the actual minimum length on the stack
                    builder.local_get(*num_elements);

                    // computing next sequence length
                    builder
                        .local_get(**length)
                        .i32_const(*element_size)
                        .binop(BinaryOp::I32DivU)
                        .local_tee(*tmp);

                    // checking if actual minimum is still smaller
                    builder
                        .local_get(*num_elements)
                        .local_get(*tmp)
                        .binop(BinaryOp::I32LtU);

                    // check which is smaller and assign
                    builder.select(None).local_set(*num_elements);
                }
            }
            _ => {
                return Err(GeneratorError::TypeError(
                    "There should be at least one sequence argument in a map".to_owned(),
                ))
            }
        }

        // cost tracking: depends on the number of elements in the result
        self.charge(generator, builder, *num_elements)?;

        // here is the map loop: we go through each corresponding element of each sequence and apply the function
        let loop_id = {
            let mut loop_ = builder.dangling_instr_seq(None);
            let loop_id = loop_.id();

            let current_stack_pointer = generator.borrow_local(ValType::I32);

            loop_
                .global_get(generator.stack_pointer)
                .local_set(*current_stack_pointer);

            // Calling the function with its arguments.
            // We need to handle the arguments of the function differently depending
            // on the function kind: simple, variadic, or user defined.
            if let Some(simple_fn) = words::lookup_simple(fname) {
                // A simple function: we need to load the already evaluated arguments one by one,
                // then visit the simple function.
                for MapArg {
                    element_type,
                    offset,
                    ..
                } in mapargs.iter()
                {
                    element_type.load(generator, &mut loop_, **offset)?;
                }
                simple_fn.visit(
                    generator,
                    &mut loop_,
                    mapargs
                        .iter()
                        .map(|MapArg { element_type, .. }| element_type.into())
                        .collect::<Vec<_>>()
                        .as_slice(),
                    return_element_type,
                )?;

                // we need to copy the result to the preallocated space if needed.
                if let Some(copy_offset) = &in_memory_offset {
                    let locals = generator.save_to_locals(&mut loop_, return_element_type, true);
                    generator.copy_value(&mut loop_, return_element_type, &locals, *copy_offset)?;
                    locals.into_iter().for_each(|l| {
                        loop_.local_get(l);
                    });
                }
            } else if let Some(variadic) = words::lookup_variadic_simple(fname) {
                // A variadic function: we need to interleave the already evaluated arguments with the function.
                let Some((
                    MapArg {
                        element_type: first_element_type,
                        offset: first_offset,
                        ..
                    },
                    rest_args,
                )) = mapargs.split_first()
                else {
                    return Err(GeneratorError::TypeError(
                        "map needs at least one sequence argument".to_owned(),
                    ));
                };
                // if we have only one sequence, we use the function directly, otherwise we load each following arguments
                // and interleave them with the variadic function.
                first_element_type.load(generator, &mut loop_, **first_offset)?;
                if rest_args.is_empty() {
                    variadic.visit(
                        generator,
                        &mut loop_,
                        &[first_element_type.into()],
                        return_element_type,
                    )?;
                } else {
                    for (
                        MapArg {
                            element_type: ty1, ..
                        },
                        MapArg {
                            element_type: ty2,
                            offset: offset2,
                            ..
                        },
                    ) in mapargs.iter().zip(rest_args)
                    {
                        ty2.load(generator, &mut loop_, **offset2)?;
                        variadic.visit(
                            generator,
                            &mut loop_,
                            &[ty1.into(), ty2.into()],
                            return_element_type,
                        )?;
                    }
                }

                // we need to copy the result to the preallocated space if needed.
                if let Some(copy_offset) = &in_memory_offset {
                    let locals = generator.save_to_locals(&mut loop_, return_element_type, true);
                    generator.copy_value(&mut loop_, return_element_type, &locals, *copy_offset)?;
                    locals.into_iter().for_each(|l| {
                        loop_.local_get(l);
                    });
                }
            } else {
                // if we have a user defined function, we have to stack all the arguments and call it.
                let user_defined_return_type = {
                    if let Some(FunctionType::Fixed(FixedFunction { returns, .. })) =
                        generator.get_function_type(fname)
                    {
                        returns.clone()
                    } else {
                        return Err(GeneratorError::TypeError(
                            "map tries to use an undefined user function".to_owned(),
                        ));
                    }
                };

                for MapArg {
                    element_type,
                    offset,
                    ..
                } in mapargs.iter()
                {
                    element_type.load(generator, &mut loop_, **offset)?;
                }
                generator.visit_call_user_defined(
                    &mut loop_,
                    fname,
                    &user_defined_return_type,
                    Some(return_element_type),
                    None,
                )?;
            }

            // Afer the execution of the function for an element, we have to write the result to memory.
            let return_element_size = generator.write_to_memory(
                &mut loop_,
                *current_result_offset,
                0,
                return_element_type,
            )? as i32;

            // Finally, we update all our current locals for the next loop turn
            loop_
                .local_get(*current_stack_pointer)
                .global_set(generator.stack_pointer);
            loop_
                .local_get(*result_length)
                .i32_const(return_element_size)
                .binop(BinaryOp::I32Add)
                .local_set(*result_length);
            loop_
                .local_get(*current_result_offset)
                .i32_const(return_element_size)
                .binop(BinaryOp::I32Add)
                .local_set(*current_result_offset);
            for MapArg {
                offset,
                element_type,
                ..
            } in &mapargs
            {
                loop_
                    .local_get(**offset)
                    .i32_const(element_type.type_size())
                    .binop(BinaryOp::I32Add)
                    .local_set(**offset);
            }
            loop_
                .local_get(*num_elements)
                .i32_const(1)
                .binop(BinaryOp::I32Sub)
                .local_tee(*num_elements)
                .br_if(loop_id);

            loop_id
        };

        // Now we insert the loop in the algorithm, and execute it only if we have at least one element in the
        // returned list.
        builder.local_get(*num_elements).if_else(
            None,
            |then| {
                then.local_get(result_offset)
                    .local_set(*current_result_offset);
                then.instr(Loop { seq: loop_id });
            },
            |_else| {},
        );

        // we finally return the (offset, length) of the result list
        builder.local_get(result_offset).local_get(*result_length);

        Ok(())
    }
}

#[derive(Debug)]
pub struct Len;

impl Word for Len {
    fn name(&self) -> ClarityName {
        "len".into()
    }
}

impl ComplexWord for Len {
    fn traverse(
        &self,
        generator: &mut crate::wasm_generator::WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[clarity::vm::SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 1, args.len(), ArgumentCountCheck::Exact);

        self.charge(generator, builder, 0)?;

        // Traverse the sequence, leaving the offset and length on the stack.
        let seq = args.get_expr(0)?;
        generator.traverse_expr(builder, seq)?;

        // Save the length, then drop the offset and push the length back.
        let length_local = generator.module.locals.add(ValType::I32);
        builder
            .local_set(length_local)
            .drop()
            .local_get(length_local);

        // Get the length
        generator
            .get_expr_type(seq)
            .ok_or_else(|| GeneratorError::TypeError("append result must be typed".to_string()))
            .and_then(|ty| match ty {
                TypeSignature::SequenceType(SequenceSubtype::ListType(list)) => {
                    // The length of the list in bytes is on the top of the stack. If we
                    // divide that by the length of each element, then we'll have the
                    // length of the list in elements.
                    let element_length = get_type_size(list.get_list_item_type());
                    builder.i32_const(element_length);

                    // Divide the length of the list by the length of each element to get
                    // the number of elements in the list.
                    builder.binop(BinaryOp::I32DivU);

                    Ok(())
                }
                TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(
                    _,
                ))) => {
                    // UTF8 is represented as 32-bit (4 bytes) unicode scalars values.
                    // Compute the number of elements in the list by dividing the total byte length by 4
                    // (i.e., each element is 4 bytes). This division is equivalent to performing an unsigned
                    // bitwise right shift by 2 bits.
                    builder.i32_const(2);
                    builder.binop(BinaryOp::I32ShrU);

                    Ok(())
                }
                // The byte length of buffers and ASCII strings is the same as
                // the value length, so just leave it as-is.
                TypeSignature::SequenceType(SequenceSubtype::BufferType(_))
                | TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(
                    _,
                ))) => Ok(()),
                _ => Err(GeneratorError::TypeError(
                    "expected sequence type".to_string(),
                )),
            })?;

        // Convert this 32-bit length to a 64-bit value.
        builder.unop(UnaryOp::I64ExtendUI32);

        // Then push a 0 for the upper 64 bits.
        builder.i64_const(0);

        Ok(())
    }
}

#[derive(Debug)]
pub enum ElementAt {
    Original,
    Alias,
}

impl Word for ElementAt {
    fn name(&self) -> ClarityName {
        match self {
            ElementAt::Original => "element-at".into(),
            ElementAt::Alias => "element-at?".into(),
        }
    }
}

impl ComplexWord for ElementAt {
    fn traverse(
        &self,
        generator: &mut crate::wasm_generator::WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        expr: &SymbolicExpression,
        args: &[clarity::vm::SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 2, args.len(), ArgumentCountCheck::Exact);

        self.charge(generator, builder, 0)?;

        // Traverse the sequence, leaving the offset and length on the stack.
        let seq = args.get_expr(0)?;
        generator.traverse_expr(builder, seq)?;

        // Extend the length to 64-bits.
        builder.unop(UnaryOp::I64ExtendUI32);

        // Traverse the index, leaving the value on top of the stack.
        generator.traverse_expr(builder, args.get_expr(1)?)?;

        // Check if the upper 64-bits are greater than 0.
        builder.i64_const(0).binop(BinaryOp::I64GtU);

        // Save the overflow indicator to a local.
        let overflow_local = generator.module.locals.add(ValType::I32);
        builder.local_set(overflow_local);

        // Save the lower part of the index to a local.
        let index_local = generator.module.locals.add(ValType::I64);
        builder.local_tee(index_local);

        // Check if the lower 64-bits are greater than 1024x1024 (max value
        // size). We do this check before comparing with the length of the list
        // because it ensures that the multiplication will not overflow.
        builder.i64_const(1024 * 1024).binop(BinaryOp::I64GtU);

        // Or with the overflow indicator.
        builder
            .local_get(overflow_local)
            .binop(BinaryOp::I32Or)
            .local_set(overflow_local);

        // Push the index onto the stack again.
        builder.local_get(index_local);

        // Record the element type, for use later.
        let element_ty: SequenceElementType = generator
            .get_expr_type(seq)
            .ok_or_else(|| GeneratorError::TypeError("append result must be typed".to_string()))
            .and_then(|ty| match ty {
                TypeSignature::SequenceType(SequenceSubtype::ListType(list)) => {
                    // The length of the list in bytes is on the top of the stack. If we
                    // divide that by the length of each element, then we'll have the
                    // length of the list in elements.
                    let elem_ty = list.get_list_item_type();
                    let element_length = get_type_size(elem_ty);
                    builder.i64_const(element_length as i64);

                    // Multiply the index by the length of each element to get
                    // byte-offset into the list.
                    builder.binop(BinaryOp::I64Mul);

                    Ok(SequenceElementType::Other(elem_ty.clone()))
                }
                TypeSignature::SequenceType(SequenceSubtype::BufferType(_))
                | TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(
                    _,
                ))) => {
                    // The index is the same as the byte-offset, so just leave
                    // it as-is.
                    Ok(SequenceElementType::Byte)
                }
                TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(
                    _,
                ))) => {
                    // UTF8 is represented as 32-bit (4 bytes) unicode scalars values.
                    // Calculate the total byte length of the list by multiplying the element count by 4
                    // Multiplying by 4 is equivalent to performing a bitwise left shift by 2 bits.
                    builder.i64_const(2);
                    builder.binop(BinaryOp::I64Shl);

                    Ok(SequenceElementType::UnicodeScalar)
                }
                _ => Err(GeneratorError::TypeError(
                    "expected sequence type".to_string(),
                )),
            })?;

        // Save the element offset to the local.
        builder.local_tee(index_local);

        // Check if the element offset is out of range by comparing it to the
        // length of the list.
        builder.binop(BinaryOp::I64LeU);

        // Or with the overflow indicator.
        builder.local_get(overflow_local).binop(BinaryOp::I32Or);

        // If the index is out of range, then return `none`, else load the
        // value at the specified index and return `(some value)`.
        let result_ty = generator
            .get_expr_type(expr)
            .ok_or_else(|| GeneratorError::TypeError("append result must be typed".to_string()))?;
        let result_wasm_types = clar2wasm_ty(result_ty);

        let branch_ty = InstrSeqType::new(
            &mut generator.module.types,
            &[ValType::I32],
            &result_wasm_types,
        );
        let mut then = builder.dangling_instr_seq(branch_ty);
        let then_id = then.id();

        // First, drop the offset.
        then.drop();

        // Push the `none` indicator.
        then.i32_const(0);

        // Then push a placeholder for the element type.
        match &element_ty {
            SequenceElementType::Byte | SequenceElementType::UnicodeScalar => {
                // The element type is an in-memory type, so we need
                // placeholders for offset and length
                then.i32_const(0).i32_const(0);
            }
            SequenceElementType::Other(elem_ty) => {
                // Read the element type from the list.
                add_placeholder_for_clarity_type(&mut then, elem_ty)
            }
        }

        let mut else_ = builder.dangling_instr_seq(branch_ty);
        let else_id = else_.id();

        let offset_local = generator.module.locals.add(ValType::I32);

        // Add the element offset to the offset of the list.
        else_
            .local_get(index_local)
            // We know this offset is in range, so it must be a 32-bit
            // value, so this operation is safe.
            .unop(UnaryOp::I32WrapI64)
            .binop(BinaryOp::I32Add)
            .local_set(offset_local);

        // Push the `some` indicator
        else_.i32_const(1);

        // Load the value at the specified offset.
        match &element_ty {
            SequenceElementType::Byte => {
                // The element type is a byte (from a string or buffer), so
                // we need to push the offset and length (1) to the
                // stack.
                else_.local_get(offset_local).i32_const(1);
            }
            SequenceElementType::UnicodeScalar => {
                // UTF8 is represented as 32-bit unicode scalar values.
                else_.local_get(offset_local).i32_const(4);
            }
            SequenceElementType::Other(elem_ty) => {
                // If the element type is not UTF8, use `read_from_memory`.
                generator.read_from_memory(&mut else_, offset_local, 0, elem_ty)?;
            }
        }

        builder.instr(ir::IfElse {
            consequent: then_id,
            alternative: else_id,
        });

        Ok(())
    }
}

#[derive(Debug)]
pub struct ReplaceAt;

impl Word for ReplaceAt {
    fn name(&self) -> ClarityName {
        "replace-at?".into()
    }
}

impl ComplexWord for ReplaceAt {
    fn traverse(
        &self,
        generator: &mut crate::wasm_generator::WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        expr: &SymbolicExpression,
        args: &[clarity::vm::SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 3, args.len(), ArgumentCountCheck::Exact);

        let memory = generator.get_memory()?;

        let seq = args.get_expr(0)?;
        let seq_ty = generator
            .get_expr_type(seq)
            .ok_or_else(|| {
                GeneratorError::TypeError("replace-at? result must be typed".to_string())
            })?
            .clone();
        let element_ty = generator.get_sequence_element_type(seq)?;

        let length = generator.module.locals.add(ValType::I32);
        let number_of_elements = generator.module.locals.add(ValType::I32);

        // Create a new stack local for a copy of the input list
        let (dest_offset, _) = generator.create_call_stack_local(builder, &seq_ty, false, true);

        // Put the destination offset on the stack
        builder.local_get(dest_offset);

        // Traverse the list, leaving the offset and length on top of the stack.
        generator.traverse_expr(builder, seq)?;

        // Save actual list length to a local + keep it on the stack for the memcpy
        builder.local_tee(length);

        // At this point, we can compute the cost of the function call using the number of elements in the list
        builder.local_get(length);
        match &element_ty {
            SequenceElementType::Byte => {
                // nothing to change here
            }
            SequenceElementType::UnicodeScalar => {
                // number of bytes / 4
                builder.i32_const(2).binop(BinaryOp::I32ShrU);
            }
            SequenceElementType::Other(ty) => {
                // number of bytes / element size
                builder
                    .i32_const(get_type_size(ty))
                    .binop(BinaryOp::I32DivU);
            }
        }
        builder.local_set(number_of_elements);
        self.charge(generator, builder, number_of_elements)?;

        // Copy the input list to the new stack local
        builder.memory_copy(memory, memory);

        // Extend the sequence length to 64-bits.
        builder.local_get(length).unop(UnaryOp::I64ExtendUI32);

        // Traverse the index, leaving the value on top of the stack.
        generator.traverse_expr(builder, args.get_expr(1)?)?;

        // Check if the upper 64-bits are greater than 0.
        builder.i64_const(0).binop(BinaryOp::I64GtU);

        // Save the overflow indicator to a local.
        let overflow_local = generator.module.locals.add(ValType::I32);
        builder.local_set(overflow_local);

        // Save the lower part of the index to a local.
        let index_local = generator.module.locals.add(ValType::I64);
        builder.local_tee(index_local);

        // Check if the lower 64-bits are greater than 1024x1024 (max value
        // size). We do this check before comparing with the length of the list
        // because it ensures that the multiplication will not overflow.
        builder.i64_const(1024 * 1024).binop(BinaryOp::I64GtU);

        // Or with the overflow indicator.
        builder
            .local_get(overflow_local)
            .binop(BinaryOp::I32Or)
            .local_set(overflow_local);

        // Push the index onto the stack again.
        builder.local_get(index_local);

        // Get the offset of the specified index.
        match &element_ty {
            SequenceElementType::Other(ty) => {
                // The length of the list in bytes is on the top of the stack. If we
                // divide that by the length of each element, then we'll have the
                // length of the list in elements.
                let element_length = get_type_size(ty);
                builder.i64_const(element_length as i64);

                // Multiply the index by the length of each element to get
                // byte-offset into the list.
                builder.binop(BinaryOp::I64Mul);
            }
            SequenceElementType::Byte => {
                // The index is the same as the byte-offset, so just leave
                // it as-is.
            }
            SequenceElementType::UnicodeScalar => {
                // UTF8 is represented as 32-bit (4 bytes) unicode scalars values.
                // Calculate the total byte length of the list by multiplying the element count by 4
                // Multiplying by 4 is equivalent to performing a bitwise left shift by 2 bits.
                builder.i64_const(2);
                builder.binop(BinaryOp::I64Shl);
            }
        }

        // Save the element offset to the local.
        builder.local_tee(index_local);

        // Check if the element offset is out of range by comparing it to the
        // length of the list.
        builder.binop(BinaryOp::I64LeU);

        // Or with the overflow indicator.
        builder
            .local_get(overflow_local)
            .binop(BinaryOp::I32Or)
            .local_set(overflow_local);

        // Traverse the replacement value, leaving it on the stack.
        let replacement = args.get_expr(2)?;
        generator.traverse_expr(builder, replacement)?;

        // For types `string-ascii`, `string-utf8` and `buff`, an empty replacement could be a
        // valid value with a max-len of 1. However, using one is a runtime error.
        if matches!(
            element_ty,
            SequenceElementType::Byte | SequenceElementType::UnicodeScalar
        ) {
            let repl_len = generator.module.locals.add(ValType::I32);
            builder.local_tee(repl_len).unop(UnaryOp::I32Eqz).if_else(
                None,
                |then| {
                    then.i32_const(ErrorMap::BadTypeConstruction as i32)
                        .call(generator.func_by_name("stdlib.runtime-error"));
                },
                |_| {},
            );
            builder.local_get(repl_len);
        }

        let input_ty = generator.get_expr_type(replacement).ok_or_else(|| {
            GeneratorError::TypeError("replace-at? value must be typed".to_string())
        })?;
        let input_wasm_types = clar2wasm_ty(input_ty);

        // Push the overflow result to the stack for `if_else`.
        builder.local_get(overflow_local);

        // If the index is out of range, then return `none`, else write the
        // value at the specified index and return `(some value)`.
        let result_ty = generator
            .get_expr_type(expr)
            .ok_or_else(|| GeneratorError::TypeError("append result must be typed".to_string()))?;
        let result_wasm_types = clar2wasm_ty(result_ty);

        let mut then = builder.dangling_instr_seq(InstrSeqType::new(
            &mut generator.module.types,
            &input_wasm_types,
            &result_wasm_types,
        ));
        let then_id = then.id();

        // First, drop the value.
        match &element_ty {
            SequenceElementType::Other(elem_ty) => {
                // Read the element type from the list.
                drop_value(&mut then, elem_ty);
            }
            SequenceElementType::Byte | SequenceElementType::UnicodeScalar => {
                // The value is a byte or 32-bit scalar, but it's represented by an offset
                // and length, so drop those.
                then.drop().drop();
            }
        }

        // Push the `none` indicator and placeholders for offset/length
        then.i32_const(0).i32_const(0).i32_const(0);

        let mut else_ = builder.dangling_instr_seq(InstrSeqType::new(
            &mut generator.module.types,
            &input_wasm_types,
            &result_wasm_types,
        ));
        let else_id = else_.id();

        let offset_local = generator.module.locals.add(ValType::I32);

        // Add the element offset to the offset of the destination.
        else_
            .local_get(index_local)
            // We know this offset is in range, so it must be a 32-bit
            // value, so this operation is safe.
            .unop(UnaryOp::I32WrapI64)
            .local_get(dest_offset)
            .binop(BinaryOp::I32Add)
            .local_set(offset_local);

        // Write the value to the specified offset.
        match &element_ty {
            SequenceElementType::Byte => {
                // The element type is a byte (from a string or buffer), so
                // we need to just copy that byte to the specified offset.

                // Drop the length of the value (it must be 1)
                else_.drop();

                // Save the source offset to a local.
                let src_local = generator.module.locals.add(ValType::I32);
                else_.local_set(src_local);

                else_
                    .local_get(offset_local)
                    .local_get(src_local)
                    .i32_const(1)
                    .memory_copy(memory, memory);
            }
            SequenceElementType::UnicodeScalar => {
                // The element is a 32-bit unicode scalar value, so we
                // need to just copy those 4 bytes to the specified offset.

                // Drop the length of the value (it must be 4)
                else_.drop();

                // Save the source offset to a local.
                let src_local = generator.module.locals.add(ValType::I32);
                else_.local_set(src_local);

                else_
                    .local_get(offset_local)
                    .local_get(src_local)
                    .i32_const(4)
                    .memory_copy(memory, memory);
            }
            SequenceElementType::Other(elem_ty) => {
                generator.write_to_memory(&mut else_, offset_local, 0, elem_ty)?;
            }
        }

        // Push the `some` indicator with destination offset/length.
        else_.i32_const(1).local_get(dest_offset).local_get(length);

        builder.instr(IfElse {
            consequent: then_id,
            alternative: else_id,
        });

        Ok(())
    }
}

#[derive(Debug)]
pub struct Slice;

impl Word for Slice {
    fn name(&self) -> ClarityName {
        "slice?".into()
    }
}

impl ComplexWord for Slice {
    fn traverse(
        &self,
        generator: &mut crate::wasm_generator::WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[clarity::vm::SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 3, args.len(), ArgumentCountCheck::Exact);

        self.charge(generator, builder, 0)?;

        let seq = args.get_expr(0)?;

        // Traverse the sequence, leaving the offset and length on the stack.
        generator.traverse_expr(builder, seq)?;

        // Extend the sequence length to 64-bits.
        builder.unop(UnaryOp::I64ExtendUI32);

        // Save the length to a local.
        let length_local = generator.module.locals.add(ValType::I64);
        builder.local_tee(length_local);

        // Traverse the left position, leaving it on the stack.
        generator.traverse_expr(builder, args.get_expr(1)?)?;

        // Check if the upper 64-bits are greater than 0.
        builder.i64_const(0).binop(BinaryOp::I64GtU);

        // Save the overflow indicator to a local.
        let overflow_local = generator.module.locals.add(ValType::I32);
        builder.local_set(overflow_local);

        // Save the lower part of the index, which will ultimately be
        // multiplied by the element size and added to the source offset to be
        // the offset of the result, to a local.
        let left_local = generator.module.locals.add(ValType::I64);
        builder.local_tee(left_local);

        // Check if the lower 64-bits are greater than 1024x1024 (max value
        // size). We do this check before comparing with the length of the list
        // because it ensures that the multiplication will not overflow.
        builder.i64_const(1024 * 1024).binop(BinaryOp::I64GtU);

        // Or with the overflow indicator.
        builder
            .local_get(overflow_local)
            .binop(BinaryOp::I32Or)
            .local_set(overflow_local);

        // Push the lower bound index onto the stack again.
        builder.local_get(left_local);

        let seq_ty = generator
            .get_expr_type(seq)
            .ok_or_else(|| GeneratorError::TypeError("slice? sequence must be typed".to_string()))?
            .clone();

        // Get the offset of the specified index.
        match &seq_ty {
            TypeSignature::SequenceType(SequenceSubtype::ListType(list)) => {
                // The length of the list in bytes is on the top of the stack. If we
                // divide that by the length of each element, then we'll have the
                // length of the list in elements.
                let elem_ty = list.get_list_item_type().clone();
                let element_length = get_type_size(&elem_ty);
                builder.i64_const(element_length as i64);

                // Multiply the index by the length of each element to get
                // byte-offset into the list.
                builder.binop(BinaryOp::I64Mul);

                Ok(())
            }
            TypeSignature::SequenceType(SequenceSubtype::BufferType(_))
            | TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(_))) => {
                // The index is the same as the byte-offset, so just leave
                // it as-is.
                Ok(())
            }
            TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(_))) => {
                // UTF8 is represented as 32-bit (4 bytes) unicode scalars values.
                // Calculate the total byte length of the list by multiplying the element count by 4
                // Multiplying by 4 is equivalent to performing a bitwise left shift by 2 bits.
                builder.i64_const(2);
                builder.binop(BinaryOp::I64Shl);

                Ok(())
            }
            _ => Err(GeneratorError::TypeError(
                "expected sequence type".to_string(),
            )),
        }?;

        // Save the element offset to the local.
        builder.local_tee(left_local);

        // Check if the element offset is out of range by comparing it to the
        // length of the list.
        builder.binop(BinaryOp::I64LeU);

        // Or with the overflow indicator.
        builder.local_get(overflow_local).binop(BinaryOp::I32Or);

        // Save the overflow indicator to a local.
        builder.local_set(overflow_local);

        // Extend the base offset to 64-bits and save it to a local.
        let base_offset_local = generator.module.locals.add(ValType::I64);
        builder
            .unop(UnaryOp::I64ExtendUI32)
            .local_tee(base_offset_local);

        // Add this left offset to the offset of the list, which is on the top
        // of the stack now, to use as the offset of the slice, if it is in
        // bounds.
        // If it is in bounds, then this truncation to 32-bits will be safe.
        builder
            .local_get(left_local)
            .binop(BinaryOp::I64Add)
            .local_set(left_local);

        // Now check the right bound.

        // First, reload the source length.
        builder.local_get(length_local);

        // Traverse the right position, leaving it on the stack.
        generator.traverse_expr(builder, args.get_expr(2)?)?;

        // Check if the upper 64-bits are greater than 0.
        builder.i64_const(0).binop(BinaryOp::I64GtU);

        // Save the overflow indicator to a local.
        let overflow_local = generator.module.locals.add(ValType::I32);
        builder.local_set(overflow_local);

        // Save the lower part of the index, which will ultimately be
        // multiplied by the element size and added to the source offset to be
        // the offset of the result, to a local.
        let right_local = generator.module.locals.add(ValType::I64);
        builder.local_tee(right_local);

        // Check if the lower 64-bits are greater than 1024x1024 (max value
        // size). We do this check before comparing with the length of the list
        // because it ensures that the multiplication will not overflow.
        builder.i64_const(1024 * 1024).binop(BinaryOp::I64GtU);

        // Or with the overflow indicator.
        builder
            .local_get(overflow_local)
            .binop(BinaryOp::I32Or)
            .local_set(overflow_local);

        // Push the lower bound index onto the stack again.
        builder.local_get(right_local);

        let seq_ty = generator
            .get_expr_type(seq)
            .ok_or_else(|| GeneratorError::TypeError("slice? sequence must be typed".to_string()))?
            .clone();

        // Get the offset of the specified index.
        match &seq_ty {
            TypeSignature::SequenceType(SequenceSubtype::ListType(list)) => {
                // The length of the list in bytes is on the top of the stack. If we
                // divide that by the length of each element, then we'll have the
                // length of the list in elements.
                let elem_ty = list.get_list_item_type().clone();
                let element_length = get_type_size(&elem_ty);
                builder.i64_const(element_length as i64);

                // Multiply the index by the length of each element to get
                // byte-offset into the list.
                builder.binop(BinaryOp::I64Mul);

                Ok(())
            }
            TypeSignature::SequenceType(SequenceSubtype::BufferType(_))
            | TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(_))) => {
                // The index is the same as the byte-offset, so just leave
                // it as-is.
                Ok(())
            }
            TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(_))) => {
                // UTF8 is represented as 32-bit (4 bytes) unicode scalars values.
                // Calculate the total byte length of the list by multiplying the element count by 4
                // Multiplying by 4 is equivalent to performing a bitwise left shift by 2 bits.
                builder.i64_const(2);
                builder.binop(BinaryOp::I64Shl);

                Ok(())
            }
            _ => Err(GeneratorError::TypeError(
                "expected sequence type".to_string(),
            )),
        }?;

        // Save the element offset to the local.
        builder.local_tee(right_local);

        // Check if the element offset is out of range by comparing it to the
        // length of the list.
        builder.binop(BinaryOp::I64LtU);

        // Or with the overflow indicator.
        builder
            .local_get(overflow_local)
            .binop(BinaryOp::I32Or)
            .local_set(overflow_local);

        // Add the right offset to the offset of the list, which is on the top
        // of the stack now, to get the end of the slice, if it is in bounds.
        // If it is in bounds, then this truncation to 32-bits will be safe.
        builder
            .local_get(base_offset_local)
            .local_get(right_local)
            .binop(BinaryOp::I64Add)
            .local_set(right_local);

        // check if length is negative

        builder.local_get(right_local);
        builder.local_get(left_local);

        builder.binop(BinaryOp::I64LtU);

        // Or with the overflow indicator.
        builder
            .local_get(overflow_local)
            .binop(BinaryOp::I32Or)
            .local_set(overflow_local);

        // Push a `0` and a `1` to the stack, for none or some, to be selected
        // by the `select` instruction, using the overflow indicator.
        builder.i32_const(0).i32_const(1).local_get(overflow_local);

        // If either bound is out of range, then return `none`, else return
        // `(some sequence)`, where `sequence` is the slice of the input
        // sequence with offset left and length right - left.
        builder.select(Some(ValType::I32));

        // Now push the offset (`local_left`) and length
        // (`local_right - local_left`). If the result is `none`, then these
        // will just be ignored. If the offsets are in range, then the
        // truncation to 32-bits is safe.
        builder
            .local_get(left_local)
            .unop(UnaryOp::I32WrapI64)
            .local_get(right_local)
            .local_get(left_local)
            .binop(BinaryOp::I64Sub)
            .unop(UnaryOp::I32WrapI64);

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use clarity::vm::Value;

    use crate::tools::{crosscheck, crosscheck_compare_only, evaluate, interpret};

    #[test]
    fn fold_less_than_three_args() {
        let result = evaluate("(fold + (list 1 2 3))");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 3 arguments, got 2"));
    }

    #[test]
    fn fold_more_than_three_args() {
        let result = evaluate("(fold + (list 1 2 3) 1 0)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 3 arguments, got 4"));
    }

    #[test]
    fn append_less_than_two_args() {
        let result = evaluate("(append (list 1 2 3))");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 1"));
    }

    #[test]
    fn append_more_than_two_args() {
        let result = evaluate("(append (list 1 2 3) 1 0)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 3"));
    }

    #[test]
    fn as_max_len_less_than_two_args() {
        let result = evaluate("(as-max-len? (list 1 2 3))");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 1"));
    }

    #[test]
    fn as_max_len_more_than_two_args() {
        let result = evaluate("(as-max-len? (list 1 2 3) 1 0)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 3"));
    }

    #[test]
    fn concat_less_than_two_args() {
        let result = evaluate("(concat (list 1 2 3))");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 1"));
    }

    #[test]
    fn concat_more_than_two_args() {
        let result = evaluate("(concat (list 1 2 3) (list 4 5) (list 6 7))");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 3"));
    }

    #[test]
    fn map_less_than_two_args() {
        let result = evaluate("(map +)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting >= 2 arguments, got 1"));
    }

    #[test]
    fn len_less_than_one_arg() {
        let result = evaluate("(len)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 1 arguments, got 0"));
    }

    #[test]
    fn len_more_than_one_arg() {
        let result = evaluate("(len (list 1 2 3) (list 4 5))");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 1 arguments, got 2"));
    }

    #[test]
    fn element_at_less_than_two_args() {
        let result = evaluate("(element-at? (list 1 2 3))");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 1"));
    }

    #[test]
    fn element_at_more_than_two_args() {
        let result = evaluate("(element-at? (list 1 2 3) 1 0)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 3"));
    }

    #[test]
    fn replace_at_less_than_three_args() {
        let result = evaluate("(replace-at? (list 1 2 3) 2)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 3 arguments, got 2"));
    }

    #[test]
    fn replace_at_more_than_three_args() {
        let result = evaluate("(replace-at? (list 1 2 3) 1 4 0)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 3 arguments, got 4"));
    }

    #[test]
    fn slice_less_than_three_args() {
        let result = evaluate("(slice? (list 1 2 3) u1)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 3 arguments, got 2"));
    }

    #[test]
    fn slice_more_than_three_args() {
        let result = evaluate("(slice? (list 1 2 3) u1 u2 u3)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 3 arguments, got 4"));
    }

    #[test]
    fn append_with_different_length_and_max_length() {
        crosscheck(
            "
                (define-data-var lst (list 20 int) (list))
                (append (var-get lst) 42)
            ",
            Ok(Some(
                Value::cons_list_unsanitized(vec![Value::Int(42)]).unwrap(),
            )),
        )
    }

    #[test]
    fn test_fold_sub() {
        crosscheck(
            r#"
(define-private (sub (x int) (y int))
    (- x y)
)
(fold sub (list 1 2 3 4) 0)
    "#,
            Ok(Some(Value::Int(2))),
        )
    }

    #[test]
    fn test_fold_builtin() {
        crosscheck(r#"(fold + (list 1 2 3 4) 0)"#, Ok(Some(Value::Int(10))))
    }

    #[test]
    fn test_fold_sub_empty() {
        crosscheck(
            r#"
(define-private (sub (x int) (y int))
    (- x y)
)
(define-private (fold-sub (l (list 10 int)))
    (fold sub l 42)
)
(fold-sub (list))
    "#,
            Ok(Some(Value::Int(42))),
        )
    }

    #[test]
    fn test_fold_string_ascii() {
        crosscheck(
            r#"
(define-private (concat-string (a (string-ascii 20)) (b (string-ascii 20)))
    (unwrap-panic (as-max-len? (concat a b) u20))
)
(fold concat-string "cdef" "ab")
    "#,
            Ok(Some(
                Value::string_ascii_from_bytes("fedcab".to_string().into_bytes()).unwrap(),
            )),
        )
    }

    #[test]
    fn test_fold_string_ascii_empty() {
        crosscheck(
            r#"
(define-private (concat-string (a (string-ascii 20)) (b (string-ascii 20)))
    (unwrap-panic (as-max-len? (concat a b) u20))
)
(fold concat-string "" "ab")
    "#,
            Ok(Some(
                Value::string_ascii_from_bytes("ab".to_string().into_bytes()).unwrap(),
            )),
        )
    }

    #[test]
    fn test_fold_string_utf8() {
        crosscheck(
            r#"
(define-private (concat-string (a (string-utf8 20)) (b (string-utf8 20)))
    (unwrap-panic (as-max-len? (concat a b) u20))
)
(fold concat-string u"cdef" u"ab")
    "#,
            Ok(Some(
                Value::string_utf8_from_bytes("fedcab".into()).unwrap(),
            )),
        )
    }

    #[test]
    fn test_fold_string_utf8_b() {
        crosscheck(
            r#"
(define-private (concat-string (a (string-utf8 20)) (b (string-utf8 20)))
    (unwrap-panic (as-max-len? (concat a b) u20))
)
(fold concat-string u"cdef" u"ab\u{1F98A}")
    "#,
            Ok(Some(
                Value::string_utf8_from_bytes("fedcab🦊".into()).unwrap(),
            )),
        )
    }

    #[test]
    fn test_fold_string_utf8_empty() {
        crosscheck(
            r#"
(define-private (concat-string (a (string-utf8 20)) (b (string-utf8 20)))
    (unwrap-panic (as-max-len? (concat a b) u20))
)
(fold concat-string u"" u"ab\u{1F98A}")
    "#,
            Ok(Some(Value::string_utf8_from_bytes("ab🦊".into()).unwrap())),
        )
    }

    #[test]
    fn test_fold_buffer() {
        crosscheck(
            r"
(define-private (concat-buff (a (buff 20)) (b (buff 20)))
    (unwrap-panic (as-max-len? (concat a b) u20))
)
(fold concat-buff 0x03040506 0x0102)
",
            Ok(Some(
                Value::buff_from(vec![0x06, 0x05, 0x04, 0x03, 0x01, 0x02]).unwrap(),
            )),
        )
    }

    #[test]
    fn test_fold_buffer_empty() {
        crosscheck(
            "
(define-private (concat-buff (a (buff 20)) (b (buff 20)))
    (unwrap-panic (as-max-len? (concat a b) u20))
)
(fold concat-buff 0x 0x0102)
",
            Ok(Some(Value::buff_from(vec![0x01, 0x02]).unwrap())),
        )
    }

    #[test]
    fn fold_init() {
        crosscheck(
            "(define-private (foo (index uint) (res (response bool uint)))
            (if (< index u1) (err u0) (ok true))
          )
          (define-private (bar)
            (fold foo (list u0) (ok true))
          )
          (bar)",
            Ok(Some(Value::err_uint(0))),
        );
    }

    #[test]
    fn test_map_simple_list() {
        crosscheck(
            r#"
(define-private (addify (a int))
    (+ a 1)
)
(map addify (list 1 2 3))
        "#,
            Ok(Some(
                Value::cons_list_unsanitized(vec![Value::Int(2), Value::Int(3), Value::Int(4)])
                    .unwrap(),
            )),
        )
    }

    #[test]
    fn test_map_simple_buff() {
        crosscheck(
            r#"
(define-private (zero-or-one (char (buff 1))) (if (is-eq char 0x00) 0x00 0x01))
(map zero-or-one 0x000102)
        "#,
            Ok(Some(
                Value::cons_list_unsanitized(vec![
                    Value::buff_from_byte(0),
                    Value::buff_from_byte(1),
                    Value::buff_from_byte(1),
                ])
                .unwrap(),
            )),
        )
    }

    #[test]
    fn test_map_simple_string_ascii() {
        crosscheck(
            r#"
(define-private (a-or-b (char (string-ascii 1))) (if (is-eq char "a") "a" "b"))
(map a-or-b "aca")
        "#,
            Ok(Some(
                Value::cons_list_unsanitized(vec![
                    Value::string_ascii_from_bytes(vec![0x61]).unwrap(),
                    Value::string_ascii_from_bytes(vec![0x62]).unwrap(),
                    Value::string_ascii_from_bytes(vec![0x61]).unwrap(),
                ])
                .unwrap(),
            )),
        )
    }

    #[test]
    fn test_map_simple_string_utf8() {
        crosscheck(
            r#"
(define-private (a-or-b (char (string-utf8 1))) (if (is-eq char u"a") u"a" u"b"))
(map a-or-b u"aca")
        "#,
            Ok(Some(
                Value::cons_list_unsanitized(vec![
                    Value::string_utf8_from_bytes(vec![0x61]).unwrap(),
                    Value::string_utf8_from_bytes(vec![0x62]).unwrap(),
                    Value::string_utf8_from_bytes(vec![0x61]).unwrap(),
                ])
                .unwrap(),
            )),
        )
    }

    #[test]
    fn test_map() {
        const MAP_FNS: &str = "
(define-private (addify-1 (a int))
  (+ a 1))

(define-private (addify-2 (a int) (b int))
  (+ a b 1))
";

        let a = &format!("{MAP_FNS} (map addify-1 (list 1 2 3))");
        crosscheck(a, evaluate("(list 2 3 4)"));

        let b = &format!("{MAP_FNS} (map addify-2 (list 1 2 3) (list 7 8))");
        crosscheck(b, evaluate("(list 9 11)"));
    }

    #[test]
    fn test_heterogeneus() {
        const MAP_HETERO: &str = "
(define-private (selectron (a bool) (b int) (c int))
  (if a b c))";

        let a = &format!(
            "{MAP_HETERO}
(map selectron
  (list true false false true)
  (list 1 2 3 4)
  (list 10 20 30))"
        );
        crosscheck(a, evaluate("(list 1 20 30)"));
    }

    #[test]
    fn test_builtin() {
        let a = "
(map +
  (list 1 2 3 4)
  (list 10 20 30))
";
        crosscheck(a, evaluate("(list 11 22 33)"))
    }

    #[test]
    fn map_and() {
        let a = "
(map and
  (list true true true)
  (list false true true)
  (list false false true))
";
        crosscheck(a, evaluate("(list false false true)"))
    }

    #[test]
    fn map_or() {
        let a = "
(map or
  (list true false true)
  (list false false true)
  (list false false false))
";
        crosscheck(a, evaluate("(list true false true)"));
    }

    #[test]
    fn map_divide() {
        let a = "(map / (list 1 4 9) (list 1 2 3))";
        crosscheck(a, evaluate("(list 1 2 3)"));
    }

    #[test]
    fn map_less_than_or_equal() {
        let a = "(map <= (list 1 3 3) (list 1 2 3))";
        crosscheck(a, evaluate("(list true false true)"));
    }

    #[test]
    fn map_less_than() {
        let a = "(map < (list 1 2 3) (list 1 3 3))";
        crosscheck(a, evaluate("(list false true false)"));
    }

    #[test]
    fn map_greater_than() {
        let a = "(map > (list 1 3 3) (list 1 2 3))";
        crosscheck(a, evaluate("(list false true false)"));
    }

    #[test]
    fn map_greater_than_or_equal() {
        let a = "(map >= (list 1 2 3) (list 1 3 3))";
        crosscheck(a, evaluate("(list true false true)"));
    }

    #[test]
    fn map_to_int() {
        let a = "(map to-int (list u1 u2 u3))";
        crosscheck(a, evaluate("(list 1 2 3)"));
    }

    #[test]
    fn map_log2() {
        let a = "(map log2 (list 1 2 3))";
        crosscheck(a, evaluate("(list 0 1 1)"));
    }

    #[test]
    fn map_mod() {
        let a = "(map mod (list 10 15 5) (list 1 2 3))";
        crosscheck(a, evaluate("(list 0 1 2)"));
    }

    #[test]
    fn map_mul() {
        let a = "(map * (list 1 2 3) (list 1 2 3))";
        crosscheck(a, evaluate("(list 1 4 9)"));
    }

    #[test]
    fn map_not() {
        let a = "(map not (list true false true false))";
        crosscheck(a, evaluate("(list false true false true)"));
    }

    #[test]
    fn map_pow() {
        let a = "(map pow (list 1 2 3) (list 1 2 3))";
        crosscheck(a, evaluate("(list 1 4 27)"));
    }

    #[test]
    fn map_sha512_256() {
        let a = "(map sha512/256 (list 1 2 3))";
        crosscheck(
            a,
            evaluate(
                "
        (list
            0x515a7e92e7c60522db968d81ff70b80818fc17aeabbec36baf0dda2812e94a86
            0x541f557997791a762051eceb7c1069d9c903067d1d020bd38da294b10b0d680c
            0xe8107bb16a6b5f0cac737990336f93bc82bb678ba8a9cba86be3c3f818a34230
        )",
            ),
        );
    }

    #[test]
    fn map_sqrti() {
        let a = "(map sqrti (list 1 4 9))";
        crosscheck(a, evaluate("(list 1 2 3)"));
    }

    #[test]
    fn map_to_uint() {
        let a = "(map to-uint (list 1 2 3))";
        crosscheck(a, evaluate("(list u1 u2 u3)"));
    }

    #[test]
    fn map_xor() {
        let a = "(map xor (list 5 10 60) (list 1 2 -3))";
        crosscheck(a, evaluate("(list 4 8 -63)"));
    }

    #[test]
    fn map_keccak256() {
        let a = "(map keccak256 (list 1 2 3))";
        crosscheck(
            a,
            evaluate(
                "
        (list
            0x97550c84a9e30d01461a29ac1c54c29e82c1925ee78b2ee1776d9e20c0183334
            0xf74616ab34b70062ff83d0f3459bee08066c0b32ed44ed6f4c52723036ee295c
            0x48dd032f5ebe0286a7aae330fe25a2fbe8e8288814e8f7ccb149f024611e71b1
        )",
            ),
        );
    }

    #[test]
    fn as_max_len_string_utf8() {
        crosscheck(
            r#"(as-max-len? u"hello" u16)"#,
            Ok(Some(
                Value::some(
                    Value::string_utf8_from_string_utf8_literal("hello".to_owned()).unwrap(),
                )
                .unwrap(),
            )),
        );
    }

    #[test]
    fn fold() {
        crosscheck(
            "
(define-private (sub (x int) (y int))
    (- x y))

(define-public (fold-sub)
    (ok (fold sub (list 1 2 3 4) 0)))

(fold-sub)
",
            evaluate("(ok 2)"),
        )
    }

    #[test]
    fn as_max_len_list() {
        crosscheck(
            r#"(as-max-len? (list 42 21) u2)"#,
            Ok(Some(
                Value::some(
                    Value::cons_list_unsanitized(vec![Value::Int(42), Value::Int(21)]).unwrap(),
                )
                .unwrap(),
            )),
        );
    }

    #[test]
    fn as_max_len_string_0() {
        crosscheck(
            r#"(as-max-len? "" u0)"#,
            Ok(Some(
                Value::some(Value::string_ascii_from_bytes(vec![]).unwrap()).unwrap(),
            )),
        );
    }

    #[test]
    fn as_max_len_list_0() {
        crosscheck(
            r#"(as-max-len? (list) u0)"#,
            Ok(Some(
                Value::some(Value::cons_list_unsanitized(vec![]).unwrap()).unwrap(),
            )),
        )
    }

    #[test]
    fn fold_bench() {
        crosscheck(
            "
(define-private (add-square (x int) (y int))
    (+ (* x x) y))

(define-public (fold-add-square (l (list 8192 int)) (init int))
    (ok (fold add-square l init)))

(fold-add-square (list 1 2 3 4) 3)
",
            evaluate("(ok 33)"),
        );
    }

    #[test]
    fn fold_sub() {
        crosscheck(
            "
(define-private (subalot (a int) (b int))
    (- b a))

(fold subalot (list 1 2 3 4 5) 399)
",
            Ok(Some(Value::Int(384))),
        );
    }

    #[test]
    fn map_sub() {
        crosscheck(
            "
(map - (list 1 2 3 4) (list 4 5 7 9) (list 41 51 71 9999))
",
            evaluate("(list -44 -54 -75 -10004)"),
        );
    }

    #[test]
    fn map_mul_regression() {
        crosscheck(
            "
(map * (list 0) (list 5) (list -34028236692093846346337460743176821146))
",
            evaluate("(list 0)"),
        );
    }

    #[test]
    fn map_unary() {
        crosscheck("(map - (list 10 20 30))", evaluate("(list -10 -20 -30)"));
    }

    #[test]
    fn map_repeated() {
        crosscheck(
            &"(map + (list 1 2 3) (list 1 2 3) (list 1 2 3))".repeat(700),
            Ok(Some(
                Value::cons_list_unsanitized(vec![Value::Int(3), Value::Int(6), Value::Int(9)])
                    .unwrap(),
            )),
        );
    }

    #[test]
    fn double_append() {
        let snippet = "(append (append (list 1) 2) 3)";

        let expected =
            Value::cons_list_unsanitized(vec![Value::Int(1), Value::Int(2), Value::Int(3)])
                .unwrap();

        crosscheck(snippet, Ok(Some(expected)))
    }

    #[test]
    fn fold_with_response_partial_acc() {
        let snippet = "
            (define-private (foo (a (response int bool)) (b (response int uint)))
                (match b
                    bok (ok (+ (unwrap-panic a) bok))
                    berr (ok (+ (unwrap-panic a) (to-int berr)))
                )
            )
            (fold foo (list (ok 1)) (ok 2))
        ";
        crosscheck(snippet, Ok(Some(Value::okay(Value::Int(3)).unwrap())));
    }

    #[test]
    fn fold_with_response_full_acc() {
        let snippet = "
            (define-private (foo (a (response int bool)) (b (response int uint)))
                (match b
                    bok (ok (+ (unwrap-panic a) bok))
                    berr (err (+ (to-uint (unwrap-panic a)) berr))
                )
            )
            (fold foo (list (ok 1)) (ok 2))
        ";
        crosscheck(snippet, Ok(Some(Value::okay(Value::Int(3)).unwrap())));
    }

    #[test]
    fn map_needs_ducktyping() {
        let snippet = r#"
            (define-private (foo (a int))
                (ok a)
            )

            (if true (map foo (list 1)) (list (err "unreachable")))
        "#;

        crosscheck(
            snippet,
            Ok(Some(
                Value::cons_list_unsanitized(vec![Value::okay(Value::Int(1)).unwrap()]).unwrap(),
            )),
        );
    }

    #[test]
    fn map_multiple_argument_needs_workaround() {
        let snippet = "
            (define-private (foo (a int) (b (response int int)))
                (+ a (unwrap-panic b))
            )

            (map foo (list 1 2 3) (list (ok 1) (ok 2) (ok 3)))
        ";

        let expected =
            Value::cons_list_unsanitized([2, 4, 6].into_iter().map(Value::Int).collect()).unwrap();

        crosscheck(snippet, Ok(Some(expected)));
    }

    #[test]
    fn unit_fold_repsonses_full_type() {
        let snippet = "
(define-private (knus (a (response int int))
                      (b (response int int)))
  (match a
    a1 (match b
      b1 (err (+ a1 b1))
      b2 (ok  (- a1 b2)))
    a2 (match b
      b3 (ok  (+ a2 b3))
      b4 (err (- a2 b4)))))

(fold knus (list (ok 1)) (err 0))";

        crosscheck_compare_only(snippet);
    }

    #[test]
    fn unit_fold_repsonses_partial_type() {
        let snippet = "
(define-private (knus (a (response int int))
                      (b (response int int)))
  (match a
    a1 (match b
      b1 (err (+ a1 b1))
      b2 (ok  (- a1 b2)))
    a2 (match b
      b3 (ok  (+ a2 b3))
      b4 (err (- a2 b4)))))

(fold knus (list (err 1)) (err 0))";

        crosscheck_compare_only(snippet);
    }

    #[test]
    fn test_large_list() {
        let n = 50000 / 2 + 1;
        crosscheck_compare_only(&format!("(list {})", "9922 ".repeat(n)));
    }

    //
    // Module with tests that should only be executed
    // when running Clarity::V2 or Clarity::v3.
    //
    #[cfg(not(feature = "test-clarity-v1"))]
    #[cfg(test)]
    mod clarity_v2_v3 {
        use clarity::vm::errors::RuntimeErrorType;

        use super::*;

        #[test]
        fn replace_at_with_different_length_and_max_length() {
            crosscheck(
                "
                (define-data-var lst (list 20 int) (list 1))
                (replace-at? (var-get lst) u0 42)
            ",
                Ok(Some(
                    Value::some(Value::cons_list_unsanitized(vec![Value::Int(42)]).unwrap())
                        .unwrap(),
                )),
            )
        }

        #[test]
        fn test_map_mixed() {
            crosscheck(
                r#"
    (define-private (add-everything
        (a int)
        (b uint)
        (c (string-ascii 1))
        (d (string-utf8 1))
        (e (buff 1))
        )
        (+
            a
            (to-int b)
            (unwrap-panic (string-to-int? c))
            (unwrap-panic (string-to-int? d))
            (buff-to-int-be e)
        )
    )
    (map add-everything
        (list 1 2 3)
        (list u1 u2 u3)
        "123"
        u"123"
        0x010203
    )
            "#,
                Ok(Some(
                    Value::cons_list_unsanitized(vec![
                        Value::Int(5),
                        Value::Int(10),
                        Value::Int(15),
                    ])
                    .unwrap(),
                )),
            )
        }

        #[test]
        fn test_builtin_string() {
            let a = r#"
    (map >
      "ab"
      "ba"
    )"#;
            crosscheck(a, evaluate("(list false true)"));
        }

        #[test]
        fn map_large_result() {
            let n = 65535; // max legal `(list <size> uint)` size
            let buf = (0..n)
                .map(|i| format!("{:02x}", i % 256))
                .collect::<Vec<_>>()
                .join("");
            let snippet = format!(
                r#"
            (define-private (foo (a (buff 1))) (buff-to-uint-be a))
            (map foo 0x{buf})
            "#
            );

            crosscheck(
                &snippet,
                Ok(Some(
                    Value::cons_list_unsanitized((0..n).map(|c| Value::UInt(c % 256)).collect())
                        .unwrap(),
                )),
            );
        }

        #[test]
        fn slice_right_lt_left() {
            crosscheck("(slice? \"abc\" u1 u0)", evaluate("none"));
            crosscheck("(slice? \"abc\" u2 u1)", evaluate("none"));
        }

        #[test]
        fn slice_overflow() {
            crosscheck("(slice? \"abc\" u4 u5)", evaluate("none"));
        }

        #[test]
        fn slice() {
            crosscheck("(slice? \"abc\" u1 u2)", evaluate("(some \"b\")"));
        }

        #[test]
        fn slice_null() {
            crosscheck("(slice? \"abc\" u0 u0)", evaluate("(some \"\")"));
            crosscheck("(slice? \"abc\" u1 u1)", evaluate("(some \"\")"));
            crosscheck("(slice? \"abc\" u2 u2)", evaluate("(some \"\")"));
        }

        #[test]
        fn slice_full() {
            crosscheck("(slice? \"abc\" u0 u3)", evaluate("(some \"abc\")"));
        }

        #[test]
        fn replace_element_cannot_be_empty_buff() {
            let snippet = r#"(replace-at? 0x12345678 u0 0x)"#;

            crosscheck(
                snippet,
                Err(clarity::vm::errors::Error::Runtime(
                    RuntimeErrorType::BadTypeConstruction,
                    Some(Vec::new()),
                )),
            )
        }

        #[test]
        fn replace_element_cannot_be_empty_string_ascii() {
            let snippet = r#"(replace-at? "abcd" u0 "")"#;

            crosscheck(
                snippet,
                Err(clarity::vm::errors::Error::Runtime(
                    RuntimeErrorType::BadTypeConstruction,
                    Some(Vec::new()),
                )),
            )
        }

        #[test]
        fn replace_element_cannot_be_empty_string_utf8() {
            let snippet = r#"(replace-at? u"abcd" u0 u"")"#;

            crosscheck(
                snippet,
                Err(clarity::vm::errors::Error::Runtime(
                    RuntimeErrorType::BadTypeConstruction,
                    Some(Vec::new()),
                )),
            )
        }
        #[test]
        fn map_bit_and() {
            let a = "(map bit-and (list 1 2 3) (list 1 7 6) (list 1 15 15))";
            crosscheck(a, evaluate("(list 1 2 2)"));
        }

        #[test]
        fn map_bit_not() {
            let a = "(map bit-not (list 1 2 3))";
            crosscheck(a, evaluate("(list -2 -3 -4)"));
        }

        #[test]
        fn map_bit_or() {
            let a = "(map bit-or (list 1 2 3) (list 1 7 6) (list 1 15 15))";
            crosscheck(a, evaluate("(list 1 15 15)"));
        }

        #[test]
        fn map_bit_shift_left() {
            let a = "(map bit-shift-left (list u1 u2 u3) (list u2 u3 u4))";
            crosscheck(a, evaluate("(list u4 u16 u48)"));
        }

        #[test]
        fn map_bit_shift_right() {
            let a = "(map bit-shift-right (list u4 u16 u48) (list u2 u3 u4))";
            crosscheck(a, evaluate("(list u1 u2 u3)"));
        }

        #[test]
        fn map_bit_xor() {
            let a = "(map bit-xor (list 4 16 48) (list 2 3 4) (list 3 4 5))";
            crosscheck(a, evaluate("(list 5 23 49)"));
        }

        #[test]
        fn map_buff_to_int_be() {
            let a = "(map buff-to-int-be (list 0x010203 0x040506 0x070809))";
            crosscheck(a, evaluate("(list 66051 263430 460809)"));
        }

        #[test]
        fn map_buff_to_int_le() {
            let a = "(map buff-to-int-le (list 0x010203 0x040506 0x070809))";
            crosscheck(a, evaluate("(list 197121 394500 591879)"));
        }

        #[test]
        fn map_buff_to_uint_be() {
            let a = "(map buff-to-uint-be (list 0x010203 0x040506 0x070809))";
            crosscheck(a, evaluate("(list u66051 u263430 u460809)"));
        }

        #[test]
        fn map_buff_to_uint_le() {
            let a = "(map buff-to-uint-le (list 0x010203 0x040506 0x070809))";
            crosscheck(a, evaluate("(list u197121 u394500 u591879)"));
        }
        #[test]
        fn map_is_standard() {
            let a = "(map is-standard (list 'ST3X6QWWETNBZWGBK6DRGTR1KX50S74D3425Q1TPK 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR))";
            crosscheck(a, evaluate("(list true false)"));
        }

        #[test]
        fn map_principal_construct() {
            let snippet = "
(define-data-var index-local uint u0)
(define-data-var list-local (list 100 (buff 1)) (list ))
(define-public (test-principal-construct)
  (begin
    (var-set list-local (list 0x1a 0x1a))
    (ok (map test-principal-construct-inner (list 0xfa6bf38ed557fe417333710d6033e9419391a320 0x164247d6f2b425ac5771423ae6c80c754f7172b0)))
  )
)

(define-private (test-principal-construct-inner (pub-key-hash (buff 20)))
  (let
    (
      (index (var-get index-local))
    )
    (var-set index-local (+ u1 (var-get index-local)))
    (principal-construct? (unwrap-panic (element-at? (var-get list-local) index)) pub-key-hash)
  )
)
(test-principal-construct)";
            crosscheck(snippet, evaluate("
        (ok
            (list
                (ok 'ST3X6QWWETNBZWGBK6DRGTR1KX50S74D3425Q1TPK) (ok 'STB44HYPYAT2BB2QE513NSP81HTMYWBJP02HPGK6)
            )
        )"));
        }

        #[test]
        fn map_principal_destruct() {
            let a = "(map principal-destruct? (list 'ST3X6QWWETNBZWGBK6DRGTR1KX50S74D3425Q1TPK 'STB44HYPYAT2BB2QE513NSP81HTMYWBJP02HPGK6))";
            crosscheck(
                a,
                evaluate(
                    "
        (list
            (ok
                (tuple
                    (hash-bytes 0xfa6bf38ed557fe417333710d6033e9419391a320)
                    (name none)
                    (version 0x1a)
                )
            )
            (ok
                (tuple
                    (hash-bytes 0x164247d6f2b425ac5771423ae6c80c754f7172b0)
                    (name none)
                    (version 0x1a)
                )
            )
        )",
                ),
            );
        }

        #[test]
        fn map_string_to_int() {
            let a = "(map string-to-int? (list \"1\" \"2\" \"3\"))";
            crosscheck(a, evaluate("(list (some 1) (some 2) (some 3))"));
        }

        #[test]
        fn map_string_to_uint() {
            let a = "(map string-to-uint? (list \"1\" \"2\" \"3\"))";
            crosscheck(a, evaluate("(list (some u1) (some u2) (some u3))"));
        }

        #[test]
        fn map_int_to_ascii() {
            let a = "(map int-to-ascii (list u1 u2 u3))";
            crosscheck(a, evaluate("(list \"1\" \"2\" \"3\")"));
        }

        #[test]
        fn map_int_to_utf8() {
            let a = "(map int-to-utf8 (list u1 u2 u3))";
            crosscheck(a, evaluate("(list u\"1\" u\"2\" u\"3\")"));
        }
    }

    #[test]
    fn fold_cannot_oom() {
        // this comes from a proptest, which is why this is so big and the type/values look so weird.
        let snippet = r#"
            (define-data-var res (list 10 {HUjqhooZkWOxCBP: {FptMqjTJNUNgg: (string-ascii 86),aXGLXMMVAwPHl: (string-utf8 6),dPliquaWzyA: (string-utf8 6),},KjI: (buff 106),LlhgxuCkgvY: uint,cLzfhdGIFWt: principal,cT: (string-utf8 5),}) (list))

            (define-private (accumulate (elem {HUjqhooZkWOxCBP: {FptMqjTJNUNgg: (string-ascii 86),aXGLXMMVAwPHl: (string-utf8 6),dPliquaWzyA: (string-utf8 6),},KjI: (buff 106),LlhgxuCkgvY: uint,cLzfhdGIFWt: principal,cT: (string-utf8 5),}) (acc (list 20 {HUjqhooZkWOxCBP: {FptMqjTJNUNgg: (string-ascii 86),aXGLXMMVAwPHl: (string-utf8 6),dPliquaWzyA: (string-utf8 6),},KjI: (buff 106),LlhgxuCkgvY: uint,cLzfhdGIFWt: principal,cT: (string-utf8 5),})))
                (unwrap-panic (as-max-len? (append acc elem) u20))
            )

            (fold accumulate
                (list
                    (tuple (HUjqhooZkWOxCBP (tuple (FptMqjTJNUNgg "}R+/PK>jm//o`a-GN(3\"aK! lFiX:1kZ94nwxT`;P@@1DT=`N<NN@pdPHN2zTb<Q*[mAE5{BUF8ge d6\\Af^f:") (aXGLXMMVAwPHl u"}\u{9B76E}::\u{771C3}]") (dPliquaWzyA u"\u{1F574}Z\u{8A24B}p$\u{FEFF}"))) (KjI 0x1d16e49ed0a6780ebd431192856b2efba35c0d0a7072efacca76372d6778e35e485434435a10e6cdbc070ff522e07bec5b242d40dcf4f00df6c2de55c8aba8d67c8942f3d7b3fe201bc7722352a52ea9ae725ac6a87a5136b275e272e85db812801174ce6f947c2644bc) (LlhgxuCkgvY u266584415760704871682925682368427159672) (cLzfhdGIFWt 'SC7RDYK8R075CT65GJF46BWFBEPZD3F4107BECX5) (cT u"\u{F3F0}\u{D}\u{32C69}`\u{468}"))
                    (tuple (HUjqhooZkWOxCBP (tuple (FptMqjTJNUNgg "YYAXt;[.xV?do;!?_vcv+UIuyUQXI#vWhLSr[L**n!xjrORli-rRu8Z#!C>j7cM{C;vke8-QJX;G<Zh@t4u\\j$") (aXGLXMMVAwPHl u"\u{1B}`\u{A5}h\u{BFD24}`") (dPliquaWzyA u"\u{23A}{\u{103C41}7\u{6B8B3}\u{0}"))) (KjI 0x77099cb8af6c27735855f8e22397c05d3b83345ea374287362a36c35069164497628c984ff26d3e5398cd7d98c47c49c0c84fe275ca96dd37f5545930e9c52794521cfb5d043136b5c02190194525a66d131f27ce9847d39687e35289eb3dfd78152309dc999dc437431) (LlhgxuCkgvY u290403534025191254672308036914300859385) (cLzfhdGIFWt 'S31VQ762JEFDBRG2AN6GMJ46Q5A42CVN81SYRTHH5) (cT u"\u{9}\u{D}:F}"))
                    (tuple (HUjqhooZkWOxCBP (tuple (FptMqjTJNUNgg "$nrO.#;n6}efpH)4<&<nsg(|{j6xL*4Kg1:Otm?D=>DI0be\"C_7j[%TO\\D-(b 5zvF[Ux#2Cl|l])FHmzmya1S") (aXGLXMMVAwPHl u"x&j\u{A5}\u{9FB98}a") (dPliquaWzyA u"`\u{23A}\u{B}\u{23A}\u{BE}&"))) (KjI 0xd4c3155ee99c15bfd2163f0d6deb998e003d967cee91cb168bfe6c7ddd066b15294e88842538e5245d0b579242bf069c21b4601b121fa214a030195ec4dc66d697d9bbac32f75cb33939c677529944fcb2421455679a85736eeea0168d4090285f29d47b3835d10fce90) (LlhgxuCkgvY u112340289429567555812382063329072771939) (cLzfhdGIFWt 'SX33HWZ9D8N62BS4PWEE1TXAHXJS8CT77C3MZT223) (cT u"U\u{106EBA}:u~"))
                    (tuple (HUjqhooZkWOxCBP (tuple (FptMqjTJNUNgg "/rG?'{p&L|LHM7m0Pf'zDaN@%5TTSI`IjlS!pAW#kSIGq]=I\\gTV(\"-1#GD^DtweW=Fr8v1m* VIZEzm'mb86n") (aXGLXMMVAwPHl u"\u{202E}\u{9DE06}*\u{468}\u{B}`") (dPliquaWzyA u"\u{7F}\u{A}=6\u{6342C}\u{F6}"))) (KjI 0xd8a431afc574142072940c1d80fa7a76c8079132e9b3ad99f5a7af0df8bd06da102792d69fb489bd00d5857df298c7ab7685bbca38a6c442bb34d152ff1836298d2bde2fd38394674fbc2d3a2af0208a7864bd741808987ab3cd6bdcbd061854c931433d34a515f7b912) (LlhgxuCkgvY u180909627654866266770371222299909290078) (cLzfhdGIFWt 'SGJGSDVNSCCWATPE7QN38E3VD7ZWQFGR8AT296Y0) (cT u"\u{361D9}&\u{D}'\u{B}"))
                    (tuple (HUjqhooZkWOxCBP (tuple (FptMqjTJNUNgg "zBwm8ArbBL!T >kLsQ@x+za\"a*4Q9II14:\\>Ff\"sM|D8dF63(?I,j}U:\\SXFj{<Fux|?q<WRskA{n:y29@[QF:") (aXGLXMMVAwPHl u"$\u{202E}\u{94DCC}\u{202E}'\u{C4762}") (dPliquaWzyA u"'`\u{F8EAE}\u{0}\u{9}\u{0}"))) (KjI 0xdfdf24465c485e22c372dd0a0acedbac90fd2f68b703af66002ab5d437f2eb1df61472580925d7846d2322bdc1d37664a553dac7ea25269f73687e49e37e95ebfb2057ad388cfb3bcb08797fb38a8f9ed08751d47f0e8f5ede286afb566089aad97a933abe292e1b71a9) (LlhgxuCkgvY u52803673722867896838744451212775160657) (cLzfhdGIFWt 'SG3VNED7GQKFMBX92CR6375GRJ0S1SVTS29EHK36X.MMFKlfGOxhOfdVapvrPWXoCKxBDnILfe) (cT u"\u{97}\u{B}v\u{FFFD}e"))
                    (tuple (HUjqhooZkWOxCBP (tuple (FptMqjTJNUNgg "X\"LbZDW)tQkjd?DB+(9OaK5UmYL6Eu;.$)2H8(0S.lN*')Y`'[h}DWz\\Dc l-/G('o:;?'\\t.#?gD,e{$Z9uO?") (aXGLXMMVAwPHl u"\u{23A}\u{1F574}\u{8EF57}{\"\u{107F93}") (dPliquaWzyA u"\u{E3B9D}`.2\u{C14BF}\u{D1CD9}"))) (KjI 0x81377e6109e49e6e50b37894cf5e259a6175d5c68cd37cbd3469a778bf86ea1956d997f9500d968cac6aa20f34444b93c313b9139bbeef06c2fd6902ffc913bf0aae2abbefc338babec1022e1bbd8a8df3fccaab3aa17108254c8e6b415d3edcfd9e0738bca4ea3c2749) (LlhgxuCkgvY u86526039109882199526131538780536033377) (cLzfhdGIFWt 'S92XK4FCQJCXK2AES16WVJWP66689MGXKHSTJW6NV.IopLHoUBzNdvRaEnoDjDri) (cT u".[\u{3EBDC}?\u{51CF4}"))
                    (tuple (HUjqhooZkWOxCBP (tuple (FptMqjTJNUNgg "qEM?kK^:^y0hBKdX2KGx4j(2,mJWF5whQ&{9]zq9M?hO`}7-J}7`#&yz(V/mSe{-f)ydt({0w*xhBIHedB+qNd") (aXGLXMMVAwPHl u"\u{10DB3B}|\u{B}<\u{D4}$") (dPliquaWzyA u"u<&\u{5474A}\u{FFFD}\u{37831}"))) (KjI 0x883e5fba16581ffaf0760531bad9760c3bfad38f585ed395bcbd87fea722737a545882d339e212b2473c20ed5df75747af5dc6c285fa7291446f4cd640b11ed0da45a5f65254dc03ceda920eda93a366ed457cb96769826e9dcbe793755b596f918b12e1156c14c6aac8) (LlhgxuCkgvY u54905774066604940256152088345328184940) (cLzfhdGIFWt 'SDFXQR791656BCGQJE2PBM7Z10134852HX2X22HJ) (cT u"5f`\u{468}\u{63CCA}"))
                    (tuple (HUjqhooZkWOxCBP (tuple (FptMqjTJNUNgg "?1b?U*-}@{%{T(Z9/fIcV$KD,\"Es-TrcnS`.HZTYnY[00l& Q*Qk,kio2@x<&N{r3)`6f`.{SKGcBEzd >c[5p") (aXGLXMMVAwPHl u"=\u{4856D}\u{23A}{\u{0}:") (dPliquaWzyA u"\u{468}%\u{E4}\"\u{202E}\u{23A}"))) (KjI 0x65632440e4cb2a9c12821ba9e6c6dca8352f081b8b18e8fd40df33110adf2084c0bb7290e1fd4fd68e0c9de78ed8c1d4fc08879a1b59b17776a4b7109e2cc661c5af67048d1a094c6daff3f467401a13b6d107f963742be1b6ca39d7fb0b0f3824066311120113e2a8e3) (LlhgxuCkgvY u55353300269423966798277265961322403298) (cLzfhdGIFWt 'SW3JYDPJMCDCT5M42TFVXSG07NN1FRY1P16N4DDKW.PsuTiLAbPJiaTjsYRKFfrca) (cT u"{.\u{F04E9}\u{A}k"))
                )
                (var-get res)
            )
        "#;

        let expected = interpret(
            r#"
                (list
                    (tuple (HUjqhooZkWOxCBP (tuple (FptMqjTJNUNgg "}R+/PK>jm//o`a-GN(3\"aK! lFiX:1kZ94nwxT`;P@@1DT=`N<NN@pdPHN2zTb<Q*[mAE5{BUF8ge d6\\Af^f:") (aXGLXMMVAwPHl u"}\u{9B76E}::\u{771C3}]") (dPliquaWzyA u"\u{1F574}Z\u{8A24B}p$\u{FEFF}"))) (KjI 0x1d16e49ed0a6780ebd431192856b2efba35c0d0a7072efacca76372d6778e35e485434435a10e6cdbc070ff522e07bec5b242d40dcf4f00df6c2de55c8aba8d67c8942f3d7b3fe201bc7722352a52ea9ae725ac6a87a5136b275e272e85db812801174ce6f947c2644bc) (LlhgxuCkgvY u266584415760704871682925682368427159672) (cLzfhdGIFWt 'SC7RDYK8R075CT65GJF46BWFBEPZD3F4107BECX5) (cT u"\u{F3F0}\u{D}\u{32C69}`\u{468}"))
                    (tuple (HUjqhooZkWOxCBP (tuple (FptMqjTJNUNgg "YYAXt;[.xV?do;!?_vcv+UIuyUQXI#vWhLSr[L**n!xjrORli-rRu8Z#!C>j7cM{C;vke8-QJX;G<Zh@t4u\\j$") (aXGLXMMVAwPHl u"\u{1B}`\u{A5}h\u{BFD24}`") (dPliquaWzyA u"\u{23A}{\u{103C41}7\u{6B8B3}\u{0}"))) (KjI 0x77099cb8af6c27735855f8e22397c05d3b83345ea374287362a36c35069164497628c984ff26d3e5398cd7d98c47c49c0c84fe275ca96dd37f5545930e9c52794521cfb5d043136b5c02190194525a66d131f27ce9847d39687e35289eb3dfd78152309dc999dc437431) (LlhgxuCkgvY u290403534025191254672308036914300859385) (cLzfhdGIFWt 'S31VQ762JEFDBRG2AN6GMJ46Q5A42CVN81SYRTHH5) (cT u"\u{9}\u{D}:F}"))
                    (tuple (HUjqhooZkWOxCBP (tuple (FptMqjTJNUNgg "$nrO.#;n6}efpH)4<&<nsg(|{j6xL*4Kg1:Otm?D=>DI0be\"C_7j[%TO\\D-(b 5zvF[Ux#2Cl|l])FHmzmya1S") (aXGLXMMVAwPHl u"x&j\u{A5}\u{9FB98}a") (dPliquaWzyA u"`\u{23A}\u{B}\u{23A}\u{BE}&"))) (KjI 0xd4c3155ee99c15bfd2163f0d6deb998e003d967cee91cb168bfe6c7ddd066b15294e88842538e5245d0b579242bf069c21b4601b121fa214a030195ec4dc66d697d9bbac32f75cb33939c677529944fcb2421455679a85736eeea0168d4090285f29d47b3835d10fce90) (LlhgxuCkgvY u112340289429567555812382063329072771939) (cLzfhdGIFWt 'SX33HWZ9D8N62BS4PWEE1TXAHXJS8CT77C3MZT223) (cT u"U\u{106EBA}:u~"))
                    (tuple (HUjqhooZkWOxCBP (tuple (FptMqjTJNUNgg "/rG?'{p&L|LHM7m0Pf'zDaN@%5TTSI`IjlS!pAW#kSIGq]=I\\gTV(\"-1#GD^DtweW=Fr8v1m* VIZEzm'mb86n") (aXGLXMMVAwPHl u"\u{202E}\u{9DE06}*\u{468}\u{B}`") (dPliquaWzyA u"\u{7F}\u{A}=6\u{6342C}\u{F6}"))) (KjI 0xd8a431afc574142072940c1d80fa7a76c8079132e9b3ad99f5a7af0df8bd06da102792d69fb489bd00d5857df298c7ab7685bbca38a6c442bb34d152ff1836298d2bde2fd38394674fbc2d3a2af0208a7864bd741808987ab3cd6bdcbd061854c931433d34a515f7b912) (LlhgxuCkgvY u180909627654866266770371222299909290078) (cLzfhdGIFWt 'SGJGSDVNSCCWATPE7QN38E3VD7ZWQFGR8AT296Y0) (cT u"\u{361D9}&\u{D}'\u{B}"))
                    (tuple (HUjqhooZkWOxCBP (tuple (FptMqjTJNUNgg "zBwm8ArbBL!T >kLsQ@x+za\"a*4Q9II14:\\>Ff\"sM|D8dF63(?I,j}U:\\SXFj{<Fux|?q<WRskA{n:y29@[QF:") (aXGLXMMVAwPHl u"$\u{202E}\u{94DCC}\u{202E}'\u{C4762}") (dPliquaWzyA u"'`\u{F8EAE}\u{0}\u{9}\u{0}"))) (KjI 0xdfdf24465c485e22c372dd0a0acedbac90fd2f68b703af66002ab5d437f2eb1df61472580925d7846d2322bdc1d37664a553dac7ea25269f73687e49e37e95ebfb2057ad388cfb3bcb08797fb38a8f9ed08751d47f0e8f5ede286afb566089aad97a933abe292e1b71a9) (LlhgxuCkgvY u52803673722867896838744451212775160657) (cLzfhdGIFWt 'SG3VNED7GQKFMBX92CR6375GRJ0S1SVTS29EHK36X.MMFKlfGOxhOfdVapvrPWXoCKxBDnILfe) (cT u"\u{97}\u{B}v\u{FFFD}e"))
                    (tuple (HUjqhooZkWOxCBP (tuple (FptMqjTJNUNgg "X\"LbZDW)tQkjd?DB+(9OaK5UmYL6Eu;.$)2H8(0S.lN*')Y`'[h}DWz\\Dc l-/G('o:;?'\\t.#?gD,e{$Z9uO?") (aXGLXMMVAwPHl u"\u{23A}\u{1F574}\u{8EF57}{\"\u{107F93}") (dPliquaWzyA u"\u{E3B9D}`.2\u{C14BF}\u{D1CD9}"))) (KjI 0x81377e6109e49e6e50b37894cf5e259a6175d5c68cd37cbd3469a778bf86ea1956d997f9500d968cac6aa20f34444b93c313b9139bbeef06c2fd6902ffc913bf0aae2abbefc338babec1022e1bbd8a8df3fccaab3aa17108254c8e6b415d3edcfd9e0738bca4ea3c2749) (LlhgxuCkgvY u86526039109882199526131538780536033377) (cLzfhdGIFWt 'S92XK4FCQJCXK2AES16WVJWP66689MGXKHSTJW6NV.IopLHoUBzNdvRaEnoDjDri) (cT u".[\u{3EBDC}?\u{51CF4}"))
                    (tuple (HUjqhooZkWOxCBP (tuple (FptMqjTJNUNgg "qEM?kK^:^y0hBKdX2KGx4j(2,mJWF5whQ&{9]zq9M?hO`}7-J}7`#&yz(V/mSe{-f)ydt({0w*xhBIHedB+qNd") (aXGLXMMVAwPHl u"\u{10DB3B}|\u{B}<\u{D4}$") (dPliquaWzyA u"u<&\u{5474A}\u{FFFD}\u{37831}"))) (KjI 0x883e5fba16581ffaf0760531bad9760c3bfad38f585ed395bcbd87fea722737a545882d339e212b2473c20ed5df75747af5dc6c285fa7291446f4cd640b11ed0da45a5f65254dc03ceda920eda93a366ed457cb96769826e9dcbe793755b596f918b12e1156c14c6aac8) (LlhgxuCkgvY u54905774066604940256152088345328184940) (cLzfhdGIFWt 'SDFXQR791656BCGQJE2PBM7Z10134852HX2X22HJ) (cT u"5f`\u{468}\u{63CCA}"))
                    (tuple (HUjqhooZkWOxCBP (tuple (FptMqjTJNUNgg "?1b?U*-}@{%{T(Z9/fIcV$KD,\"Es-TrcnS`.HZTYnY[00l& Q*Qk,kio2@x<&N{r3)`6f`.{SKGcBEzd >c[5p") (aXGLXMMVAwPHl u"=\u{4856D}\u{23A}{\u{0}:") (dPliquaWzyA u"\u{468}%\u{E4}\"\u{202E}\u{23A}"))) (KjI 0x65632440e4cb2a9c12821ba9e6c6dca8352f081b8b18e8fd40df33110adf2084c0bb7290e1fd4fd68e0c9de78ed8c1d4fc08879a1b59b17776a4b7109e2cc661c5af67048d1a094c6daff3f467401a13b6d107f963742be1b6ca39d7fb0b0f3824066311120113e2a8e3) (LlhgxuCkgvY u55353300269423966798277265961322403298) (cLzfhdGIFWt 'SW3JYDPJMCDCT5M42TFVXSG07NN1FRY1P16N4DDKW.PsuTiLAbPJiaTjsYRKFfrca) (cT u"{.\u{F04E9}\u{A}k"))
                )
            "#,
        );

        crosscheck(snippet, expected);
    }

    #[test]
    fn map_cannot_oom() {
        let snippet = "
            (define-private (foo (a (list 100 {CgKqvgr: (buff 79),})) (b {CgKqvgr: (buff 79),}))
                (append a b)
            ) 

            (map foo (list (list (tuple (CgKqvgr 0x7d008ba1f4ed1955af2b67c290f7875aac0014b5d271a69e9b3b7c1d569599eb1d44673f4a63bdc33cc903933bf4c08cfd9ed861fe53767db39c6faf6e1c156433295e75bb24bed21180fdfeb8ce9d)) (tuple (CgKqvgr 0x3c494e7db0dfab3592837879dbf942c47a63afc13aab52e84cb26d9598fc7bf5ab0944da410957e2875630a00044821340b25bce91f9d40756db18e559ede1aa8f9b8dae6e7ea5844e3b2c8e0d785f))) (list (tuple (CgKqvgr 0x4baa30e193557d264bf9221b85f1c6bc0785df4af8dac870c8a2f9c67b112a5d7cb747a95f96c828553586e8abf2961a5c8a4e10597e7571b7158d0194de9d561feb634adf6c91887e71dc2a0d978c)) (tuple (CgKqvgr 0xc4cb3cbe486c51fd1214ef7f70b4d9ef5a5db64b67a3809d80c654262d6ce7fdfbc7a0955c5dd424981eda828b40b5840cf628259c24e64c3a43e5817d13bf24976760f3f76f0349601e149ee37511)) (tuple (CgKqvgr 0xd946bad7920fc3edc8f8959bf9a9bc781aebbd4f1fa7b880384e648eb53e4fc5feeaa4d4657184e136d7b785b9884c80c8906e5cf98eaaabec88c3d5f865f245e3a522faef4e60f61910dde9d2a402)) (tuple (CgKqvgr 0x8cdfd327efd7d3ebbb700e15dc16f138b41d4a821144aa097994a8c07e4ecd9fd2e873b0415a65ff8fbd68475a46da8cf75a46335c4719a4e6a6e08e3b6d6b6c731fd23a97d5261486955d47d57482)) (tuple (CgKqvgr 0x86dc880db5bad7366fb951bb036f544b4cea799281879392902c10109307e14fb54af576c5c2f52b7d5bc8fe0d881fee69b1c5ed15f8ae7ac8bc902bf1d8f8d9ab89338f16e00232d94dfc402a1dee)) (tuple (CgKqvgr 0xf0fb280e91628b982e4005df73e4d04dcb4f7cb99da029d46a97ad578dd27fd7d08c7efa112b1ef2933dcb7b42a31d1f8cafa5abe5a34a223796f484488970e766f9ef4d71ca578b0d5b1fa306a61f)) (tuple (CgKqvgr 0x5b361847f6b8be43704ac8872895764f8e03a1cc7df0eb9e0e7f798f2ca050173d7c8bddb194824f7bb986ad0c94877787867ee338234785f9bb0de9feb1fe2562534b9446fa34eda00278baa63862)) (tuple (CgKqvgr 0xb96a708b0bde21ddfc31e472b2af88e457d2c8a205ad5b5380e4ee524d11d4a6381852396a8b1b85392c2160003cc778f38eec653e074d93b3313f6be41617997a8b2687c95f5a699af806386c91e9)) (tuple (CgKqvgr 0xb62dd47e5f5bf920b8fc84e8351df559c3dfdda1daec131c5287e6dcb929459ba474b65d4c5a5c296e5182f2726d68224924ce54bce1cefa1243cdea7cc028fdfc06245d6b4c72a131bfae95f17192)) (tuple (CgKqvgr 0x11565d956bfec3f277b3beaeffd8b70a810052f59eb6f4cf2d4ca8509adb1ebbe786252e5842e194862ce607bdee92947939b49c01bdba7abadc6a6091798e2886e8f0aadc3223646113cf2a4a37b6))) (list (tuple (CgKqvgr 0x53e60ea1ef01c9002a6a9cd2c777482119f36baf31f0fa55f695f0690e7f065c8a32da786f7a2635bee06983773ba9807f712652922014474fd893deafd11612c96557de994cfdb68f8c0c1f721ef1)) (tuple (CgKqvgr 0x247d7c5cf35c73ca5eb5c60ce7c0112013a5e85425904f62d811ea50f513129d561a1ee083b88c39500816471c35fc59e200bf63e4dedae2b1922140398754f0742918f103b95b89bfcf9d626acbb6)) (tuple (CgKqvgr 0x19bed1545914c48f0339573a77ac8d05fac795794ffdbfedadc78d2ceb1e1edd5c372990de641e41510f9cd81695de591cba7a08d80523ba26b1ac79ba1dcac5edd148b64eabea7558da5484a47b8d)) (tuple (CgKqvgr 0x4785456c87b46816fb19a6487ee97bc614abf05ca7d3a5bca66f3bc9c96de1871b3b4185f734effc86a0eafb9f0f665f6ce9b4afe228a1e980b653026b0bdddfdfe6d484da8126e1d19ec6e97e031b)) (tuple (CgKqvgr 0x259152508c6928c6e44a0ca0b75a60ccd8384357ff19221aa448a011c78317cd7eb22179271d7ebdc9dce9f2cbcd0709c54118800d2cf82d6f22228f9352a7bcf424f263ff514cea126baf9a3b3cba)) (tuple (CgKqvgr 0xb2d4ba5183fa85f85cb23a019a911faa95b79645fe763eab6031352f7405111f656871f720916db93ec5afd369a2fa880a91d05283e3ef008981980ec1cb4e8dcc500a4c361267f7a631a579e2243b))) (list (tuple (CgKqvgr 0x80fb00dee5dde4918843d329c8ec257fa29d937642413c20be2012e73d410665f9174c700f39c1c7b9fdc8f741e292c3b09beccc57a1f45c666d2f0690524fad67dc989b5f21ece3bbcb212b671e83)) (tuple (CgKqvgr 0x16c504f9675b02c2da65956d1fd6da1ac711dcba848b3d8ffdbe3ed352476ff59e36ad004dfb12ade328efd793255d654f0cb7102da6c4b0810de8b2b036186f99b97e67054b4a6e85c276b8da28da)))) (list (tuple (CgKqvgr 0x51ababa90b38940b6700791bf48329ee7bea78e9d0b59cc597a35b6681a53ddacb76efbc62fdb00cc50f13b0230494d6d3f91be7f8569831a5d546d485261188b0e1787d8fcb1cfb519c22b7f98577)) (tuple (CgKqvgr 0x3fdf5fc9c52ea0200ed5aea6fa9230c43012b22fc205372a4e101cd01d6ce624af992fa36450f06ccd6452ed16a368c983a2b5c3eddf7d79e863e90fb17c876187904cae374872f8d4b0019e927cc2)) (tuple (CgKqvgr 0x4e76293871093c0cb1182ebf3affbafb8dbb445e7183a97758190116b557f8e63fef3c758752e6e11d0caec4dce3f3abcaeb650558959f120299ccd0a06e17d9444f42bc9f7801bc13941687d84e33)) (tuple (CgKqvgr 0x35a44071d0f6479b2e51d897c8ccdcc331d03a767ecb9d17171830d75ba065229e5ba88bdf299f69290ff17c290d9ab2354122fd7f74d991cb0c19033123991bb453872484b333aa79d59efc4b625a)) (tuple (CgKqvgr 0x1bfaa564fca25d8ab6f6d5b71c01c2485b7286ff0218abcd827a40b14afa5d11ac400a9f742c9e9ac24e7d696fe90f955b1580718673e76bc2389b33b547a85ef39dba5bd6ec12fbf395f8b5759be8)) (tuple (CgKqvgr 0x723997e5a77d3389c2f2bcdad63ebb3f03cb012ae0c8a1e7adf65191a9f424aa7804114c44575221247e2a865bcc4b82e2572bf518078ccef655fbcc7b371ca04b61eb833039a8b88fc680e6cee0fe)) (tuple (CgKqvgr 0x23d80ff91c979ef484bd47b146e9c23e06357baf57c56c59a1603deaaccc89c7ec698219e6f0aa80c0e40400f6850dfc8376b58233b0075562ea532d0769957049d61856f46b0e54fdab3093ae3ab9)) (tuple (CgKqvgr 0xfdab1ac288936663e8c2629035542d49d1fe0dff4225fbfb44c94065a34405cfdf3a1668fa117deb867d53c44d1c975ec6f49ae30e4dc4fa155939f46bc8b026ce1734217b82936456473f997b8456)) (tuple (CgKqvgr 0x939b7f418fcec9c1deb98a1f2304bd039beba615004f4908a3b545da43705dada8bf2e4a88370c7b26ffe81797cbdc33224457c0045cd856c5c68fca0f393d0e53a1d5379450c75f4e4aa9f7b2b7c4)) (tuple (CgKqvgr 0x1e2e203068f653df8fff263c320e3ab02552e25fb37bdbbd716dc16fde00df45c75c50e2b9ecc4e5345e03a5ac05d376a563bb30e187a696393441650e17466a0ce0d7f1968f6fb46b80095602e9d1))))
        ";

        let mut env = crate::tools::TestEnvironment::default();
        let res = env.evaluate(snippet);
        eprintln!("{res:?}");
    }
}
