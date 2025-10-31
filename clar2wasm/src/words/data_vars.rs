use clarity::vm::types::{TypeSignature, TypeSignatureExt};
use clarity::vm::{ClarityName, SymbolicExpression};
use walrus::ValType;

use super::{ComplexWord, Word};
use crate::check_args;
use crate::cost::WordCharge;
use crate::wasm_generator::{ArgumentsExt, GeneratorError, LiteralMemoryEntry, WasmGenerator};
use crate::wasm_utils::{check_argument_count, ArgumentCountCheck};

#[derive(Debug)]
pub struct DefineDataVar;

impl Word for DefineDataVar {
    fn name(&self) -> ClarityName {
        "define-data-var".into()
    }
}

impl ComplexWord for DefineDataVar {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 3, args.len(), ArgumentCountCheck::Exact);

        let name = args.get_name(0)?;
        // Making sure if name is not reserved
        if generator.is_reserved_name(name) {
            return Err(GeneratorError::InternalError(format!(
                "Name already used {name:?}"
            )));
        }

        let data_type = args.get_expr(1)?;
        let ty =
            TypeSignature::parse_type_repr(generator.contract_analysis.epoch, data_type, &mut ())
                .map_err(|e| GeneratorError::TypeError(e.to_string()))?;

        let initial = args.get_expr(2)?;
        generator.set_expr_type(initial, ty.clone())?;

        // Store the identifier as a string literal in the memory
        let (name_offset, name_length) = generator.add_string_literal(name)?;

        // Traverse the initial value for the data variable (result is on the
        // data stack)
        generator.traverse_expr(builder, initial)?;

        // The initial value can be placed on the top of the memory, since at
        // the top-level, we have not set up the call stack yet.
        let offset = generator.module.locals.add(ValType::I32);
        builder
            .i32_const(generator.literal_memory_end as i32)
            .local_set(offset);

        // Write the initial value to the memory, to be read by the host.
        let size = generator.write_to_memory(builder, offset, 0, &ty)?;

        // Increment the literal memory end
        // FIXME: These initial values do not need to be saved in the literal
        //        memory forever... we just need them once, when .top-level
        //        is called.
        generator.literal_memory_end += size;

        // Push the name onto the data stack
        builder
            .i32_const(name_offset as i32)
            .i32_const(name_length as i32);

        // Push the offset onto the data stack
        builder.local_get(offset);

        // Push the size onto the data stack
        builder.i32_const(size as i32);

        // Call the host interface function, `define_variable`
        builder.call(
            generator
                .module
                .funcs
                .by_name("stdlib.define_variable")
                .ok_or_else(|| {
                    GeneratorError::InternalError("stdlib.define_variable not found".to_owned())
                })?,
        );

        // Add type to the datavars_types (for var-set workaround)
        if generator.datavars_types.insert(name.clone(), ty).is_some() {
            return Err(GeneratorError::InternalError(format!(
                "Data var defined twice: {name}"
            )));
        }

        Ok(())
    }
}

#[derive(Debug)]
pub struct SetDataVar;

impl Word for SetDataVar {
    fn name(&self) -> ClarityName {
        "var-set".into()
    }
}

impl ComplexWord for SetDataVar {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 2, args.len(), ArgumentCountCheck::Exact);

        let name = args.get_name(0)?;
        let value = args.get_expr(1)?;

        // WORKAROUND: need to set the correct type of the data var to the argument.
        let ty = generator
            .datavars_types
            .get(name)
            .ok_or_else(|| {
                GeneratorError::InternalError(
                    "Data var should have been defined with a type before var-set".to_owned(),
                )
            })?
            .clone();
        generator.set_expr_type(value, ty.clone())?;

        generator.traverse_expr(builder, value)?;

        // Get the offset and length for this identifier in the literal memory
        let id_offset = *generator
            .literal_memory_offset
            .get(&LiteralMemoryEntry::Ascii(name.as_str().into()))
            .ok_or_else(|| GeneratorError::InternalError(format!("variable not found: {name}")))?;
        let id_length = name.len();

        // Create space on the call stack to write the value
        let (offset, size) = generator.create_call_stack_local(builder, &ty, true, false);

        self.charge(generator, builder, size as u32)?;

        // Write the value to the memory, to be read by the host
        generator.write_to_memory(builder, offset, 0, &ty)?;

        // Push the identifier offset and length onto the data stack
        builder
            .i32_const(id_offset as i32)
            .i32_const(id_length as i32);

        // Push the offset and size to the data stack
        builder.local_get(offset).i32_const(size);

        // Call the host interface function, `set_variable`
        builder.call(
            generator
                .module
                .funcs
                .by_name("stdlib.set_variable")
                .ok_or_else(|| {
                    GeneratorError::InternalError("stdlib.set_variable not found".to_owned())
                })?,
        );

        // `var-set` always returns `true`
        builder.i32_const(1);

        Ok(())
    }
}

#[derive(Debug)]
pub struct GetDataVar;

impl Word for GetDataVar {
    fn name(&self) -> ClarityName {
        "var-get".into()
    }
}

impl ComplexWord for GetDataVar {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 1, args.len(), ArgumentCountCheck::Exact);

        let name = args.get_name(0)?;

        // Get the offset and length for this identifier in the literal memory
        let id_offset = *generator
            .literal_memory_offset
            .get(&LiteralMemoryEntry::Ascii(name.as_str().into()))
            .ok_or_else(|| GeneratorError::TypeError(format!("variable not found: {name}")))?;
        let id_length = name.len();

        // Create a new local to hold the result on the call stack
        let ty = generator
            .get_expr_type(expr)
            .ok_or_else(|| {
                GeneratorError::TypeError("var-get expression must be typed".to_owned())
            })?
            .clone();
        let (offset, size) = generator.create_call_stack_local(builder, &ty, true, true);

        self.charge(generator, builder, size as u32)?;

        // Push the identifier offset and length onto the data stack
        builder
            .i32_const(id_offset as i32)
            .i32_const(id_length as i32);

        // Push the offset and size to the data stack
        builder.local_get(offset).i32_const(size);

        // Call the host interface function, `get_variable`
        builder.call(
            generator
                .module
                .funcs
                .by_name("stdlib.get_variable")
                .ok_or_else(|| {
                    GeneratorError::InternalError("stdlib.get_variable not found".to_owned())
                })?,
        );

        // Host interface fills the result into the specified memory. Read it
        // back out, and place the value on the data stack.
        generator.read_from_memory(builder, offset, 0, &ty)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use clarity::vm::errors::{CheckErrors, Error};
    use clarity::vm::Value;

    use crate::tools::{
        crosscheck, crosscheck_expect_failure, crosscheck_with_clarity_version, evaluate,
    };

    //
    // Module with tests that should only be executed
    // when running Clarity::V1.
    //
    #[cfg(feature = "test-clarity-v1")]
    mod clarity_v1 {
        use clarity::types::StacksEpochId;

        use crate::tools::crosscheck_with_epoch;

        #[test]
        fn validate_define_data_var_epoch() {
            crosscheck_with_epoch(
                "(define-data-var index-of? int 0)",
                Ok(None),
                StacksEpochId::Epoch20,
            );
        }
    }

    #[test]
    fn define_data_var_less_than_three_args() {
        let result = evaluate("(define-data-var something int)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 3 arguments, got 2"));
    }

    #[test]
    fn define_data_var_more_than_three_args() {
        let result = evaluate("(define-data-var something int 0 0)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 3 arguments, got 4"));
    }

    #[test]
    fn var_set_less_than_two_args() {
        let result = evaluate("(define-data-var something int 1)(var-set something)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting >= 2 arguments, got 1"));
    }

    #[test]
    fn var_set_more_than_two_args() {
        // TODO: see issue #488
        // The inconsistency in function arguments should have been caught by the typechecker.
        // The runtime error below is being used as a workaround for a typechecker issue
        // where certain errors are not properly handled.
        // This test should be re-worked once the typechecker is fixed
        // and can correctly detect all argument inconsistencies.
        let snippet = "(define-data-var something int 1) (var-set something 1 2)";
        let expected = Err(Error::Unchecked(CheckErrors::IncorrectArgumentCount(2, 3)));
        crosscheck(snippet, expected);
    }

    #[test]
    fn var_get_less_than_one_arg() {
        let result = evaluate("(var-get)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 1 arguments, got 0"));
    }

    #[test]
    fn var_get_more_than_one_arg() {
        let result = evaluate("(define-data-var something int 1)(var-get something 1)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 1 arguments, got 2"));
    }

    #[test]
    fn test_var_get() {
        crosscheck(
            "
(define-data-var something int 123)

(define-public (simple)
    (ok (var-get something)))

(simple)
",
            evaluate("(ok 123)"),
        );
    }

    #[test]
    fn test_var_set() {
        crosscheck(
            "
(define-data-var something int 123)

(define-public (simple)
  (begin
    (var-set something 5368002525449479521366)
    (ok (var-get something))))

(simple)
",
            evaluate("(ok 5368002525449479521366)"),
        );
    }

    #[test]
    fn validate_define_data_var() {
        // Reserved keyword
        crosscheck_expect_failure("(define-data-var map int 0)");

        // Custom variable name
        crosscheck("(define-data-var a int 0)", Ok(None));

        // Custom variable name duplicate
        crosscheck_expect_failure("(define-data-var a int 0) (define-data-var a int 0)");
    }

    #[test]
    fn define_data_var_has_correct_type_with_clarity1() {
        // https://github.com/stacks-network/clarity-wasm/issues/497
        let snippet = "
            (define-data-var v (optional uint) none)
            (var-set v (some u171713071701372222108711587))
            (var-get v)
        ";

        crosscheck_with_clarity_version(
            snippet,
            Ok(Value::some(Value::UInt(171713071701372222108711587)).ok()),
            clarity::vm::ClarityVersion::Clarity1,
        );
    }
}
