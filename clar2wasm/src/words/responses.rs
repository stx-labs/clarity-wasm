use clarity::vm::types::TypeSignature;
use clarity::vm::{ClarityName, SymbolicExpression};
use walrus::ir::BinaryOp;

use super::{ComplexWord, Word};
use crate::check_args;
use crate::cost::WordCharge;
use crate::wasm_generator::{drop_value, ArgumentsExt, GeneratorError, WasmGenerator};
use crate::wasm_utils::ArgumentCountCheck;

pub fn traverse_response(
    generator: &mut WasmGenerator,
    builder: &mut walrus::InstrSeqBuilder,
    args: &[SymbolicExpression],
) -> Result<(), GeneratorError> {
    let res = args.get_expr(0)?;
    generator.traverse_expr(builder, res)?;
    // there is a response type on top of the stack.

    // Get the type of the response expression
    let ty = generator
        .get_expr_type(res)
        .ok_or_else(|| GeneratorError::TypeError("input expression must be typed".to_owned()))?
        .clone();

    let (ok_ty, err_ty) = if let TypeSignature::ResponseType(types) = &ty {
        &**types
    } else {
        return Err(GeneratorError::TypeError(format!(
            "Expected a Response type. Found {ty:?}"
        )));
    };

    // Drop the err type.
    drop_value(builder, err_ty);

    // Drop the ok type.
    drop_value(builder, ok_ty);

    Ok(())
}

#[derive(Debug)]
pub struct IsOk;

impl Word for IsOk {
    fn name(&self) -> ClarityName {
        "is-ok".into()
    }
}

impl ComplexWord for IsOk {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 1, args.len(), ArgumentCountCheck::Exact);

        self.charge(generator, builder, 0)?;

        traverse_response(generator, builder, args)
    }
}

#[derive(Debug)]
pub struct IsErr;

impl Word for IsErr {
    fn name(&self) -> ClarityName {
        "is-err".into()
    }
}

impl ComplexWord for IsErr {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 1, args.len(), ArgumentCountCheck::Exact);

        self.charge(generator, builder, 0)?;

        traverse_response(generator, builder, args)?;

        // Add one to stack
        // and proceed with a XOR operation
        // to invert the indicator value
        builder.i32_const(1).binop(BinaryOp::I32Xor);

        // Xor'ed indicator is on stack.
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::tools::evaluate;

    #[test]
    fn test_is_ok_no_args() {
        let result = evaluate("(is-ok)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 1 arguments, got 0"));
    }

    #[test]
    fn test_is_ok_more_than_one_arg() {
        let result = evaluate("(is-ok (ok 21) 21)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 1 arguments, got 2"));
    }

    #[test]
    fn test_is_err_no_args() {
        let result = evaluate("(is-err)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 1 arguments, got 0"));
    }

    #[test]
    fn test_is_err_more_than_one_arg() {
        let result = evaluate("(is-err (err 21) 21)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 1 arguments, got 2"));
    }
}
