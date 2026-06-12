use clarity::vm::types::TypeSignature;
use clarity::vm::{ClarityName, SymbolicExpression};
use walrus::ir::BinaryOp;

use super::{ComplexWord, Word};
use crate::check_args;
use crate::cost::WordCharge;
use crate::wasm_generator::{drop_value, ArgumentsExt, GeneratorError, WasmGenerator};
use crate::wasm_utils::ArgumentCountCheck;

pub fn traverse_optional(
    generator: &mut WasmGenerator,
    builder: &mut walrus::InstrSeqBuilder,
    args: &[SymbolicExpression],
) -> Result<(), GeneratorError> {
    let opt = args.get_expr(0)?;
    generator.traverse_expr(builder, opt)?;
    // there is an optional type on top of the stack.

    // Get the type of the optional expression
    let ty = generator
        .get_expr_type(opt)
        .ok_or_else(|| GeneratorError::TypeError("input expression must be typed".to_owned()))?
        .clone();

    let some_ty = if let TypeSignature::OptionalType(some_type) = &ty {
        &**some_type
    } else {
        return Err(GeneratorError::TypeError(format!(
            "Expected an Optional type. Found {ty:?}"
        )));
    };

    // Drop the some type.
    drop_value(builder, some_ty);

    Ok(())
}

#[derive(Debug)]
pub struct IsSome;

impl Word for IsSome {
    fn name(&self) -> ClarityName {
        ClarityName::from_literal("is-some")
    }
}

impl ComplexWord for IsSome {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 1, args.len(), ArgumentCountCheck::Exact);

        self.charge(generator, builder, 0)?;

        traverse_optional(generator, builder, args)
    }
}

#[derive(Debug)]
pub struct IsNone;

impl Word for IsNone {
    fn name(&self) -> ClarityName {
        ClarityName::from_literal("is-none")
    }
}

impl ComplexWord for IsNone {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 1, args.len(), ArgumentCountCheck::Exact);

        self.charge(generator, builder, 0)?;

        traverse_optional(generator, builder, args)?;

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
    fn test_is_some_no_args() {
        let result = evaluate("(is-some)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 1 arguments, got 0"));
    }

    #[test]
    fn test_is_some_more_than_one_arg() {
        let result = evaluate("(is-some x y)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 1 arguments, got 2"));
    }

    #[test]
    fn test_is_none_no_args() {
        let result = evaluate("(is-none)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 1 arguments, got 0"));
    }

    #[test]
    fn test_is_none_more_than_one_arg() {
        let result = evaluate("(is-none x y)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 1 arguments, got 2"));
    }
}
