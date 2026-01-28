use clarity::vm::types::TypeSignature;
use clarity::vm::{ClarityName, SymbolicExpression};

use super::{ComplexWord, Word};
use crate::check_args;
use crate::cost::WordCharge;
use crate::wasm_generator::{
    add_placeholder_for_type, clar2wasm_ty, ArgumentsExt, GeneratorError, WasmGenerator,
};
use crate::wasm_utils::ArgumentCountCheck;

#[derive(Debug)]
pub struct ClaritySome;

impl Word for ClaritySome {
    fn name(&self) -> ClarityName {
        "some".into()
    }
}

impl ComplexWord for ClaritySome {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 1, args.len(), ArgumentCountCheck::Exact);

        self.charge(generator, builder, 0)?;

        let value = args.get_expr(0)?;
        // (some <val>) is represented by an i32 1, followed by the value
        builder.i32_const(1);

        if let TypeSignature::OptionalType(inner_type) = generator
            .get_expr_type(expr)
            .ok_or_else(|| GeneratorError::TypeError("some expression must be typed".to_owned()))?
        {
            // WORKKAROUND: set inner value full type
            generator.set_expr_type(value, *inner_type.clone())?;

            generator.traverse_expr(builder, value)
        } else {
            Err(GeneratorError::TypeError(
                "expected optional type".to_owned(),
            ))
        }
    }
}

#[derive(Debug)]
pub struct ClarityOk;

impl Word for ClarityOk {
    fn name(&self) -> ClarityName {
        "ok".into()
    }
}

impl ComplexWord for ClarityOk {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 1, args.len(), ArgumentCountCheck::Exact);

        self.charge(generator, builder, 0)?;

        let value = args.get_expr(0)?;

        let TypeSignature::ResponseType(inner_types) = generator
            .get_expr_type(expr)
            .ok_or_else(|| GeneratorError::TypeError("ok expression must be typed".to_owned()))?
            .clone()
        else {
            return Err(GeneratorError::TypeError(
                "expected response type".to_owned(),
            ));
        };

        // (ok <val>) is represented by an i32 1, followed by the ok value,
        // followed by a placeholder for the err value
        builder.i32_const(1);

        //WORKAROUND: set full type to ok value
        generator.set_expr_type(value, inner_types.0)?;
        generator.traverse_expr(builder, value)?;

        // deal with err placeholders
        let err_types = clar2wasm_ty(&inner_types.1);
        for err_type in err_types.iter() {
            add_placeholder_for_type(builder, *err_type);
        }

        Ok(())
    }
}

#[derive(Debug)]
pub struct ClarityErr;

impl Word for ClarityErr {
    fn name(&self) -> ClarityName {
        "err".into()
    }
}

impl ComplexWord for ClarityErr {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 1, args.len(), ArgumentCountCheck::Exact);

        self.charge(generator, builder, 0)?;

        let value = args.get_expr(0)?;
        // (err <val>) is represented by an i32 0, followed by a placeholder
        // for the ok value, followed by the err value
        builder.i32_const(0);
        let ty = generator
            .get_expr_type(expr)
            .ok_or_else(|| GeneratorError::TypeError("err expression must be typed".to_owned()))?;
        if let TypeSignature::ResponseType(inner_types) = ty {
            let ok_types = clar2wasm_ty(&inner_types.0);
            for ok_type in ok_types.iter() {
                add_placeholder_for_type(builder, *ok_type);
            }
            // WORKAROUND: set full type to err value
            generator.set_expr_type(value, inner_types.1.clone())?
        } else {
            return Err(GeneratorError::TypeError(
                "expected response type".to_owned(),
            ));
        }
        generator.traverse_expr(builder, value)
    }
}

#[cfg(test)]
mod tests {
    use crate::tools::evaluate;

    #[test]
    fn some_less_than_one_arg() {
        let result = evaluate("(some)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 1 arguments, got 0"));
    }

    #[test]
    fn some_more_than_one_arg() {
        let result = evaluate("(some 1 2)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 1 arguments, got 2"));
    }

    #[test]
    fn ok_less_than_one_arg() {
        let result = evaluate("(ok)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 1 arguments, got 0"));
    }

    #[test]
    fn ok_more_than_one_arg() {
        let result = evaluate("(ok 1 2)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 1 arguments, got 2"));
    }

    #[test]
    fn err_less_than_one_arg() {
        let result = evaluate("(err)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 1 arguments, got 0"));
    }

    #[test]
    fn err_more_than_one_arg() {
        let result = evaluate("(err 1 2)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 1 arguments, got 2"));
    }
}
