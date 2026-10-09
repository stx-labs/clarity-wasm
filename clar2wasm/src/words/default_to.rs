use clarity::vm::types::TypeSignature;
use clarity::vm::{ClarityName, SymbolicExpression};
use walrus::ir::InstrSeqType;

use super::{ComplexWord, Word};
use crate::check_args;
use crate::cost::WordCharge;
use crate::wasm_generator::{
    clar2wasm_ty, drop_value, ArgumentsExt, GeneratorError, WasmGenerator,
};
use crate::wasm_utils::ArgumentCountCheck;

#[derive(Debug)]
pub struct DefaultTo;

impl Word for DefaultTo {
    fn name(&self) -> ClarityName {
        ClarityName::from_literal("default-to")
    }
}

impl ComplexWord for DefaultTo {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 2, args.len(), ArgumentCountCheck::Exact);

        self.charge(generator, builder, 0)?;

        // There are a `default` value and an `optional` arguments.
        // (default-to 767 (some 1))
        // i64              i64               i32        i64           i64
        // default-val-low, default-val-high, indicator, plc-val-low, plc-val-high
        let default = args.get_expr(0)?;
        let optional = args.get_expr(1)?;

        // WORKAROUND:
        //  - the default type should be the same as the expression
        //  - the optional type should be the same type as the expression, wrapped
        // in a optional.
        // We explicitly set them to avoid representation bugs.
        let Some(expr_type) = generator.get_expr_type(expr).cloned() else {
            return Err(GeneratorError::TypeError(
                "default-to expression should be typed".to_owned(),
            ));
        };
        generator.set_expr_type(default, expr_type.clone())?;
        generator.set_expr_type(optional, TypeSignature::OptionalType(Box::new(expr_type)))?;

        generator.traverse_args(builder, args)?;

        // Default value type
        let default_ty = generator
            .get_expr_type(default)
            .ok_or_else(|| {
                GeneratorError::TypeError("default expression must be typed".to_owned())
            })?
            .clone();

        // Optional value type
        let opt_ty = generator
            .get_expr_type(optional)
            .ok_or_else(|| {
                GeneratorError::TypeError("optional expression must be typed".to_owned())
            })?
            .clone();
        // Optional value
        let opt_val_ty = if let TypeSignature::OptionalType(opt_type) = &opt_ty {
            &**opt_type
        } else {
            return Err(GeneratorError::TypeError(format!(
                "Expected an Optional type. Found {opt_ty:?}"
            )));
        };
        // Save Optional value to locals
        let opt_val_locals = generator.save_to_locals(builder, opt_val_ty, true);

        // Params and result types for the if_else branch
        let out_types = clar2wasm_ty(&default_ty);

        builder.if_else(
            InstrSeqType::new(&mut generator.module.types, &out_types, &out_types),
            |then| {
                drop_value(then, &default_ty);

                for opt_val_local in opt_val_locals {
                    then.local_get(opt_val_local);
                }
            },
            |_| {},
        );

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::tools::evaluate;

    #[test]
    fn default_to_less_than_two_args() {
        let result = evaluate("(default-to 0)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 1"));
    }

    #[test]
    fn default_to_more_than_two_args() {
        let result = evaluate("(default-to 0 1 2)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 3"));
    }
}
