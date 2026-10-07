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
        // We explicitly set them to avoid representation bugs, keeping their hidden tuple fields.
        let Some(expr_type) = generator.get_expr_type(expr).cloned() else {
            return Err(GeneratorError::TypeError(
                "default-to expression should be typed".to_owned(),
            ));
        };
        let opt_ty = TypeSignature::OptionalType(Box::new(expr_type.clone()));

        generator.traverse_expr_as(builder, default, &expr_type)?;
        generator.traverse_expr_as(builder, optional, &opt_ty)?;

        // Save Optional value to locals
        let opt_val_locals = generator.save_to_locals(builder, &expr_type, true);

        // Params and result types for the if_else branch
        let out_types = clar2wasm_ty(&expr_type);

        builder.if_else(
            InstrSeqType::new(&mut generator.module.types, &out_types, &out_types),
            |then| {
                drop_value(then, &expr_type);

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
    use clarity::vm::Value;

    use crate::tools::{crosscheck, evaluate};

    #[test]
    fn default_to_with_hidden_tuple_field_in_value() {
        let snippet = r#"
            (define-map blacklist principal { soft: bool, full: bool })
            (map-set blacklist tx-sender { soft: true, full: false })
            (get soft (default-to { soft: false } (map-get? blacklist tx-sender)))
        "#;

        crosscheck(snippet, Ok(Some(Value::Bool(true))));
    }

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
