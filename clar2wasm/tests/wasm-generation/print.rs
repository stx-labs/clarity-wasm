use clar2wasm::tools::{crosscheck, crosscheck_multi_contract};
use clarity::vm::Value;
use clarity_types::ContractName;
use proptest::prelude::{Just, Strategy};
use proptest::proptest;

use crate::{prop_signature, type_string, PropValue};

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn print_any(val in PropValue::any()) {
        crosscheck(
            &format!("(print {val})"),
            Ok(Some(val.into()))
        );
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    #[ignore]
   fn print_val_from_function_call(
        (ty, val) in prop_signature().prop_flat_map(|ty| {
            (Just(ty.clone()), PropValue::from_type(ty))
        })
    ) {
        let ty_str = type_string(&ty);

        let callee = ContractName::from_literal("callee");
        let callee_snippet = format!(
            r#"(define-read-only (print-param (par {ty_str}))
                (print par))"#
        );

        let caller = ContractName::from_literal("caller");
        let caller_snippet = format!(r#"(contract-call? .{callee} print-param {val})"#);

        let expected = Some(Value::from(val.clone()));

        crosscheck_multi_contract(
            &[
                (callee, &callee_snippet),
                (caller, &caller_snippet),
            ],
            Ok(expected),
        );
    }
}
