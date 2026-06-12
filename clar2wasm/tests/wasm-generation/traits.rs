use std::fmt::Write;

use clar2wasm::tools::crosscheck_multi_contract;
use clarity::vm::types::TypeSignature;
use clarity_types::ContractName;
use proptest::prelude::*;

use crate::{prop_signature, type_string, PropValue};

#[derive(Debug)]
struct TraitMethod {
    name: String,
    args: Vec<TypeSignature>,
    returns_ty: TypeSignature,
    returns_val: PropValue,
}

prop_compose! {
    fn trait_method() (
        name in "[a-zA-Z]{2}([a-zA-Z0-9]|[-_!?+<>=/*]){20,115}",
        args in prop::collection::vec(
                prop_signature(),
                0..=20
            ),
        (returns_ty, returns_val) in (prop_signature(), prop_signature()).prop_flat_map(|(ok_ty, err_ty)| {
            let res_ty = TypeSignature::ResponseType(Box::new((ok_ty, err_ty)));
            (Just(res_ty.clone()), PropValue::from_type(res_ty))
        })
    ) -> TraitMethod {
        TraitMethod { name, args, returns_ty, returns_val }
    }
}

impl TraitMethod {
    fn method_signature(&self) -> String {
        let args = self
            .args
            .split_first()
            .map_or_else(String::new, |(fst, rest)| {
                rest.iter().fold(type_string(fst), |mut acc, arg| {
                    write!(acc, " {}", type_string(arg)).unwrap();
                    acc
                })
            });
        format!(
            "({} ({}) {})",
            self.name,
            args,
            type_string(&self.returns_ty)
        )
    }

    fn method_implementation(&self) -> String {
        let args = self
            .args
            .split_first()
            .map_or_else(String::new, |(fst, rest)| {
                rest.iter().zip('b'..).fold(
                    format!("(a {})", type_string(fst)),
                    |mut acc, (arg, n)| {
                        write!(acc, " ({n} {})", type_string(arg)).unwrap();
                        acc
                    },
                )
            });
        format!(
            "(define-public ({} {})\n\t{}\n)",
            self.name, args, self.returns_val,
        )
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn define_and_impl_trait(
        trait_name in "impl-trait-[a-z]{1,5}",
        methods in prop::collection::vec(trait_method(), 1..20),
    ) {
        let first_contract_name = ContractName::from_literal("foo");
        let first_snippet =
            methods
                .iter()
                .fold(format!("(define-trait {trait_name} ("), |mut acc, meth| {
                    write!(acc, "\n\t{}", meth.method_signature()).unwrap();
                    acc
                })
                + "\n))";

        let second_contract_name = ContractName::from_literal("bar");
        let second_snippet = methods.iter().fold(
            format!("(impl-trait .{first_contract_name}.{trait_name})\n"),
            |mut acc, meth| {
                writeln!(acc, "{}", meth.method_implementation()).unwrap();
                acc
            },
        );

        crosscheck_multi_contract(
            &[
                (first_contract_name, &first_snippet),
                (second_contract_name, &second_snippet),
            ],
            Ok(None),
        )
    }
}
