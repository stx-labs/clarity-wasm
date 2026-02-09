use std::fmt::Write;

use clar2wasm::tools::crosscheck_multi_contract;
#[cfg(not(any(
    feature = "test-clarity-v1",
    feature = "test-clarity-v2",
    feature = "test-clarity-v3"
)))]
use clarity::util::hash::Sha512Trunc256Sum;
use clarity::vm::types::{ResponseData, TupleData};
use clarity::vm::{ClarityName, Value};
use proptest::prelude::*;

use crate::{prop_signature, type_string, PropValue, TypePrinter};

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn contract_call_accepts_any_args(
        (tys, values)
            in prop::collection::vec(
                prop_signature().prop_ind_flat_map2(|ty| PropValue::from_type(ty.clone())),
                1..=20
            )
            .prop_map(|arg_ty| arg_ty.into_iter().unzip::<_, _, Vec<_>, Vec<_>>())
            .no_shrink(),
        result in PropValue::any().no_shrink()
    ) {
        // first contract
        let first_contract_name = "foo".into();
        let mut function_arguments = String::new();
        for (name, ty) in ('a'..).zip(tys.iter()) {
            write!(function_arguments, "({name} {}) ", type_string(ty)).unwrap();
        }
        let first_snippet = format!(
            r#"
                (define-public (foofun {function_arguments})
                    (ok {result})
                )
            "#
        );

        // second contract
        let second_contract_name = "bar".into();
        let mut call_arguments = String::new();
        for value in values {
            write!(call_arguments, "{value} ").unwrap();
        }
        let second_snippet =
            format!(r#"(contract-call? .{first_contract_name} foofun {call_arguments})"#);

        crosscheck_multi_contract(
            &[
                (first_contract_name, &first_snippet),
                (second_contract_name, &second_snippet),
            ],
            Ok(Some(Value::Response(ResponseData {
                committed: true,
                data: Box::new(result.into()),
            }))),
        );
    }

    #[test]
    fn contract_call_returns_any_value_from_argument(
        (ty, value) in prop_signature().prop_ind_flat_map2(|ty| PropValue::from_type(ty.clone())).no_shrink()
    ) {
        // first contract
        let first_contract_name = "foo".into();
        let first_snippet = format!(
            r#"
                (define-public (foofun (a {}))
                    (ok a)
                )
            "#, type_string(&ty)
        );

        // second contract
        let second_contract_name = "bar".into();
        let second_snippet =
            format!(r#"(contract-call? .{first_contract_name} foofun {value})"#);

        crosscheck_multi_contract(
            &[
                (first_contract_name, &first_snippet),
                (second_contract_name, &second_snippet),
            ],
            Ok(Some(Value::Response(ResponseData {
                committed: true,
                data: Box::new(value.into()),
            }))),
        );
    }

    #[test]
    fn contract_call_can_use_all_arguments(
        (tys, values)
            in prop::collection::vec(
                prop_signature()
                    .prop_ind_flat_map2(|ty| PropValue::from_type(ty.clone())),
                1..=20
            )
            .prop_map(|arg_ty| arg_ty.into_iter().unzip::<_, _, Vec<_>, Vec<_>>())
            .no_shrink(),
    ) {
        let first_contract_name = "foo".into();
        let mut function_arguments = String::new();
        for (name, ty) in ('a'..).zip(tys.iter()) {
            write!(function_arguments, "({name} {}) ", type_string(ty)).unwrap();
        }
        let expected_res = ('a'..)
            .take(tys.len())
            .fold(String::new(), |mut output, arg| {
                write!(output, "{arg}: {arg}, ").unwrap();
                output
            });
        let first_snippet = format!(
            r#"
                (define-public (foofun {function_arguments})
                    (ok {{ {expected_res} }})
                )
            "#
        );

        // second contract
        let second_contract_name = "bar".into();
        let mut call_arguments = String::new();
        for value in values.iter() {
            write!(call_arguments, "{value} ").unwrap();
        }
        let second_snippet =
            format!(r#"(contract-call? .{first_contract_name} foofun {call_arguments})"#);

        let expected = TupleData::from_data(
            ('a'..)
                .map(|c| ClarityName::try_from(c.to_string()).unwrap())
                .zip(values.into_iter().map(Value::from))
                .collect(),
        )
        .unwrap()
        .into();

        crosscheck_multi_contract(
            &[
                (first_contract_name, &first_snippet),
                (second_contract_name, &second_snippet),
            ],
            Ok(Some(Value::Response(ResponseData {
                committed: true,
                data: Box::new(expected),
            }))),
        );
    }
}

#[cfg(any(
    feature = "test-clarity-v1",
    feature = "test-clarity-v2",
    feature = "test-clarity-v3"
))]
proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn as_contract_can_return_any_value(
        value in PropValue::any()
    ) {
        clar2wasm::tools::crosscheck(
            &format!("(as-contract {value})"),
            Ok(Some(value.into()))
        );
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn contract_dynamic_call_accepts_any_args(
        (tys, values)
            in prop::collection::vec(
                prop_signature().prop_ind_flat_map2(|ty| PropValue::from_type(ty.clone())),
                1..=20
            )
            .prop_map(|arg_ty| arg_ty.into_iter().unzip::<_, _, Vec<_>, Vec<_>>())
            .no_shrink(),
        result in PropValue::any().no_shrink(),
        err_type in prop_signature(),
    ) {
        // first contract
        let first_contract_name = "foo".into();
        let mut function_types = String::new();
        let mut function_arguments = String::new();
        for (name, ty) in ('a'..).zip(tys.iter()) {
            let ty = type_string(ty);
            write!(function_arguments, "({name} {ty}) ").unwrap();
            function_types += &(ty + " ");
        }
        let first_snippet = format!(
            r#"
                (define-trait foo-trait (
                    (foofun ({function_types}) (response {} {}))
                ))

                (define-public (foofun {function_arguments})
                    (ok {result})
                )
            "#,
            result.type_string(),
            type_string(&err_type)
        );

        // second contract
        let second_contract_name = "bar".into();

        let contract_call_args: String =
            ('a'..)
                .take(values.len())
                .fold(String::new(), |mut acc, name| {
                    write!(acc, "{name} ").unwrap();
                    acc
                });

        let mut call_arguments = String::new();
        for value in values {
            write!(call_arguments, "{value} ").unwrap();
        }

        let second_snippet = format!(
            r#"
                (use-trait foo-trait .foo.foo-trait)
                (define-private (call-it (tt <foo-trait>) {function_arguments})
                    (contract-call? tt foofun {contract_call_args})
                )
                (call-it .foo {call_arguments})
            "#
        );

        crosscheck_multi_contract(
            &[
                (first_contract_name, &first_snippet),
                (second_contract_name, &second_snippet),
            ],
            Ok(Some(Value::Response(ResponseData {
                committed: true,
                data: Box::new(result.into()),
            }))),
        );
    }

    #[test]
    fn contract_dynamic_call_accepts_any_args_trait_in_let(
        (tys, values)
            in prop::collection::vec(
                prop_signature().prop_ind_flat_map2(|ty| PropValue::from_type(ty.clone())),
                1..=20
            )
            .prop_map(|arg_ty| arg_ty.into_iter().unzip::<_, _, Vec<_>, Vec<_>>())
            .no_shrink(),
        result in PropValue::any().no_shrink(),
        err_type in prop_signature(),
    ) {
        // first contract
        let first_contract_name = "foo".into();
        let mut function_types = String::new();
        let mut function_arguments = String::new();
        for (name, ty) in ('a'..).zip(tys.iter()) {
            let ty = type_string(ty);
            write!(function_arguments, "({name} {ty}) ").unwrap();
            function_types += &(ty + " ");
        }
        let first_snippet = format!(
            r#"
                (define-trait foo-trait (
                    (foofun ({function_types}) (response {} {}))
                ))

                (define-public (foofun {function_arguments})
                    (ok {result})
                )
            "#,
            result.type_string(),
            type_string(&err_type)
        );

        // second contract
        let second_contract_name = "bar".into();

        let contract_call_args: String =
            ('a'..)
                .take(values.len())
                .fold(String::new(), |mut acc, name| {
                    write!(acc, "{name} ").unwrap();
                    acc
                });

        let mut call_arguments = String::new();
        for value in values {
            write!(call_arguments, "{value} ").unwrap();
        }

        let second_snippet = format!(
            r#"
                (use-trait foo-trait .foo.foo-trait)
                (define-private (call-it (tt <foo-trait>) {function_arguments})
                    (let ((ttt tt))
                        (contract-call? ttt foofun {contract_call_args})
                    )
                )
                (call-it .foo {call_arguments})
            "#
        );

        crosscheck_multi_contract(
            &[
                (first_contract_name, &first_snippet),
                (second_contract_name, &second_snippet),
            ],
            Ok(Some(Value::Response(ResponseData {
                committed: true,
                data: Box::new(result.into()),
            }))),
        );
    }

    #[test]
    fn contract_dynamic_call_accepts_any_args_trait_in_match_some(
        (tys, values)
            in prop::collection::vec(
                prop_signature().prop_ind_flat_map2(|ty| PropValue::from_type(ty.clone())),
                1..=20
            )
            .prop_map(|arg_ty| arg_ty.into_iter().unzip::<_, _, Vec<_>, Vec<_>>())
            .no_shrink(),
        result in PropValue::any().no_shrink(),
        (err_type, err_value) in prop_signature().prop_ind_flat_map2(PropValue::from_type).no_shrink(),
    ) {
        // first contract
        let first_contract_name = "foo".into();
        let mut function_types = String::new();
        let mut function_arguments = String::new();
        for (name, ty) in ('a'..).zip(tys.iter()) {
            let ty = type_string(ty);
            write!(function_arguments, "({name} {ty}) ").unwrap();
            function_types += &(ty + " ");
        }
        let first_snippet = format!(
            r#"
                (define-trait foo-trait (
                    (foofun ({function_types}) (response {} {}))
                ))

                (define-public (foofun {function_arguments})
                    (ok {result})
                )
            "#,
            result.type_string(),
            type_string(&err_type)
        );

        // second contract
        let second_contract_name = "bar".into();

        let contract_call_args: String =
            ('a'..)
                .take(values.len())
                .fold(String::new(), |mut acc, name| {
                    write!(acc, "{name} ").unwrap();
                    acc
                });

        let mut call_arguments = String::new();
        for value in values {
            write!(call_arguments, "{value} ").unwrap();
        }

        let second_snippet = format!(
            r#"
                (use-trait foo-trait .foo.foo-trait)
                (define-private (call-it (tt (optional <foo-trait>)) {function_arguments})
                    (match tt
                        ttt (contract-call? ttt foofun {contract_call_args})
                        (err {err_value})
                    )
                )
                (call-it (some .foo) {call_arguments})
            "#
        );

        crosscheck_multi_contract(
            &[
                (first_contract_name, &first_snippet),
                (second_contract_name, &second_snippet),
            ],
            Ok(Some(Value::Response(ResponseData {
                committed: true,
                data: Box::new(result.into()),
            }))),
        );
    }

    #[test]
    fn contract_dynamic_call_accepts_any_args_trait_in_match_ok(
        (tys, values)
            in prop::collection::vec(
                prop_signature().prop_ind_flat_map2(|ty| PropValue::from_type(ty.clone())),
                1..=20
            )
            .prop_map(|arg_ty| arg_ty.into_iter().unzip::<_, _, Vec<_>, Vec<_>>())
            .no_shrink(),
        result in PropValue::any().no_shrink(),
        (err_type, err_value) in prop_signature().prop_ind_flat_map2(PropValue::from_type).no_shrink(),
    ) {
        // first contract
        let first_contract_name = "foo".into();
        let mut function_types = String::new();
        let mut function_arguments = String::new();
        for (name, ty) in ('a'..).zip(tys.iter()) {
            let ty = type_string(ty);
            write!(function_arguments, "({name} {ty}) ").unwrap();
            function_types += &(ty + " ");
        }
        let first_snippet = format!(
            r#"
                (define-trait foo-trait (
                    (foofun ({function_types}) (response {} {}))
                ))

                (define-public (foofun {function_arguments})
                    (ok {result})
                )
            "#,
            result.type_string(),
            type_string(&err_type)
        );

        // second contract
        let second_contract_name = "bar".into();

        let contract_call_args: String =
            ('a'..)
                .take(values.len())
                .fold(String::new(), |mut acc, name| {
                    write!(acc, "{name} ").unwrap();
                    acc
                });

        let mut call_arguments = String::new();
        for value in values {
            write!(call_arguments, "{value} ").unwrap();
        }

        let second_snippet = format!(
            r#"
                (use-trait foo-trait .foo.foo-trait)
                (define-private (call-it (tt (response <foo-trait> uint)) {function_arguments})
                    (match tt
                        ttt (contract-call? ttt foofun {contract_call_args})
                        unused (err {err_value})
                    )
                )
                (call-it (ok .foo) {call_arguments})
            "#
        );

        crosscheck_multi_contract(
            &[
                (first_contract_name, &first_snippet),
                (second_contract_name, &second_snippet),
            ],
            Ok(Some(Value::Response(ResponseData {
                committed: true,
                data: Box::new(result.into()),
            }))),
        );
    }

    #[test]
    fn contract_dynamic_call_accepts_any_args_trait_in_match_err(
        (tys, values)
            in prop::collection::vec(
                prop_signature().prop_ind_flat_map2(|ty| PropValue::from_type(ty.clone())),
                1..=20
            )
            .prop_map(|arg_ty| arg_ty.into_iter().unzip::<_, _, Vec<_>, Vec<_>>())
            .no_shrink(),
        result in PropValue::any().no_shrink(),
        (err_type, err_value) in prop_signature().prop_ind_flat_map2(PropValue::from_type).no_shrink(),
    ) {
        // first contract
        let first_contract_name = "foo".into();
        let mut function_types = String::new();
        let mut function_arguments = String::new();
        for (name, ty) in ('a'..).zip(tys.iter()) {
            let ty = type_string(ty);
            write!(function_arguments, "({name} {ty}) ").unwrap();
            function_types += &(ty + " ");
        }
        let first_snippet = format!(
            r#"
                (define-trait foo-trait (
                    (foofun ({function_types}) (response {} {}))
                ))

                (define-public (foofun {function_arguments})
                    (ok {result})
                )
            "#,
            result.type_string(),
            type_string(&err_type)
        );

        // second contract
        let second_contract_name = "bar".into();

        let contract_call_args: String =
            ('a'..)
                .take(values.len())
                .fold(String::new(), |mut acc, name| {
                    write!(acc, "{name} ").unwrap();
                    acc
                });

        let mut call_arguments = String::new();
        for value in values {
            write!(call_arguments, "{value} ").unwrap();
        }

        let second_snippet = format!(
            r#"
                (use-trait foo-trait .foo.foo-trait)
                (define-private (call-it (tt (response uint <foo-trait>)) {function_arguments})
                    (match tt
                        unused (err {err_value})
                        ttt (contract-call? ttt foofun {contract_call_args})
                    )
                )
                (call-it (err .foo) {call_arguments})
            "#
        );

        crosscheck_multi_contract(
            &[
                (first_contract_name, &first_snippet),
                (second_contract_name, &second_snippet),
            ],
            Ok(Some(Value::Response(ResponseData {
                committed: true,
                data: Box::new(result.into()),
            }))),
        );
    }

    #[test]
    fn contract_dynamic_call_use_all_args(
        (tys, values)
            in prop::collection::vec(
                prop_signature().prop_ind_flat_map2(|ty| PropValue::from_type(ty.clone())),
                1..=20
            )
            .prop_map(|arg_ty| arg_ty.into_iter().unzip::<_, _, Vec<_>, Vec<_>>())
            .no_shrink(),
        err_type in prop_signature(),
    ) {
        // first contract
        let first_contract_name = "foo".into();
        let mut function_types = String::new();
        let mut function_arguments = String::new();
        for (name, ty) in ('a'..).zip(tys.iter()) {
            let ty = type_string(ty);
            write!(function_arguments, "({name} {ty}) ").unwrap();
            function_types += &(ty + " ");
        }
        let expected_res: PropValue = Value::from(
            TupleData::from_data(
                ('a'..)
                    .map(|c| ClarityName::try_from(c.to_string()).unwrap())
                    .zip(values.iter().cloned().map(Value::from))
                    .collect(),
            )
            .unwrap(),
        )
        .into();
        let expected_res_ty = ('a'..).zip(tys.iter()).fold('{'.to_string(), |mut acc, (c, ty)| {
            write!(acc, "{c}: {}, ", type_string(ty)).unwrap();
            acc
        }) + "}";

        let foofun_res = ('a'..).take(values.len()).fold("{".to_owned(), |mut acc, n| {
            write!(acc, "{n}: {n}, ").unwrap();
            acc
        }) + "}";

        let first_snippet = format!(
            r#"
                    (define-trait foo-trait (
                        (foofun ({function_types}) (response {expected_res_ty} {}))
                    ))

                    (define-public (foofun {function_arguments})
                        (ok {foofun_res})
                    )
                "#,
            type_string(&err_type),
        );

        // second contract
        let second_contract_name = "bar".into();

        let contract_call_args: String =
            ('a'..)
                .take(values.len())
                .fold(String::new(), |mut acc, name| {
                    write!(acc, "{name} ").unwrap();
                    acc
                });

        let mut call_arguments = String::new();
        for value in values {
            write!(call_arguments, "{value} ").unwrap();
        }

        let second_snippet = format!(
            r#"
                    (use-trait foo-trait .foo.foo-trait)
                    (define-private (call-it (tt <foo-trait>) {function_arguments})
                        (contract-call? tt foofun {contract_call_args})
                    )
                    (call-it .foo {call_arguments})
                "#
        );

        crosscheck_multi_contract(
            &[
                (first_contract_name, &first_snippet),
                (second_contract_name, &second_snippet),
            ],
            Ok(Some(Value::Response(ResponseData {
                committed: true,
                data: Box::new(expected_res.into()),
            }))),
        );
    }
}

#[cfg(not(any(
    feature = "test-clarity-v1",
    feature = "test-clarity-v2",
    feature = "test-clarity-v3"
)))]
proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn contract_hash_returns_correct_hash_for_any_contract(
        function_defs in prop::collection::vec(
            (
                prop::sample::select(vec!["define-public", "define-read-only", "define-private"]),
                prop::string::string_regex("[a-z][a-z0-9]{0,15}").unwrap(),
                prop::collection::vec(
                    prop_signature(),
                    0..=5
                ),
                PropValue::any()
            ),
            1..=5
        )
        .prop_map(|defs| {
            defs.into_iter().enumerate().map(|(idx, (func_type, name, tys, result))| {
                // Ensure function name is at least 2 characters and doesn't start with "u" followed by digit
                // (which could be confused with uint literals like u0, u1, etc.)
                let func_name = if name.is_empty()
                    || name.len() == 1
                    || (name.starts_with('u') && name.chars().nth(1).is_some_and(|c| c.is_ascii_digit()))
                {
                    format!("func{}", idx)
                } else {
                    name
                };
                (func_type, func_name, tys, result)
            }).collect::<Vec<_>>()
        })
        .no_shrink()
    ) {
        // callee contract - generate random contract structure
        let callee_contract_name = "callee".into();
        let mut callee_snippet = String::new();

        for (func_type, func_name, tys, result) in function_defs.iter() {
            let mut function_arguments = String::new();
            for (name, ty) in ('a'..).zip(tys.iter()) {
                write!(function_arguments, "({name} {}) ", type_string(ty)).unwrap();
            }

            write!(
                callee_snippet,
                "({} ({} {})\n    (ok {}))\n",
                func_type, func_name, function_arguments.trim_end(), result
            ).unwrap();
        }

        // caller contract
        let caller_contract_name = "caller".into();
        let caller_snippet = "(contract-hash? .callee)";

        let expected = Sha512Trunc256Sum::from_data(callee_snippet.as_bytes());

        crosscheck_multi_contract(
            &[
                (callee_contract_name, &callee_snippet),
                (caller_contract_name, caller_snippet),
            ],
            Ok(Some(
                Value::okay(Value::buff_from(expected.0.to_vec()).unwrap()).unwrap(),
            )),
        );
    }
}
