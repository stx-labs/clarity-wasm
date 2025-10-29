use std::fmt::Write;

use clar2wasm::tools::{crosscheck, crosscheck_multi_contract, TestEnvironment};
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

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn as_contract_can_return_any_value(
        value in PropValue::any()
    ) {
        crosscheck(
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

    #[test]
    fn contract_call_with_hashing_works_proptest(buffer_size in 1usize..100000usize) {
        let large_buff = format!("0x{}", "aa".repeat(buffer_size));
        println!("buffer_size: {}", buffer_size);

        let hasher_contract = format!(
            r#"
(define-public (hash-large-buffer (input (buff {})))
    (ok (sha256 input))
)
        "#, large_buff.len());

        // First interpret the contracts to get the expected result
        let mut env = TestEnvironment::default();
        env.init_contract_with_snippet("hasher", hasher_contract.as_str())
            .expect("Failed to init hasher contract");
        let expected = env
            .interpret(&format!("(contract-call? .hasher hash-large-buffer {})", large_buff))
            .expect("Failed to interpret contract call");
        let caller_contract = format!("(contract-call? .hasher hash-large-buffer {})", large_buff);
        let contracts = [
            ("hasher".into(), hasher_contract.as_str()),

            (
                "caller".into(),
                caller_contract.as_str()
            ),
        ];

        // Compare compiled version with interpreted version
        crosscheck_multi_contract(&contracts, Ok(expected));
    }
}
