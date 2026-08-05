use std::fmt::Write;

use clar2wasm::tools::{as_oom_check_snippet, crosscheck_multi_contract, TestConfig};
use clar2wasm::wasm_utils::signature_from_string;
#[cfg(not(any(
    feature = "test-clarity-v1",
    feature = "test-clarity-v2",
    feature = "test-clarity-v3"
)))]
use clarity::util::hash::Sha512Trunc256Sum;
use clarity::vm::types::{ResponseData, TupleData};
use clarity::vm::{ClarityName, ContractName, Value};
use proptest::prelude::*;

use crate::{prop_signature, type_string, PropValue, TypePrinter};

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    #[ignore]
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
        let first_contract_name = ContractName::from_literal("foo");
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
        let second_contract_name = ContractName::from_literal("bar");
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
    #[ignore]
    fn contract_call_returns_any_value_from_argument(
        (ty, value) in prop_signature().prop_ind_flat_map2(|ty| PropValue::from_type(ty.clone())).no_shrink()
    ) {
        // first contract
        let first_contract_name = ContractName::from_literal("foo");
        let first_snippet = format!(
            r#"
                (define-public (foofun (a {}))
                    (ok a)
                )
            "#, type_string(&ty)
        );

        // second contract
        let second_contract_name = ContractName::from_literal("bar");
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
    #[ignore]
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
        let first_contract_name = ContractName::from_literal("foo");
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
        let second_contract_name = ContractName::from_literal("bar");
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
        let first_contract_name = ContractName::from_literal("foo");
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
        let second_contract_name = ContractName::from_literal("bar");

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
    #[ignore]
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
        let first_contract_name = ContractName::from_literal("foo");
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
        let second_contract_name = ContractName::from_literal("bar");

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
    #[ignore]
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
        let first_contract_name = ContractName::from_literal("foo");
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
        let second_contract_name = ContractName::from_literal("bar");

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
    #[ignore]
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
        let first_contract_name = ContractName::from_literal("foo");
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
        let second_contract_name = ContractName::from_literal("bar");

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
    #[ignore]
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
        let first_contract_name = ContractName::from_literal("foo");
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
        let second_contract_name = ContractName::from_literal("bar");

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
        let first_contract_name = ContractName::from_literal("foo");
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
        let second_contract_name = ContractName::from_literal("bar");

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
        let callee_contract_name = ContractName::from_literal("callee");
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
        let caller_contract_name = ContractName::from_literal("caller");
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

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    #[ignore]
    fn contract_call_no_oom_one_arg(
        (ty, val) in prop_signature().prop_ind_flat_map2(PropValue::from_type)
    ) {
        let version = TestConfig::clarity_version();
        let epoch = TestConfig::latest_epoch();

        let ty_string = type_string(&ty);
        let full_ty = signature_from_string(
            &ty_string,
            version,
            epoch,
        )
        .unwrap();

        let callee = as_oom_check_snippet(
            &format!(
                r#"
                    (define-public (foo (arg {ty_string}))
                        (ok arg)
                    )
                "#
            ),
            &[full_ty],
            epoch,
            version,
        );

        let caller = format!("(contract-call? .callee foo {val})");

        let expected = Value::okay(val.into()).unwrap();

        crosscheck_multi_contract(
            &[(ContractName::from_literal("callee"), &callee), (ContractName::from_literal("caller"), &caller)],
            Ok(Some(expected)),
        );
    }

   #[test]
   #[ignore]
    fn contract_call_no_oom_many_arg(
        (types, values) in
            prop::collection::vec(
                prop_signature().prop_ind_flat_map2(PropValue::from_type),
                1..10,
            )
            .prop_map(|s| -> (Vec<_>, Vec<_>) { s.into_iter().unzip() } )
            .no_shrink()
    ) {
        let version = TestConfig::clarity_version();
        let epoch = TestConfig::latest_epoch();

        let types_strings: Vec<_> = types.iter().map(type_string).collect();
        let full_types: Vec<_> = types_strings
            .iter()
            .map(|s| signature_from_string(s, version, epoch).unwrap())
            .collect();

        let args: String = ('a'..='z')
            .zip(types_strings)
            .map(|(name, ty)| format!("({name} {ty}) "))
            .collect();
        let returns = ('a'..='z')
            .take(types.len())
            .fold("{".to_owned(), |mut acc, c| {
                acc.push_str(&format!("{c}: {c}, "));
                acc
            })
            + "}";

        let callee = as_oom_check_snippet(
            &format!(
                r#"
                    (define-public (foo {args})
                        (ok {returns})
                    )
                "#
            ),
            &full_types,
            epoch,
            version,
        );

        let caller = values
            .iter()
            .fold("(contract-call? .callee foo".to_owned(), |mut acc, v| {
                acc.push(' ');
                acc.push_str(&v.to_string());
                acc
            })
            + ")";

        let expected = Value::okay(
            TupleData::from_data(
                ('a'..='z')
                    .zip(values)
                    .map(|(name, val)| (name.to_string().try_into().unwrap(), val.into()))
                    .collect(),
            )
            .unwrap()
            .into(),
        )
        .unwrap();

        crosscheck_multi_contract(
            &[(ContractName::from_literal("callee"), &callee), (ContractName::from_literal("caller"), &caller)],
            Ok(Some(expected)),
        );
    }
}

#[cfg(any(
    feature = "test-clarity-v2",
    feature = "test-clarity-v3",
    feature = "test-clarity-v4"
))]
#[test]
fn contract_call_constant_pre_34_fails() {
    use clarity::vm::errors::{VmExecutionError, WasmError};

    let callee = r#"(define-public (foo) (ok u42))"#;
    let caller = r#"
            (define-constant cst .callee)
            (contract-call? cst foo)
        "#;
    let mut env = clar2wasm::tools::TestEnvironment::new(
        clarity::types::StacksEpochId::Epoch33,
        TestConfig::clarity_version(),
    );
    std::assert_matches!(
        [
            (ContractName::from_literal("callee"), callee),
            (ContractName::from_literal("caller"), caller),
        ]
        .iter()
        .map(|(name, snippet)| env.init_contract_with_snippet(name, snippet))
        .collect::<Vec<_>>()
        .last()
        .unwrap()
        .as_ref()
        .unwrap_err(),
        VmExecutionError::Wasm(WasmError::WasmGeneratorError(_))
    );
}

#[cfg(any(
    feature = "test-clarity-v2",
    feature = "test-clarity-v3",
    feature = "test-clarity-v4"
))]
#[test]
fn contract_call_constant_of_constant_pre_34_fails() {
    use clarity::vm::errors::{VmExecutionError, WasmError};

    let callee = r#"(define-public (foo) (ok u42))"#;
    let caller = r#"
            (define-constant cst1 .callee)
            (define-constant cst2 cst1)
            (contract-call? cst2 foo)
        "#;

    let mut env = clar2wasm::tools::TestEnvironment::new(
        clarity::types::StacksEpochId::Epoch33,
        TestConfig::clarity_version(),
    );
    std::assert_matches!(
        [
            (ContractName::from_literal("callee"), callee),
            (ContractName::from_literal("caller"), caller),
        ]
        .iter()
        .map(|(name, snippet)| env.init_contract_with_snippet(name, snippet))
        .collect::<Vec<_>>()
        .last()
        .unwrap()
        .as_ref()
        .unwrap_err(),
        VmExecutionError::Wasm(WasmError::WasmGeneratorError(_))
    );
}

#[cfg(not(feature = "test-clarity-v1"))]
#[test]
fn contract_call_constant_post_34_succeeds() {
    let callee = r#"(define-public (foo) (ok u42))"#;
    let caller = r#"
            (define-constant cst .callee)
            (contract-call? cst foo)
        "#;

    crosscheck_multi_contract(
        &[
            (ContractName::from_literal("callee"), callee),
            (ContractName::from_literal("caller"), caller),
        ],
        Ok(Some(Value::okay(Value::UInt(42)).unwrap())),
    );
}

#[cfg(not(feature = "test-clarity-v1",))]
#[test]
fn contract_call_constant_of_constant_post_34_succeeds() {
    let callee = r#"(define-public (foo) (ok u42))"#;
    let caller = r#"
            (define-constant cst1 .callee)
            (define-constant cst2 cst1)
            (contract-call? cst2 foo)
        "#;

    crosscheck_multi_contract(
        &[
            (ContractName::from_literal("callee"), callee),
            (ContractName::from_literal("caller"), caller),
        ],
        Ok(Some(Value::okay(Value::UInt(42)).unwrap())),
    );
}
