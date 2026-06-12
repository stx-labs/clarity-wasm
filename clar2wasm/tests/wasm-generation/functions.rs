use clar2wasm::tools::crosscheck;
use clarity::vm::types::{ResponseData, TupleData, TypeSignature};
use clarity::vm::{ClarityName, Value};
use proptest::prelude::*;
use proptest::proptest;
use proptest::strategy::Strategy;

use crate::{prop_signature, response, type_string, PropValue};

fn strategies_for_function_signature() -> impl Strategy<Value = (Vec<TypeSignature>, Vec<PropValue>)>
{
    prop::collection::vec(
        prop_signature().prop_ind_flat_map2(|ty| PropValue::from_type(ty.clone())),
        1..=20,
    )
    .prop_map(|arg_ty| arg_ty.into_iter().unzip::<_, _, Vec<_>, Vec<_>>())
    .no_shrink()
}

fn strategies_for_response() -> impl Strategy<Value = PropValue> {
    (prop_signature(), prop_signature())
        .prop_flat_map(|(ok, err)| response(ok, err))
        .prop_map(PropValue::from)
        .no_shrink()
}

/// Given a list of type signatures, join them together with some generated arguments names
/// and return both the formatted signature `(arg-0 type-0) ...` and the list of
/// generated arguments names
fn format_args_signature(tys: &Vec<TypeSignature>) -> (String, Vec<String>) {
    let args: Vec<String> = (0..tys.len()).map(|i| format!("arg-{i}")).collect();
    let sig = args
        .iter()
        .zip(tys)
        .map(|(arg, ty)| format!("({arg} {})", type_string(ty)))
        .collect::<Vec<_>>()
        .join(" ");
    (sig, args)
}

fn join_stringified(values: &[PropValue]) -> String {
    values
        .iter()
        .map(|v| v.to_string())
        .collect::<Vec<_>>()
        .join(" ")
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn crossprop_define_private_accepts_any_args(
        (tys, values) in strategies_for_function_signature(),
        result in PropValue::any().no_shrink()
    ) {
        let (args_signature, _) = format_args_signature(&tys);
        let call_args = join_stringified(&values);
        crosscheck(
            &format!(
                r#"
                    (define-private (some-fn {args_signature})
                        {result}
                    )
                    (some-fn {call_args})
                "#,
            ),
            Ok(Some(result.into())),
        )
    }

    #[test]
    fn crossprop_define_private_returns_any_argument(
        ((tys, values), return_index) in strategies_for_function_signature().prop_ind_flat_map2(|(tys, _)| 0..tys.len()),
    ) {
        let (args_signature, args_name) = format_args_signature(&tys);
        let call_args = join_stringified(&values);
        crosscheck(
            &format!(
                r#"
                    (define-private (some-fn {args_signature})
                        {}
                    )
                    (some-fn {call_args})
                "#, args_name[return_index]
            ),
            Ok(Some(values[return_index].clone().into())),
        )
    }

    #[test]
    fn crossprop_define_private_can_use_all_arguments((tys, values) in strategies_for_function_signature()) {
        let (args_signature, args_name) = format_args_signature(&tys);
        let call_args = join_stringified(&values);

        let return_exp = args_name.iter().map(|arg| format!("ret-{arg}: {arg}")).collect::<Vec<_>>().join(", ");
        let expected = TupleData::from_data(
            args_name.iter()
                .map(|arg| ClarityName::try_from(format!("ret-{arg}")).unwrap())
                .zip(values.into_iter().map(Value::from))
                .collect(),
        )
        .unwrap()
        .into();

        crosscheck(
            &format!(
                r#"
                    (define-private (some-fn {args_signature})
                        {{ {return_exp} }}
                    )
                    (some-fn {call_args})
                "#,
            ),
            Ok(Some(expected)),
        )
    }

    #[test]
    fn crossprop_define_private_side_effects(
        (tys, values) in strategies_for_function_signature(),
        response in strategies_for_response())
    {
        let (args_signature, _) = format_args_signature(&tys);
        let call_args = join_stringified(&values);

        let expected = TupleData::from_data(vec![
            (ClarityName::from_literal("fn"), response.clone().into()),
            // Response does not affect private functions
            (ClarityName::from_literal("side"), Value::Bool(true)),
        ]).unwrap().into();

        crosscheck(
            &format!(
                r#"
                    (define-data-var side bool false)
                    (define-private (some-fn {args_signature})
                        (begin 
                            (var-set side true)
                            {response}
                        )
                    )
                    {{ fn: (some-fn {call_args}), side: (var-get side) }}
                "#,
            ),
            Ok(Some(expected)),
        )
    }


    #[test]
    fn crossprop_define_public_accepts_any_args(
        (tys, values) in strategies_for_function_signature(),
        response in strategies_for_response())
    {
        let (args_signature, _) = format_args_signature(&tys);
        let call_args = join_stringified(&values);
        crosscheck(
            &format!(
                r#"
                    (define-public (some-fn {args_signature})
                        {response}
                    )
                    (some-fn {call_args})
                "#,
            ),
            Ok(Some(response.into())),
        )
    }

    #[test]
    fn crossprop_define_public_returns_any_argument(
        ((tys, values), return_index) in strategies_for_function_signature().prop_ind_flat_map2(|(tys, _)| 0..tys.len()),
        response_ok in any::<bool>()
    ) {
        let (args_signature, args_name) = format_args_signature(&tys);
        let call_args = join_stringified(&values);
        let expected = Value::Response(ResponseData {
            committed: response_ok,
            data: Box::new(values[return_index].clone().into()),
        });
        crosscheck(
            &format!(
                r#"
                    (define-public (some-fn {args_signature})
                        ({} {})
                    )
                    (some-fn {call_args})
                "#, if response_ok { "ok" } else { "err" }, args_name[return_index]
            ),
            Ok(Some(expected)),
        )
    }

    #[test]
    fn crossprop_define_public_can_use_all_arguments(
        (tys, values) in strategies_for_function_signature(),
        response_ok in any::<bool>()
    ) {
        let (args_signature, args_name) = format_args_signature(&tys);
        let call_args = join_stringified(&values);

        let return_exp = args_name.iter().map(|arg| format!("ret-{arg}: {arg}")).collect::<Vec<_>>().join(", ");
        let expected = TupleData::from_data(
            args_name.iter()
                .map(|arg| ClarityName::try_from(format!("ret-{arg}")).unwrap())
                .zip(values.into_iter().map(Value::from))
                .collect(),
        ).unwrap();
        let expected = Value::Response(ResponseData {
            committed: response_ok,
            data: Box::new(expected.into()),
        });

        crosscheck(
            &format!(
                r#"
                    (define-public (some-fn {args_signature})
                        ({} {{ {return_exp} }})
                    )
                    (some-fn {call_args})
                "#, if response_ok { "ok" } else { "err" }
            ),
            Ok(Some(expected)),
        )
    }

    #[test]
    fn crossprop_define_public_side_effects(
        (tys, values) in strategies_for_function_signature(),
        response in strategies_for_response())
    {
        let (args_signature, _) = format_args_signature(&tys);
        let call_args = join_stringified(&values);

        let expected = TupleData::from_data(vec![
            (ClarityName::from_literal("fn"), response.clone().into()),
            // Err responses revert changes (`(var-set side true)`)
            (ClarityName::from_literal("side"), Value::Bool(
                match response {
                    PropValue(Value::Response(ResponseData{ committed, ..})) => committed,
                    _ => unreachable!("Expected a response")
                }
            )),
        ]).unwrap().into();

        crosscheck(
            &format!(
                r#"
                    (define-data-var side bool false)
                    (define-public (some-fn {args_signature})
                        (begin 
                            (var-set side true)
                            {response}
                        )
                    )
                    {{ fn: (some-fn {call_args}), side: (var-get side) }}
                "#,
            ),
            Ok(Some(expected)),
        )
    }


    #[test]
    fn crossprop_define_readonly_accepts_any_args(
        (tys, values) in strategies_for_function_signature(),
        result in PropValue::any().no_shrink()
    ) {
        let (args_signature, _) = format_args_signature(&tys);
        let call_args = join_stringified(&values);
        crosscheck(
            &format!(
                r#"
                    (define-read-only (some-fn {args_signature})
                        {result}
                    )
                    (some-fn {call_args})
                "#,
            ),
            Ok(Some(result.into())),
        )
    }

    #[test]
    fn crossprop_define_readonly_returns_any_argument(
        ((tys, values), return_index) in strategies_for_function_signature().prop_ind_flat_map2(|(tys, _)| 0..tys.len()),
    ) {
        let (args_signature, args_name) = format_args_signature(&tys);
        let call_args = join_stringified(&values);
        crosscheck(
            &format!(
                r#"
                    (define-read-only (some-fn {args_signature})
                        {}
                    )
                    (some-fn {call_args})
                "#, args_name[return_index]
            ),
            Ok(Some(values[return_index].clone().into())),
        )
    }

    #[test]
    fn crossprop_define_readonly_can_use_all_arguments((tys, values) in strategies_for_function_signature()) {
        let (args_signature, args_name) = format_args_signature(&tys);
        let call_args = join_stringified(&values);

        let return_exp = args_name.iter().map(|arg| format!("ret-{arg}: {arg}")).collect::<Vec<_>>().join(", ");
        let expected = TupleData::from_data(
            args_name.iter()
                .map(|arg| ClarityName::try_from(format!("ret-{arg}")).unwrap())
                .zip(values.into_iter().map(Value::from))
                .collect(),
        )
        .unwrap()
        .into();

        crosscheck(
            &format!(
                r#"
                    (define-read-only (some-fn {args_signature})
                        {{ {return_exp} }}
                    )
                    (some-fn {call_args})
                "#,
            ),
            Ok(Some(expected)),
        )
    }
}
