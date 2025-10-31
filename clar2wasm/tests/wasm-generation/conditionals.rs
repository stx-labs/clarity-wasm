use clar2wasm::tools::{crosscheck, crosscheck_compare_only};
use clarity::vm::errors::{Error, ShortReturnType};
use clarity::vm::types::{ListTypeData, SequenceData, SequenceSubtype, TypeSignature};
use clarity::vm::Value;
use proptest::prelude::*;

use crate::{prop_signature, type_string, PropValue};

proptest! {
    #![proptest_config(super::runtime_config())]
    #[test]
    fn if_true_returns_first_value(
        (v1, v2) in prop_signature()
        .prop_flat_map(|ty| {
            (PropValue::from_type(ty.clone()), PropValue::from_type(ty))
        })
    )
    {
        crosscheck(
            &format!(r#"(if true {v1} {v2})"#),
            Ok(Some(v1.into()))
        )
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]
    #[test]
    fn if_false_returns_second_value(
        (v1, v2) in prop_signature()
        .prop_flat_map(|ty| {
            (PropValue::from_type(ty.clone()), PropValue::from_type(ty))
        })
    )
    {
        crosscheck(
            &format!(r#"(if false {v1} {v2})"#),
            Ok(Some(v2.into()))
        )
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]
    #[test]
    fn match_optional_some(
        (initial, some_val, none_val) in (prop_signature(), prop_signature())
        .prop_flat_map(|(original_ty, ty)| {
            (PropValue::from_type(original_ty), PropValue::from_type(ty.clone()), PropValue::from_type(ty))
        })
    )
    {
        crosscheck(
            &format!("(match (some {initial}) value {some_val} {none_val})"),
            Ok(Some(some_val.into()))
        )
    }

    #[test]
    fn match_optional_none(
        (original_ty, some_val, none_val) in (prop_signature(), prop_signature())
        .prop_flat_map(|(original_ty, ty)| {
            (Just(original_ty), PropValue::from_type(ty.clone()), PropValue::from_type(ty))
        })
    )
    {
        crosscheck(
            &format!(r#"
                (define-data-var null (optional {}) none)
                (match (var-get null) value {some_val} {none_val})
            "#, type_string(&original_ty)),
            Ok(Some(none_val.into()))
        )
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn unwrap_optional_some(
        val in PropValue::any(),
        throw_val in PropValue::any()
    ) {
        let snippet = format!(r#"(unwrap! (some {val}) {throw_val})"#);

        crosscheck(&snippet, Ok(Some(val.into())));
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn unwrap_optional_none(
        val in PropValue::any(),
        throw_val in PropValue::any(),
    ) {
        let snippet = format!(r#"(unwrap! (if true none (some {val})) {throw_val})"#);

        crosscheck(
            &snippet,
            Err(Error::ShortReturn(ShortReturnType::ExpectedValue(Box::new(Value::from(throw_val)))))
        );
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn unwrap_response_ok(
        val in PropValue::any(),
        throw_val in PropValue::any(),
    ) {
        let snippet = format!(r#"(unwrap! (ok {val}) {throw_val})"#);

        crosscheck(&snippet, Ok(Some(val.into())));
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn unwrap_response_err(
        ok_val in PropValue::any(),
        err_val in PropValue::any(),
        throw_val in PropValue::any(),
    ) {
        let snippet = format!(r#"(unwrap! (if true (err {err_val}) (ok {ok_val})) {throw_val})"#);

        crosscheck(
            &snippet,
            Err(Error::ShortReturn(ShortReturnType::ExpectedValue(Box::new(Value::from(throw_val)))))
        );
    }

    #[test]
    fn unwrap_response_err_inside_function(
        err_val in PropValue::any(),
        (ok_val, throw_val) in prop_signature()
            .prop_flat_map(|t| (PropValue::from_type(t.clone()), PropValue::from_type(t))),
    ) {
        let snippet = format!("
            (define-private (foo)
                (unwrap! (if true (err {err_val}) (ok {ok_val})) {throw_val})
            )
            (foo)
        ");

        crosscheck(&snippet, Ok(Some(throw_val.into())));
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn unwrap_optional_none_inside_function(
        (some_val, throw_val) in prop_signature()
            .prop_flat_map(|t| (PropValue::from_type(t.clone()), PropValue::from_type(t)))
    ) {
        let snippet = format!("
            (define-private (foo)
                (unwrap! (if true none (some {some_val})) {throw_val})
            )
            (foo)
        ");

        crosscheck(&snippet, Ok(Some(throw_val.into())));
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn unwrap_optional_some_with_begin(
        some_val in PropValue::any().prop_filter("avoid intermediary unchecked responses", |v| {
            !matches!(v, PropValue(Value::Response(_)))
        }),
        (throw_val, val) in prop_signature()
            .prop_flat_map(|t| (PropValue::from_type(t.clone()), PropValue::from_type(t))),
    ) {
        let snippet = format!(r#"
            (begin
                (unwrap! (some {some_val}) {throw_val})
                {val}
            )
        "#);

        crosscheck(&snippet, Ok(Some(val.into())));
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn unwrap_optional_none_with_begin(
        some_val in PropValue::any().prop_filter("avoid intermediary unchecked responses", |v| {
            !matches!(v, PropValue(Value::Response(_)))
        }),
        (throw_val, val) in prop_signature()
            .prop_flat_map(|t| (PropValue::from_type(t.clone()), PropValue::from_type(t))),
    ) {
        let snippet = format!(r#"
            (begin
                (unwrap! (if true none (some {some_val})) {throw_val})
                {val}
            )
        "#);

        crosscheck(
            &snippet,
            Err(Error::ShortReturn(ShortReturnType::ExpectedValue(Box::new(Value::from(throw_val)))))
        );
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn unwrap_response_ok_with_begin(
        ok_val in PropValue::any().prop_filter("avoid intermediary unchecked responses", |v| {
            !matches!(v, PropValue(Value::Response(_)))
        }),
        (throw_val, val) in prop_signature()
            .prop_flat_map(|t| (PropValue::from_type(t.clone()), PropValue::from_type(t))),
    ) {
        let snippet = format!(r#"
            (begin
                (unwrap! (ok {ok_val}) {throw_val})
                {val}
            )
        "#);

        crosscheck(&snippet, Ok(Some(val.into())));
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn unwrap_response_err_with_begin(
        ok_val in PropValue::any().prop_filter("avoid intermediary unchecked responses", |v| {
            !matches!(v, PropValue(Value::Response(_)))
        }),
        err_val in PropValue::any(),
        (throw_val, val) in prop_signature()
            .prop_flat_map(|t| (PropValue::from_type(t.clone()), PropValue::from_type(t))),
    ) {
        let snippet = format!(r#"
            (begin
                (unwrap! (if true (err {err_val}) (ok {ok_val})) {throw_val})
                {val}
            )
        "#);

        crosscheck(
            &snippet,
            Err(Error::ShortReturn(ShortReturnType::ExpectedValue(Box::new(Value::from(throw_val)))))
        );
    }

    #[test]
    fn unwrap_response_err_inside_function_with_begin(
        ok_val in PropValue::any().prop_filter("avoid intermediary unchecked responses", |v| {
            !matches!(v, PropValue(Value::Response(_)))
        }),
        err_val in PropValue::any(),
        (throw_val, val) in prop_signature()
            .prop_flat_map(|t| (PropValue::from_type(t.clone()), PropValue::from_type(t))),
    ) {
        let snippet = format!("
            (define-private (foo)
                (begin
                    (unwrap! (if true (err {err_val}) (ok {ok_val})) {throw_val})
                    {val}
                )
            )
            (foo)
        ");

        crosscheck(&snippet, Ok(Some(throw_val.into())));
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn unwrap_optional_none_inside_function_with_begin(
        some_val in PropValue::any().prop_filter("avoid intermediary unchecked responses", |v| {
            !matches!(v, PropValue(Value::Response(_)))
        }),
        (throw_val, val) in prop_signature()
            .prop_flat_map(|t| (PropValue::from_type(t.clone()), PropValue::from_type(t)))
    ) {
        let snippet = format!("
            (define-private (foo)
                (begin
                    (unwrap! (if true none (some {some_val})) {throw_val})
                    {val}
                )
            )
            (foo)
        ");

        crosscheck(&snippet, Ok(Some(throw_val.into())));
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn unwrap_err_response_ok(
        ok_val in PropValue::any(),
        (err_val, throw_val) in prop_signature()
            .prop_flat_map(|t| (PropValue::from_type(t.clone()), PropValue::from_type(t)))
    ) {
        let snippet = format!("
            (unwrap-err! (if true (ok {ok_val}) (err {err_val})) {throw_val})
        ");

        crosscheck(
            &snippet,
            Err(Error::ShortReturn(ShortReturnType::ExpectedValue(Box::new(Value::from(throw_val)))))
        );
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn unwrap_err_response_err(
        ok_val in PropValue::any(),
        (err_val, throw_val) in prop_signature()
            .prop_flat_map(|t| (PropValue::from_type(t.clone()), PropValue::from_type(t))),
    ) {
        let snippet = format!("
            (unwrap-err! (if false (ok {ok_val}) (err {err_val})) {throw_val})
        ");

        crosscheck(&snippet, Ok(Some(err_val.into())));
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn unwrap_err_response_ok_inside_function(
        ok_val in PropValue::any(),
        (err_val, throw_val) in prop_signature()
            .prop_flat_map(|t| (PropValue::from_type(t.clone()), PropValue::from_type(t)))
    ) {
        let snippet = format!("
            (define-private (foo)
                (unwrap-err! (if true (ok {ok_val}) (err {err_val})) {throw_val})
            )
            (foo)
        ");

        crosscheck(&snippet, Ok(Some(throw_val.into())));
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn unwrap_err_response_err_inside_function(
        ok_val in PropValue::any(),
        (err_val, throw_val) in prop_signature()
            .prop_flat_map(|t| (PropValue::from_type(t.clone()), PropValue::from_type(t))),
    ) {
        let snippet = format!("
            (define-private (foo)
                (unwrap-err! (if false (ok {ok_val}) (err {err_val})) {throw_val})
            )
            (foo)
        ");

        crosscheck(&snippet, Ok(Some(err_val.into())));
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn unwrap_err_response_ok_with_begin(
        ok_val in PropValue::any(),
        err_val in PropValue::any().prop_filter("avoid intermediary unchecked responses", |v| {
            !matches!(v, PropValue(Value::Response(_)))
        }),
        (throw_val, val) in prop_signature()
            .prop_flat_map(|t| (PropValue::from_type(t.clone()), PropValue::from_type(t))),
    ) {
        let snippet = format!("
            (begin
                (unwrap-err! (if true (ok {ok_val}) (err {err_val})) {throw_val})
                {val}
            )
        ");

        crosscheck(
            &snippet,
            Err(Error::ShortReturn(ShortReturnType::ExpectedValue(Box::new(Value::from(throw_val)))))
        );
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn unwrap_err_response_err_with_begin(
        ok_val in PropValue::any(),
        err_val in PropValue::any().prop_filter("avoid intermediary unchecked responses", |v| {
            !matches!(v, PropValue(Value::Response(_)))
        }),
        (throw_val, val) in prop_signature()
            .prop_flat_map(|t| (PropValue::from_type(t.clone()), PropValue::from_type(t))),
    ) {
        let snippet = format!("
            (begin
                (unwrap-err! (if false (ok {ok_val}) (err {err_val})) {throw_val})
                {val}
            )
        ");

        crosscheck(&snippet, Ok(Some(val.into())));
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn unwrap_err_response_ok_inside_function_with_begin(
        ok_val in PropValue::any(),
        err_val in PropValue::any().prop_filter("avoid intermediary unchecked responses", |v| {
            !matches!(v, PropValue(Value::Response(_)))
        }),
        (throw_val, val) in prop_signature()
            .prop_flat_map(|t| (PropValue::from_type(t.clone()), PropValue::from_type(t))),
    ) {
        let snippet = format!("
            (define-private (foo)
                (begin
                    (unwrap-err! (if true (ok {ok_val}) (err {err_val})) {throw_val})
                    {val}
                )
            )
            (foo)
        ");

        crosscheck(&snippet, Ok(Some(throw_val.into())));
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn unwrap_err_response_err_inside_function_with_begin(
        ok_val in PropValue::any(),
        err_val in PropValue::any().prop_filter("avoid intermediary unchecked responses", |v| {
            !matches!(v, PropValue(Value::Response(_)))
        }),
        (throw_val, val) in prop_signature()
            .prop_flat_map(|t| (PropValue::from_type(t.clone()), PropValue::from_type(t))),
    ) {
        let snippet = format!("
            (define-private (foo)
                (begin
                    (unwrap-err! (if false (ok {ok_val}) (err {err_val})) {throw_val})
                    {val}
                )
            )
            (foo)
        ");

        crosscheck(&snippet, Ok(Some(val.into())));
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn asserts_true(throw_val in PropValue::any()) {
        crosscheck(
            &format!("(asserts! true {throw_val})"),
            Ok(Some(Value::Bool(true))),
        );
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn asserts_false(throw_val in PropValue::any()) {
        crosscheck(
            &format!("(asserts! false {throw_val})"),
            Err(Error::ShortReturn(ShortReturnType::AssertionFailed(Box::new(Value::from(throw_val))))),
        );
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn asserts_with_begin_true(
        (throw_val, val) in prop_signature()
            .prop_flat_map(|t| (PropValue::from_type(t.clone()), PropValue::from_type(t))),
    ) {
        let snippet = format!("
            (begin
                (asserts! true {throw_val})
                {val}
            )
        ");

        crosscheck(&snippet, Ok(Some(val.into())));
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn asserts_with_begin_false(
        (throw_val, val) in prop_signature()
            .prop_flat_map(|t| (PropValue::from_type(t.clone()), PropValue::from_type(t))),
    ) {
        let snippet = format!("
            (begin
                (asserts! false {throw_val})
                {val}
            )
        ");

        crosscheck(
            &snippet,
            Err(Error::ShortReturn(ShortReturnType::AssertionFailed(Box::new(Value::from(throw_val))))),
        );
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn asserts_in_function_true(
        (throw_val, val) in prop_signature()
            .prop_flat_map(|t| (PropValue::from_type(t.clone()), PropValue::from_type(t))),
    ) {
        let snippet = format!("
            (define-private (foo)
                (begin
                    (asserts! true {throw_val})
                    {val}
                )
            )
            (foo)
        ");

        crosscheck(&snippet, Ok(Some(val.into())));
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn asserts_in_function_false(
        (throw_val, val) in prop_signature()
            .prop_flat_map(|t| (PropValue::from_type(t.clone()), PropValue::from_type(t))),
    ) {
        let snippet = format!("
            (define-private (foo)
                (begin
                    (asserts! false {throw_val})
                    {val}
                )
            )
            (foo)
        ");

        crosscheck(&snippet, Ok(Some(throw_val.into())));
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn try_some(val in PropValue::any()) {
        crosscheck(
            &format!("(try! (some {val}))"),
            Ok(Some(Value::from(val))),
        );
    }

    #[test]
    fn try_none(val in PropValue::any()) {
        crosscheck(
            &format!("(try! (if false (some {val}) none))"),
            Err(Error::ShortReturn(ShortReturnType::ExpectedValue(Box::new(Value::none()))))

        );
    }

    #[test]
    fn try_ok(
        ok_val in PropValue::any(),
        err_val in PropValue::any(),
    ) {
        crosscheck(
            &format!("(try! (if true (ok {ok_val}) (err {err_val})))"),
            Ok(Some(Value::from(ok_val)))
        );
    }

    #[test]
    fn try_err(
        ok_val in PropValue::any(),
        err_val in PropValue::any(),
    ) {
        crosscheck(
            &format!("(try! (if false (ok {ok_val}) (err {err_val})))"),
            Err(Error::ShortReturn(ShortReturnType::ExpectedValue(
                Box::new(Value::error(err_val.into()).unwrap()),
            ))),
        );
    }

    #[test]
    fn try_with_begin_some(
        (some_val, val) in prop_signature()
            .prop_filter("avoid intermediary unchecked responses", |t| {
                !matches!(t, TypeSignature::ResponseType(_))
            })
            .prop_flat_map(|t| (PropValue::from_type(t.clone()), PropValue::from_type(t)))
    ) {
        let snippet = format!("
            (begin
                (try! (some {some_val}))
                {val}
            )
        ");

        crosscheck(
            &snippet,
            Ok(Some(Value::from(val))),
        );
    }

    #[test]
    fn try_with_begin_none(
        (some_val, val) in prop_signature()
            .prop_filter("avoid intermediary unchecked responses", |t| {
                !matches!(t, TypeSignature::ResponseType(_))
            })
            .prop_flat_map(|t| (PropValue::from_type(t.clone()), PropValue::from_type(t)))
    ) {
        let snippet = format!("
            (begin
                (try! (if false (some {some_val}) none))
                {val}
            )
        ");

        crosscheck(
            &snippet,
            Err(Error::ShortReturn(ShortReturnType::ExpectedValue(Box::new(Value::none())))),
        );
    }

    #[test]
    fn try_with_begin_ok(
        (ok_val, val) in prop_signature()
            .prop_filter("avoid intermediary unchecked responses", |t| {
                !matches!(t, TypeSignature::ResponseType(_))
            })
            .prop_flat_map(|t| (PropValue::from_type(t.clone()), PropValue::from_type(t))),
        err_val in PropValue::any(),
    ) {
        let snippet = format!("
            (begin
                (try! (if true (ok {ok_val}) (err {err_val})))
                {val}
            )
        ");

        crosscheck(
            &snippet,
            Ok(Some(Value::from(val))),
        );
    }

    #[test]
    fn try_with_begin_err(
        (ok_val, val) in prop_signature()
            .prop_filter("avoid intermediary unchecked responses", |t| {
                !matches!(t, TypeSignature::ResponseType(_))
            })
            .prop_flat_map(|t| (PropValue::from_type(t.clone()), PropValue::from_type(t))),
        err_val in PropValue::any(),
    ) {
        let snippet = format!("
            (begin
                (try! (if false (ok {ok_val}) (err {err_val})))
                {val}
            )
        ");

        crosscheck(
            &snippet,
            Err(Error::ShortReturn(ShortReturnType::ExpectedValue(
                Box::new(Value::error(err_val.into()).unwrap()),
            ))),
        );
    }

    #[test]
    fn try_in_function_some(
        some_val in PropValue::any()
    ) {
        let snippet = format!("
            (define-private (foo)
                (some (try! (some {some_val})))
            )
            (foo)
        ");

        crosscheck(
            &snippet,
            Ok(Some(Value::some(some_val.into()).unwrap())),
        );
    }

    #[test]
    fn try_in_function_none(
        some_val in PropValue::any()
    ) {
        let snippet = format!("
            (define-private (foo)
                (some (try! (if false (some {some_val}) none)))
            )
            (foo)
        ");

        crosscheck(
            &snippet,
            Ok(Some(Value::none())),
        );
    }

    #[test]
    fn try_in_function_ok(
        ok_val in PropValue::any(),
        err_val in PropValue::any(),
    ) {
        let snippet = format!("
            (define-private (foo)
                (ok (try! (if true (ok {ok_val}) (err {err_val}))))
            )
            (foo)
        ");

        crosscheck(
            &snippet,
            Ok(Some(Value::okay(ok_val.into()).unwrap())),
        );
    }

    #[test]
    fn try_in_function_err(
        ok_val in PropValue::any(),
        err_val in PropValue::any(),
    ) {
        let snippet = format!("
            (define-private (foo)
                (ok (try! (if false (ok {ok_val}) (err {err_val}))))
            )
            (foo)
        ");

        crosscheck(
            &snippet,
            Ok(Some(Value::error(err_val.into()).unwrap())),
        );
    }

    #[test]
    fn try_in_function_with_begin_ok(
        (ok_val, val) in prop_signature()
            .prop_filter("avoid intermediary unchecked responses", |t| {
                !matches!(t, TypeSignature::ResponseType(_))
            })
            .prop_flat_map(|t| (PropValue::from_type(t.clone()), PropValue::from_type(t))),
        err_val in PropValue::any(),
    ) {
        let snippet = format!("
            (define-private (foo)
                (begin
                    (try! (if true (ok {ok_val}) (err {err_val})))
                    (ok {val})
                )
            )
            (foo)
        ");

        crosscheck(
            &snippet,
            Ok(Some(Value::okay(val.into()).unwrap())),
        );
    }

    #[test]
    fn try_in_function_with_begin_err(
        (ok_val, val) in prop_signature()
            .prop_filter("avoid intermediary unchecked responses", |t| {
                !matches!(t, TypeSignature::ResponseType(_))
            })
            .prop_flat_map(|t| (PropValue::from_type(t.clone()), PropValue::from_type(t))),
        err_val in PropValue::any(),
    ) {
        let snippet = format!("
            (define-private (foo)
                (begin
                    (try! (if false (ok {ok_val}) (err {err_val})))
                    (ok {val})
                )
            )
            (foo)
        ");

        crosscheck(
            &snippet,
            Ok(Some(Value::error(err_val.into()).unwrap())),
        );
    }
}

const FILTER_PRELUDE: &str = "
(define-private (is-even? (x int))
        (is-eq (* (/ x 2) 2) x))

(define-private (grob (x (response int int)))
  (match x
    a (is-even? a)
    b (not (is-even? b))))";

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn crosscheck_filter_responses_short(
        seq in PropValue::from_type(
            TypeSignature::SequenceType(
                SequenceSubtype::ListType(
                    ListTypeData::new_list(
                        TypeSignature::ResponseType(
                            Box::new((TypeSignature::IntType, TypeSignature::IntType))),
                        2).unwrap()
                )
            )
        )
    ) {
        if let Value::Sequence(SequenceData::List(ld)) = seq.inner() {
            // Empty sequences fail in interpreter as well
            if !ld.data.is_empty() {
                let snippet = format!("{FILTER_PRELUDE} (filter grob {seq})");

                crosscheck_compare_only(
                    &snippet,
                );
            }
        }
    }

    #[test]
    fn crosscheck_filter_responses_long(
        seq in PropValue::from_type(
            TypeSignature::SequenceType(
                SequenceSubtype::ListType(
                    ListTypeData::new_list(
                        TypeSignature::ResponseType(
                            Box::new((TypeSignature::IntType, TypeSignature::IntType))),
                        100).unwrap()
                )
            )
        )
    ) {
        if let Value::Sequence(SequenceData::List(ld)) = seq.inner() {
            // Empty sequences fail in interpreter as well
            if !ld.data.is_empty() {
                let snippet = format!("{FILTER_PRELUDE} (filter grob {seq})");

                crosscheck_compare_only(
                    &snippet,
                );
            }
        }
    }
}

//
// Proptests that should only be executed
// when running Clarity::V2 or Clarity::v3.
//
#[cfg(not(feature = "test-clarity-v1"))]
mod clarity_v2_v3 {
    use super::*;
    use crate::runtime_config;

    proptest! {
        #![proptest_config(runtime_config())]

        // TODO: see issue #497.
        // The test below should pass when running it in ClarityV1.
        // When issue is fixed this test should be removed from this clarity_v2_v3 module.
        #[test]
        fn match_response_ok(
            (original_ok_ty, original_ok_val, original_err_ty, ok_val, err_val) in (prop_signature(), prop_signature(), prop_signature())
            .prop_flat_map(|(original_ok_ty, original_err_ty, ty)| {
                (Just(original_ok_ty.clone()), PropValue::from_type(original_ok_ty), Just(original_err_ty), PropValue::from_type(ty.clone()), PropValue::from_type(ty))
            })
        )
        {
            crosscheck(
                &format!(r#"
                    (define-data-var okval (response {} {}) (ok {original_ok_val}))
                    (match (var-get okval) value {ok_val} err-value {err_val})
                "#, type_string(&original_ok_ty), type_string(&original_err_ty)),
                Ok(Some(ok_val.into()))
            )
        }

        // TODO: see issue #497.
        // The test below should pass when running it in ClarityV1.
        // When issue is fixed this test should be removed from this clarity_v2_v3 module.
        #[test]
        fn match_response_err(
            (original_ok_ty, original_err_ty, original_err_val, ok_val, err_val) in (prop_signature(), prop_signature(), prop_signature())
            .prop_flat_map(|(original_ok_ty, original_err_ty, ty)| {
                (Just(original_ok_ty), Just(original_err_ty.clone()), PropValue::from_type(original_err_ty), PropValue::from_type(ty.clone()), PropValue::from_type(ty))
            })
        )
        {
            crosscheck(
                &format!(r#"
                    (define-data-var errval (response {} {}) (err {original_err_val}))
                    (match (var-get errval) value {ok_val} err-value {err_val})
                "#, type_string(&original_ok_ty), type_string(&original_err_ty)),
                Ok(Some(err_val.into()))
            )
        }
    }
}
