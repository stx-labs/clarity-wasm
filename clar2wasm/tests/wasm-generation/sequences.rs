use clar2wasm::tools::{crosscheck, crosscheck_compare_only};
use clarity::vm::types::{
    ListData, ListTypeData, SequenceData, SequenceSubtype, SequencedValue, TypeSignature,
    MAX_VALUE_SIZE,
};
use clarity::vm::Value;
use proptest::prelude::*;

use crate::{bool, buffer, int, list, prop_signature, type_string, PropValue};

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn append_value_to_list(mut values in (prop_signature(), 1usize..16).prop_flat_map(|(ty, size)| PropValue::many_from_type(ty, size))) {
        let expected = Value::cons_list_unsanitized(values.iter().cloned().map(Value::from).collect());
        prop_assume!(expected.is_ok(), "Couldn't generate a valid list");
        let expected = expected.unwrap();

        let elem = values.pop().unwrap();
        let values = PropValue::try_from(values).unwrap();

        crosscheck(&format!("(append {values} {elem})"), Ok(Some(expected)))
    }

    #[test]
    fn double_append_value_to_list(mut values in (prop_signature(), 2usize..16).prop_flat_map(|(ty, size)| PropValue::many_from_type(ty, size))) {
        let expected = Value::cons_list_unsanitized(values.iter().cloned().map(Value::from).collect());
        prop_assume!(expected.is_ok(), "Couldn't generate a valid list");
        let expected = expected.unwrap();

        let elem_last = values.pop().unwrap();
        let elem_before_last = values.pop().unwrap();
        let values = PropValue::try_from(values).unwrap();

        crosscheck(&format!("(append (append {values} {elem_before_last}) {elem_last})"), Ok(Some(expected)))
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn as_max_len_equal_max_len_is_some((max_len, value) in (0usize..=16).prop_ind_flat_map2(PropValue::any_sequence)) {
        crosscheck(
            &format!("(as-max-len? {value} u{max_len})"),
            Ok(Some(Value::some(value.into()).unwrap()))
        )
    }

    #[test]
    fn as_max_len_smaller_than_len_is_none((max_len, value) in (1usize..=16).prop_ind_flat_map2(PropValue::any_sequence)) {
        crosscheck(
            &format!("(as-max-len? {value} u{})", max_len-1),
            Ok(Some(Value::none()))
        )
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn concat_crosscheck(
        (seq1, seq2) in (0usize..=16)
            .prop_flat_map(PropValue::any_sequence)
            .prop_ind_flat_map2(|seq1| PropValue::from_type(TypeSignature::type_of(&seq1.into()).expect("Could not get type signature")))
            .prop_filter("skip large values", |(seq1, seq2)| seq1.inner().size().unwrap() + seq2.inner().size().unwrap() <= MAX_VALUE_SIZE)
    ) {
        let snippet = format!("(concat {seq1} {seq2})");

        let expected = {
            let Value::Sequence(mut seq_data1) = seq1.into() else { unreachable!() };
            let Value::Sequence(seq_data2) = seq2.into() else { unreachable!() };
            seq_data1.concat(&clarity::types::StacksEpochId::latest(), seq_data2).expect("Unable to concat sequences");
            Value::Sequence(seq_data1)
        };

        crosscheck(&snippet, Ok(Some(expected)));
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn len_crosscheck(seq in (1usize..=16).prop_flat_map(PropValue::any_sequence)) {
        let snippet = format!("(len {seq})");

        let expected = {
            let Value::Sequence(seq_data) = seq.into() else { unreachable!() };
            Value::UInt(seq_data.len() as u128)
        };

        crosscheck(&snippet, Ok(Some(expected)));
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn crosscheck_map_add(
        seq in proptest::collection::vec(proptest::collection::vec(1u128..=1000, 1..=100), 1..=50)
    ) {

        let result: Vec<_> = seq.iter()
        .skip(1).fold(seq[0].clone(), |acc, vecint| {
            acc.into_iter()
            .zip(vecint.iter())
            .map(|(x, y)| x + y)
            .collect()
        })
        .iter().map(|el| Value::UInt(*el)).collect();

        let expected = Value::Sequence(
            SequenceData::List(
                ListData {
                    data: result.clone(),
                    type_signature: ListTypeData::new_list(TypeSignature::UIntType, result.len() as u32).unwrap()
                }
            )
        );

        let lists: Vec<_> = seq.iter().map(|v| {
            v.iter().map(|&el| {
                Value::UInt(el)
            }).collect::<Vec<_>>()
        })
        .map(|v| {
            Value::Sequence(
                SequenceData::List(
                    ListData {
                        data: v.clone(),
                        type_signature: ListTypeData::new_list(TypeSignature::UIntType, v.len() as u32).unwrap()
                    }
                )
            )
        })
        .map(PropValue::from).collect();

        let lists_str: String = lists.iter().map(|el| el.to_string() + " ").collect();
        let snippet = format!("(map + {lists_str})");

        crosscheck(
            &snippet,
            Ok(Some(expected))
        )
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn crosscheck_map_not(
        seq in proptest::collection::vec(bool(), 1..=100)
        .prop_map(|v| {
            Value::Sequence(
                SequenceData::List(
                    ListData {
                        data: v.clone(),
                        type_signature: ListTypeData::new_list(TypeSignature::BoolType, v.len() as u32).unwrap()
                    }
                )
            )
        }).prop_map(PropValue::from)
    ) {
        let expected = extract_sequence(seq.clone());
        let snippet = format!("(map not (map not {seq}))");

        crosscheck(
            &snippet,
            Ok(Some(Value::Sequence(expected)))
        )
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn crosscheck_map_concat_int(
        seq_1 in proptest::collection::vec(int(), 1..=100)
            .prop_map(|v| {
                Value::Sequence(
                    SequenceData::List(
                        ListData {
                            data: v.clone(),
                            type_signature: ListTypeData::new_list(TypeSignature::IntType, v.len() as u32).unwrap()
                        }
                    )
                )
            }).prop_map(PropValue::from),
        seq_2 in proptest::collection::vec(int(), 1..=100)
            .prop_map(|v| {
                Value::Sequence(
                    SequenceData::List(
                        ListData {
                            data: v.clone(),
                            type_signature: ListTypeData::new_list(TypeSignature::IntType, v.len() as u32).unwrap()
                        }
                    )
                )
            }).prop_map(PropValue::from)
    ) {
        let mut expected = extract_sequence(seq_1.clone());
        expected.concat(
            &clarity::types::StacksEpochId::latest(),
            extract_sequence(seq_2.clone())
        ).expect("Could not concat sequences");

        crosscheck(
            &format!(r#"(define-private (fun (a (list 100 int)) (b (list 100 int))) (concat a b)) (try! (element-at (map fun (list {seq_1}) (list {seq_2})) u0))"#),
            Ok(Some(Value::Sequence(expected)))
        )
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn crosscheck_map_append(
        (ty, seq, elem) in prop_signature().prop_flat_map(|ty| {
            let seq = {
                let ty = ty.clone();
                (1..=10u32, 1..=10u32).prop_flat_map(move |(outer_count, inner_count)| {
                    PropValue::from_type(
                        TypeSignature::list_of(
                            TypeSignature::list_of(ty.clone(), inner_count).unwrap(),
                            outer_count,
                        )
                        .unwrap(),
                    )
                })
            };
            let elem = {
                let ty = ty.clone();
                (1..10u32).prop_flat_map(move |count| {
                    PropValue::from_type(TypeSignature::list_of(ty.clone(), count).unwrap())
                })
            };

            (Just(ty).no_shrink(), seq.no_shrink(), elem.no_shrink())
        })
    ) {
        let snippet = format!(
            r#"
                (define-private (foo (a (list 100 {t})) (b {t}))
                    (append a b)
                ) 

                (map foo {seq} {elem})
            "#,
            t = type_string(&ty)
        );

        let expected = {
            let SequenceData::List(seq) = extract_sequence(seq) else {
                unreachable!()
            };
            let SequenceData::List(elem) = extract_sequence(elem) else {
                unreachable!()
            };

            let mut res = Vec::with_capacity(seq.items().len().min(elem.items().len()));
            for (s, e) in seq.items().iter().zip(elem.items()) {
                let Value::Sequence(SequenceData::List(s)) = s else {
                    unreachable!()
                };

                let mut item = Vec::with_capacity(s.items().len() + 1);
                item.extend(s.items().clone());
                item.push(e.clone());

                res.push(Value::cons_list_unsanitized(item).unwrap());
            }

            Value::cons_list_unsanitized(res).unwrap()
        };

        crosscheck(&snippet, Ok(Some(expected)));
    }
}

fn extract_sequence(sequence: PropValue) -> SequenceData {
    match Value::from(sequence) {
        Value::Sequence(seq_data) => seq_data,
        _ => panic!("Should only call this function on the result of PropValue::any_sequence"),
    }
}

const FOLD_PRELUDE: &str = "
(define-private (knus (a (response int int))
                      (b (response int int)))
  (match a
    a1 (match b
         b1 (err (xor a1 b1))
         b2 (ok  (xor a1 b2)))
    a2 (match b
         b1 (ok  (xor a2 b1))
         b2 (err (xor a2 b2)))))";

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn crosscheck_fold_responses_short(
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
                let snippet = format!("{FOLD_PRELUDE} (fold knus {seq} (ok 0))");

                crosscheck_compare_only(
                    &snippet,
                );
            }
        }
    }

    #[test]
    fn crosscheck_fold_responses_long(
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
                let snippet = format!("{FOLD_PRELUDE} (fold knus {seq} (ok 0))");

                crosscheck_compare_only(
                    &snippet,
                );
            }
        }
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn crosscheck_map_ok_response(
        seq in (
            list(
                ListTypeData::new_list(
                    TypeSignature::ResponseType(Box::new((TypeSignature::UIntType, TypeSignature::NoType))),
                    10
                )
                .unwrap()
            )
        )
        .prop_filter("filter empty", |el| !el.clone().expect_list().unwrap().is_empty())
        .prop_map(PropValue::from)
    ) {
        let expected = {
            if let SequenceData::List(data) = extract_sequence(seq.clone()) {
                let v: Vec<Value> = data
                    .data
                    .iter()
                    .map(|el| el.clone().expect_result_ok().unwrap())
                    .collect();

                    Value::Sequence(
                        SequenceData::List(
                            ListData {
                                data: v.clone(),
                                type_signature: ListTypeData::new_list(TypeSignature::UIntType, v.len() as u32).unwrap()
                            }
                        )
                    )
            } else {
                panic!("Expected a list sequence");
            }
        };

        let snippet = format!(r#"
          (define-private (foo (a (response uint uint))) (unwrap! a u99))
          (map foo {seq})
        "#);

        crosscheck(
            &snippet,
            Ok(Some(expected))
        )
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn crosscheck_map_err_response(
        seq in (
            list(
                ListTypeData::new_list(
                    TypeSignature::ResponseType(Box::new((TypeSignature::NoType, TypeSignature::UIntType))),
                    10
                )
                .unwrap()
            )
        )
        .prop_filter("filter empty", |el| !el.clone().expect_list().unwrap().is_empty())
        .prop_map(PropValue::from)
    ) {
        let expected = {
            let seq_size = Value::from(seq.clone()).expect_list().unwrap().len();
            Value::Sequence(
                SequenceData::List(
                    ListData {
                        data: vec![Value::UInt(99); seq_size],
                        type_signature: ListTypeData::new_list(TypeSignature::UIntType, seq_size as u32).unwrap()
                    }
                )
            )
        };

        let snippet = format!(r#"
          (define-private (foo (a (response uint uint))) (unwrap! a u99))
          (map foo {seq})
        "#);

        crosscheck(
            &snippet,
            Ok(Some(expected))
        )
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn crosscheck_map_none_optional(
        seq in (
            list(
                ListTypeData::new_list(
                    TypeSignature::OptionalType(Box::new(TypeSignature::NoType)),
                    5
                )
                .unwrap()
            )
        )
        .prop_filter("filter empty list", |v| !v.clone().expect_list().unwrap().is_empty())
        .prop_map(PropValue::from)
    ) {
        let expected = {
            let seq_size = Value::from(seq.clone()).expect_list().unwrap().len();
            Value::Sequence(
                SequenceData::List(
                    ListData {
                        data: vec![Value::UInt(99); seq_size],
                        type_signature: ListTypeData::new_list(TypeSignature::UIntType, seq_size as u32).unwrap()
                    }
                )
            )
        };

        let snippet = format!(r#"
          (define-private (foo (a (optional uint))) (unwrap! a u99))
          (map foo {seq})
        "#);

        crosscheck(
            &snippet,
            Ok(Some(expected))
        )
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn crosscheck_map_response_buff(buf in buffer(50)) {
        let snippet = format!(r#"
        (define-private (foo (a (response (buff 50) int))) (len (unwrap! a u0)))
        (map foo (list (ok {buf})))
        "#);

        crosscheck(
            &snippet,
            Ok(Some(Value::cons_list_unsanitized(vec![Value::UInt(50)]).unwrap()))
        )
    }

    #[test]
    fn crosscheck_map_response_buff_nested(buf in buffer(50)) {
        let snippet = format!(r#"
        (define-private (foo (a (response (buff 50) int))) (len (unwrap! a u0)))
        (begin (map foo (list (ok {buf}))))
        "#);

        crosscheck(
            &snippet,
            Ok(Some(Value::cons_list_unsanitized(vec![Value::UInt(50)]).unwrap()))
        )
    }
}

//
// Proptests that should only be executed
// when running Clarity::V2 or Clarity::v3.
//
#[cfg(not(feature = "test-clarity-v1"))]
mod clarity_v2_v3 {
    use clarity::vm::types::CharType;

    use super::*;
    use crate::{runtime_config, type_string, TypePrinter};

    proptest! {
        #![proptest_config(runtime_config())]

        #[test]
        fn element_at_crosscheck((seq, idx) in (1usize..=16).prop_flat_map(|max_len| (PropValue::any_sequence(max_len), (0..max_len)))) {
            let snippet = format!("(element-at? {seq} u{idx})");

            let expected = {
                let Value::Sequence(seq_data) = seq.into() else { unreachable!() };
                seq_data.element_at(idx).expect("element_at failed").map_or_else(Value::none, |v| Value::some(v).unwrap())
            };

            crosscheck(&snippet, Ok(Some(expected)));
        }

        #[test]
        fn crosscheck_replace_at(
            (seq, source, dest) in (1usize..=20).prop_flat_map(|seq_size| {
                (PropValue::any_sequence(seq_size),
                // ranges from 0 to sequence_size - 1
                // to not occur on operations out of boundaries.
                (0usize..=seq_size - 1),
                (0usize..=seq_size - 1))
            }).no_shrink()
        ) {
            let list_ty = seq.type_string();

            let Value::Sequence(seq_data) = seq.clone().into() else { unreachable!() };

            let repl_ty = match &seq_data {
                SequenceData::Buffer(_) => "(buff 1)".to_owned(),
                SequenceData::String(CharType::ASCII(_)) => "(string-ascii 1)".to_owned(),
                SequenceData::String(CharType::UTF8(_)) => "(string-utf8 1)".to_owned(),
                SequenceData::List(ld) => type_string(ld.type_signature.get_list_item_type()),
            };

            let (expected, el) = {
                // collect an element from the sequence at 'source' position.
                let el = seq_data.clone().element_at(source).expect("element_at failed").map_or_else(Value::none, |value| value);
                // replace the element at 'dest' position
                // with the collected element from the 'source' position.
                (seq_data.replace_at(
                    &clarity::types::StacksEpochId::latest(),
                    dest,
                    el.clone()
                ).expect("replace_at failed"),
                PropValue::from(el)) // returning that to be used by the 'replace-at' Clarity function.
            };

            // Workaround needed for https://github.com/stacks-network/stacks-core/issues/4622
            let snippet = format!(r#"
            (define-private (replace-at-workaround? (seq {list_ty}) (idx uint) (repl {repl_ty}))
                (replace-at? seq idx repl)
            )
            (replace-at-workaround? {seq} u{dest} {el})
        "#);

            crosscheck(
                &snippet,
                Ok(Some(expected))
            )
        }

        #[test]
        fn slice_crosscheck_invalid_range(
            (seq, lo, hi) in (1usize..=16)
            .prop_flat_map(PropValue::any_sequence)
            .prop_ind_flat_map2(|seq| 0..extract_sequence(seq).len())
            .prop_ind_flat_map2(|(seq, lo)| lo..extract_sequence(seq).len())
            .prop_map(|((seq, lo), hi)| (seq, lo, hi))
        )
        {
            // always make sure hi is strictly larger than lo
            let snippet = format!("(slice? {seq} (+ u{hi} u1) u{lo})");
            let expected = Value::none();

            crosscheck(&snippet, Ok(Some(expected)));
        }

        #[test]
        fn slice_crosscheck_valid_range(
            (seq, lo, hi) in (1usize..=16)
            .prop_flat_map(PropValue::any_sequence)
            .prop_ind_flat_map2(|seq| 0..extract_sequence(seq).len())
            .prop_ind_flat_map2(|(seq, lo)| lo..extract_sequence(seq).len())
            .prop_map(|((seq, lo), hi)| (seq, lo, hi))
        )
        {
            let snippet = format!("(slice? {seq} u{lo} u{hi})");

            let expected =
                Value::some(
                    extract_sequence(seq)
                    .slice(&clarity::types::StacksEpochId::latest(), lo, hi)
                    .expect("Could not take a slice from sequence")
                ).unwrap();

            crosscheck(&snippet, Ok(Some(expected)));
        }
    }
}
