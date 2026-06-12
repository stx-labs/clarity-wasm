// Proptests that should only be executed
// when running Clarity::V2 or Clarity::v3.
//
#[cfg(not(feature = "test-clarity-v1"))]
mod clarity_v2_v3 {
    use clar2wasm::tools::{crosscheck, TestEnvironment};
    use clarity::vm::types::{
        BuffData, SequenceData, TupleData, TupleTypeSignature, TypeSignature,
    };
    use clarity::vm::{ClarityName, Value};
    use hex::FromHex as _;
    use prop::sample::SizeRange;
    use proptest::prelude::*;

    use crate::{prop_signature, runtime_config, type_string, PropValue, TypePrinter};

    proptest! {
        #![proptest_config(runtime_config())]

        #[test]
        fn deserialize_fixed_tuple_skip_one_after(val in PropValue::any()) {
            // A tuple { a: 42, b: <val>} where val should be added after the bytes
            let mut data = Vec::from_hex("0c000000020161000000000000000000000000000000002a0162").unwrap();

            val.0.serialize_write(&mut data).unwrap();
            let serialized = PropValue::from(Value::Sequence(SequenceData::Buffer(BuffData { data })));

            crosscheck(
                &format!("(from-consensus-buff? {{a: int}} {serialized})"),
                Ok(Some(
                    Value::some(Value::Tuple(
                        TupleData::from_data(vec![(ClarityName::from_literal("a"), Value::Int(42))]).unwrap(),
                    ))
                    .unwrap(),
                )),
            );
        }

        #[test]
        fn deserialize_fixed_tuple_skip_one_before(val in PropValue::any().no_shrink()) {
            // A tuple { a: <val>, b: 42 } where val should be added between the bytes
            let mut data = Vec::new();
            val.0.serialize_write(&mut data).unwrap();

            crosscheck(
                &format!("(from-consensus-buff? {{b: int}} 0x0c000000020161{}0162000000000000000000000000000000002a)", hex::encode(data)),
                Ok(Some(
                    Value::some(Value::Tuple(
                        TupleData::from_data(vec![(ClarityName::from_literal("b"), Value::Int(42))]).unwrap(),
                    ))
                    .unwrap(),
                )),
            );
        }

        #[test]
        fn deserialize_tuple_with_skippable_fields(
            (ty, tuple1) in tuple_and_signature("[a-z]{1,2}", 3),
            (_, tuple2) in tuple_and_signature("[a-z]{3,5}", 2..4)
        ) {
            let deserializable = tuple1.0.clone().expect_tuple().unwrap();
            let skippable = tuple2.0.expect_tuple().unwrap();

            let merged_tuple = TupleData::shallow_merge(deserializable, skippable);
            let merged_tuple = PropValue::from(Value::from(merged_tuple));

            let mut data = Vec::new();
            prop_assume!(
                merged_tuple.0.serialize_write(&mut data).is_ok(),
                "Cannot successfully serialize merged tuple",
            );

            crosscheck(
                &format!(
                    "(from-consensus-buff? {} 0x{})",
                    type_string(&ty),
                    hex::encode(data)
                ),
                Ok(Some(Value::some(tuple1.into()).unwrap())),
            );
        }
    }

    fn tuple_and_signature(
        field_names: impl Strategy<Value = String>,
        elements: impl Into<SizeRange>,
    ) -> impl Strategy<Value = (TypeSignature, PropValue)> {
        prop::collection::vec(
            (
                field_names.prop_map(|n| ClarityName::try_from(n).unwrap()),
                prop_signature(),
            ),
            elements,
        )
        .prop_filter_map("Invalid TupleTypeSignature", |v| {
            TupleTypeSignature::try_from(v)
                .ok()
                .map(TypeSignature::from)
        })
        .prop_ind_flat_map2(PropValue::from_type)
    }

    proptest! {
        #![proptest_config(runtime_config())]

        #[test]
        fn serialize_any_value(val in PropValue::any()) {
            // Convert the PropValue into a Clarity Value and attempt to serialize it.
            let ser_val = Value::from(val.clone()).serialize_to_vec();
            match ser_val {
                // If serialization succeeds, continue with the tests.
                Ok(vec_val) => {
                    let snippet = format!("(to-consensus-buff? {val})");
                    const INPUT_TYPE_ERROR: &str = "could not determine the input type for the serialization function";

                    // Check to discard test cases where `to-consensus-buff?` evaluation
                    // could not determine the type of the input parameter.
                    // For instance, `(to-consensus-buff? (list))` where a `NoType` should not be evaluated.
                    let mut env = TestEnvironment::default();
                    let check = env.evaluate(&snippet);
                    prop_assume!(match check {
                        Ok(_) => true,
                        Err(ref e) if e.to_string().contains(INPUT_TYPE_ERROR) => false,
                        _ => true
                    });

                    // Serialize the PropValue to check it against
                    // the `to-consensus-buff?` implementation.
                    let serialized_value = Value::Sequence(SequenceData::Buffer(BuffData {
                        data: vec_val
                    }));

                    let res = check.unwrap(); // Safe to unwrap because of the prop_assume!
                    let expected = if res.is_none() {
                        Ok(Some(Value::none()))
                    } else {
                        Ok(Some(Value::some(serialized_value.clone()).unwrap()))
                    };

                    // Crosscheck serialization
                    crosscheck(&snippet, expected);
                },
                // If the value cannot be serialized, skip the test.
                Err(_) => prop_assume!(false),
            }
        }

        #[test]
        fn deserialize_any_value(val in PropValue::any()) {
            // Convert the PropValue into a Clarity Value and attempt to serialize it.
            let ser_val = Value::from(val.clone()).serialize_to_vec();
            match ser_val {
                // If serialization succeeds, continue with the test by verifying deserialization.
                Ok(vec_val) => {
                    let serialized_value = Value::Sequence(SequenceData::Buffer(BuffData {
                        data: vec_val
                    }));

                    // Expression that attempts to deserialize the buffer.
                    // The expected outcome is that the deserialized value matches the original value.
                    let snippet = format!(
                        "(from-consensus-buff? {} {})",
                        val.type_string(),
                        serialized_value
                    );

                    crosscheck(
                        &snippet,
                        Ok(Some(Value::some(Value::from(val)).unwrap()))
                    );
                },
                // If the value cannot be serialized, skip the test.
                Err(_) => prop_assume!(false),
            }
        }
    }
}
