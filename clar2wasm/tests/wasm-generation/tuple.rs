use clar2wasm::tools::crosscheck;
use clarity::vm::types::{SequenceSubtype, StringSubtype, TupleData, TypeSignature};
use clarity::vm::Value;
use clarity_types::ClarityName;
use proptest::prelude::prop;
use proptest::strategy::{Just, Strategy};
use proptest::{prop_oneof, proptest};

use crate::{tuple, PropValue};

fn strategies_base() -> impl Strategy<Value = TypeSignature> {
    prop_oneof![
        Just(TypeSignature::IntType),
        Just(TypeSignature::UIntType),
        Just(TypeSignature::BoolType),
        (0u32..128).prop_map(|s| TypeSignature::SequenceType(SequenceSubtype::BufferType(
            s.try_into().unwrap()
        ))),
        (0u32..128).prop_map(|s| TypeSignature::SequenceType(SequenceSubtype::StringType(
            StringSubtype::ASCII(s.try_into().unwrap())
        )))
    ]
}

fn tuple_gen() -> impl Strategy<Value = Value> {
    let coll = prop::collection::btree_map(
        r#"[a-zA-Z]{1,16}"#.prop_map(|name| name.try_into().unwrap()),
        strategies_base(),
        1..8,
    )
    .prop_map(|btree| btree.try_into().unwrap());

    coll.prop_flat_map(tuple)
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn crosscheck_merge(t1 in tuple_gen(), t2 in tuple_gen()) {

        let expected = clarity::vm::functions::tuples::tuple_merge(t1.clone(), t2.clone()).unwrap();

        crosscheck(
            &format!("(merge {} {})", PropValue(t1), PropValue(t2)),
            Ok(Some(expected))
        )
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn crosscheck_get(t in tuple_gen(), v in strategies_base().prop_flat_map(PropValue::from_type)) {
        let merged = clarity::vm::functions::tuples::tuple_merge(
            t.clone(),
            Value::Tuple(
                TupleData::from_data(vec![(ClarityName::from_literal("new"), v.clone().into())]).unwrap()
            ))
            .unwrap();

        crosscheck(
            &format!("(get new {})", PropValue(merged)),
            Ok(Some(v.into()))
        )
    }
}
