use clar2wasm::tools::crosscheck;
use clarity_types::types::{CharType, SequenceData, SequenceSubtype, StringSubtype, TypeSignature};
use clarity_types::Value;
use proptest::prelude::*;

use crate::PropValue;

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn to_ascii_int(i in PropValue::from_type(TypeSignature::IntType)) {
        crosscheck(
            &format!("(to-ascii? {i})"),
            Ok(Some(
                Value::okay(Value::string_ascii_from_bytes(i.to_string().into_bytes()).unwrap())
                    .unwrap(),
            )),
        )
    }

    #[test]
    fn to_ascii_uint(u in PropValue::from_type(TypeSignature::UIntType)) {
        crosscheck(
            &format!("(to-ascii? {u})"),
            Ok(Some(
                Value::okay(Value::string_ascii_from_bytes(u.to_string().into_bytes()).unwrap())
                    .unwrap(),
            )),
        )
    }

    #[test]
    fn to_ascii_principal(p in PropValue::from_type(TypeSignature::PrincipalType)) {
        crosscheck(
            &format!("(to-ascii? {p})"),
            Ok(Some(
                Value::okay(Value::string_ascii_from_bytes(p.inner().to_string().into_bytes()).unwrap())
                    .unwrap()
            )),
        );
    }

    #[test]
    fn to_ascii_buffer(
        b in (0..=1000u32).prop_flat_map(|i| {
            PropValue::from_type(TypeSignature::SequenceType(SequenceSubtype::BufferType(
                i.try_into().unwrap(),
            )))
        })) {
            crosscheck(
                &format!("(to-ascii? {b})"),
                Ok(Some(
                    Value::okay(Value::string_ascii_from_bytes(b.to_string().into_bytes()).unwrap())
                        .unwrap(),
            )),
        );
    }

    #[test]
    fn to_ascii_string_utf8_valid(
        s in (0..=1000u32).prop_flat_map(|i| {
            PropValue::from_type(TypeSignature::SequenceType(SequenceSubtype::StringType(
                StringSubtype::UTF8(i.try_into().unwrap()),
            )))
        })) {
            let expected = {
                let Value::Sequence(SequenceData::String(CharType::UTF8(bytes))) = s.inner() else {
                    unreachable!()
                };
                let all_ascii = bytes
                    .data
                    .iter()
                    .all(|b| b.len() == 1 && (0x20u8..0x7e).contains(&b[0]));
                if all_ascii {
                    Value::okay(
                        Value::string_ascii_from_bytes(bytes.data.iter().flatten().copied().collect())
                            .unwrap(),
                    )
                    .unwrap()
                } else {
                    Value::err_uint(1)
                }
            };
            crosscheck(&format!("(to-ascii? {s})"), Ok(Some(expected)));
    }

    #[test]
    fn to_ascii_string_utf8(
        s in (0..=1000u32).prop_flat_map(|i| {
            PropValue::from_type(TypeSignature::SequenceType(SequenceSubtype::StringType(
                StringSubtype::UTF8(i.try_into().unwrap()),
            )))
        })) {
            let expected = {
                let Value::Sequence(SequenceData::String(CharType::UTF8(bytes))) = s.inner() else {
                    unreachable!()
                };
                let all_valid_ascii = bytes
                    .data
                    .iter()
                    .all(|b| b.len() == 1 && (0x20u8..0x7e).contains(&b[0]));
                if all_valid_ascii {
                    Value::okay(
                        Value::string_ascii_from_bytes(bytes.data.iter().flatten().copied().collect())
                            .unwrap(),
                    )
                    .unwrap()
                } else {
                    Value::err_uint(1)
                }
            };
            crosscheck(&format!("(to-ascii? {s})"), Ok(Some(expected)));
    }
}
