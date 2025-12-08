#![cfg(test)]
pub mod unit_tests;

use clarity::vm::types::{ListTypeData, TypeSignature};

pub(crate) fn list_of(elem: TypeSignature, max_len: u32) -> TypeSignature {
    TypeSignature::SequenceType(clarity::vm::types::SequenceSubtype::ListType(
        ListTypeData::new_list(elem, max_len).unwrap(),
    ))
}
