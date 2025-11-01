#![allow(non_camel_case_types)]

use clarity::vm::analysis::CheckErrors;
use clarity::vm::ast::build_ast;
use clarity::vm::contexts::GlobalContext;
use clarity::vm::errors::{Error, WasmError};
use clarity::vm::types::signatures::CallableSubtype;
use clarity::vm::types::{
    ASCIIData, BuffData, BufferLength, CallableData, CharType, ListData, OptionalData,
    PrincipalData, QualifiedContractIdentifier, ResponseData, SequenceData, SequenceSubtype,
    SequencedValue, StandardPrincipalData, StringSubtype, TraitIdentifier, TupleData,
    TypeSignature, TypeSignatureExt,
};
use clarity::vm::{CallStack, ClarityName, ClarityVersion, ContractContext, ContractName, Value};
use stacks_common::types::StacksEpochId;
use walrus::{GlobalId, InstrSeqBuilder};
use wasmtime::{AsContextMut, Linker, Memory, Module, Store, Val, ValType};

use crate::error_mapping::{self, ErrorMap};
use crate::initialize::ClarityWasmContext;
use crate::linker::link_host_functions;
use crate::wasm_generator::{GeneratorError, WasmGenerator};
use crate::CostLinker;

#[allow(non_snake_case)]
pub enum MintAssetErrorCodes {
    ALREADY_EXIST = 1,
}

pub enum MintTokenErrorCodes {
    NON_POSITIVE_AMOUNT = 1,
}

#[allow(non_snake_case)]
pub enum TransferAssetErrorCodes {
    NOT_OWNED_BY = 1,
    SENDER_IS_RECIPIENT = 2,
    DOES_NOT_EXIST = 3,
}

#[allow(non_snake_case)]
pub enum TransferTokenErrorCodes {
    NOT_ENOUGH_BALANCE = 1,
    SENDER_IS_RECIPIENT = 2,
    NON_POSITIVE_AMOUNT = 3,
}

#[allow(non_snake_case)]
pub enum BurnAssetErrorCodes {
    NOT_OWNED_BY = 1,
    DOES_NOT_EXIST = 3,
}

#[allow(non_snake_case)]
pub enum BurnTokenErrorCodes {
    NOT_ENOUGH_BALANCE_OR_NON_POSITIVE = 1,
}

pub enum StxErrorCodes {
    NOT_ENOUGH_BALANCE = 1,
    SENDER_IS_RECIPIENT = 2,
    NON_POSITIVE_AMOUNT = 3,
    SENDER_IS_NOT_TX_SENDER = 4,
}

// Bytes for principal version
pub const PRINCIPAL_VERSION_BYTES: usize = 1;
// Number of bytes in principal hash
pub const PRINCIPAL_HASH_BYTES: usize = 20;
// Standard principal version + hash
pub const PRINCIPAL_BYTES: usize = PRINCIPAL_VERSION_BYTES + PRINCIPAL_HASH_BYTES;
// Number of bytes used to store the length of the contract name
pub const CONTRACT_NAME_LENGTH_BYTES: usize = 1;
// 1 byte for version, 20 bytes for hash, 4 bytes for contract name length (0)
pub const STANDARD_PRINCIPAL_BYTES: usize = PRINCIPAL_BYTES + CONTRACT_NAME_LENGTH_BYTES;
// Max length of a contract name
pub const CONTRACT_NAME_MAX_LENGTH: usize = 128;
// Standard principal, but at most 128 character function name
pub const PRINCIPAL_BYTES_MAX: usize = STANDARD_PRINCIPAL_BYTES + CONTRACT_NAME_MAX_LENGTH;

/// Convert a Wasm value into a Clarity `Value`. Depending on the type, the
/// values may be directly passed in the Wasm `Val`s or may be read from the
/// Wasm memory, via an offset and size.
/// - `type_sig` is the Clarity type of the value.
/// - `value_index` is the index of the value in the array of Wasm `Val`s.
/// - `buffer` is the array of Wasm `Val`s.
/// - `memory` is the Wasm memory.
/// - `store` is the Wasm store.
///
/// Returns the Clarity `Value` and the number of Wasm `Val`s that were used.
pub fn wasm_to_clarity_value(
    type_sig: &TypeSignature,
    value_index: usize,
    buffer: &[Val],
    memory: Memory,
    store: &mut impl AsContextMut,
    epoch: StacksEpochId,
) -> Result<(Option<Value>, usize), Error> {
    match type_sig {
        TypeSignature::IntType => {
            let lower = buffer[value_index]
                .i64()
                .ok_or(Error::Wasm(WasmError::ValueTypeMismatch))?;
            let upper = buffer[value_index + 1]
                .i64()
                .ok_or(Error::Wasm(WasmError::ValueTypeMismatch))?;
            Ok((
                Some(Value::Int(((upper as i128) << 64) | (lower as u64) as i128)),
                2,
            ))
        }
        TypeSignature::UIntType => {
            let lower = buffer[value_index]
                .i64()
                .ok_or(Error::Wasm(WasmError::ValueTypeMismatch))?;
            let upper = buffer[value_index + 1]
                .i64()
                .ok_or(Error::Wasm(WasmError::ValueTypeMismatch))?;
            Ok((
                Some(Value::UInt(
                    ((upper as u128) << 64) | (lower as u64) as u128,
                )),
                2,
            ))
        }
        TypeSignature::BoolType => Ok((
            Some(Value::Bool(
                buffer[value_index]
                    .i32()
                    .ok_or(Error::Wasm(WasmError::ValueTypeMismatch))?
                    != 0,
            )),
            1,
        )),
        TypeSignature::OptionalType(optional) => {
            let value_types = clar2wasm_ty(optional);
            Ok((
                if buffer[value_index]
                    .i32()
                    .ok_or(Error::Wasm(WasmError::ValueTypeMismatch))?
                    == 1
                {
                    let (value, _) = wasm_to_clarity_value(
                        optional,
                        value_index + 1,
                        buffer,
                        memory,
                        store,
                        epoch,
                    )?;
                    Some(Value::some(value.ok_or(Error::Unchecked(
                        CheckErrors::CouldNotDetermineType,
                    ))?)?)
                } else {
                    Some(Value::none())
                },
                1 + value_types.len(),
            ))
        }
        TypeSignature::ResponseType(response) => {
            let ok_types = clar2wasm_ty(&response.0);
            let err_types = clar2wasm_ty(&response.1);

            Ok((
                if buffer[value_index]
                    .i32()
                    .ok_or(Error::Wasm(WasmError::ValueTypeMismatch))?
                    == 1
                {
                    let (ok, _) = wasm_to_clarity_value(
                        &response.0,
                        value_index + 1,
                        buffer,
                        memory,
                        store,
                        epoch,
                    )?;
                    Some(Value::okay(ok.ok_or(Error::Unchecked(
                        CheckErrors::CouldNotDetermineResponseOkType,
                    ))?)?)
                } else {
                    let (err, _) = wasm_to_clarity_value(
                        &response.1,
                        value_index + 1 + ok_types.len(),
                        buffer,
                        memory,
                        store,
                        epoch,
                    )?;
                    Some(Value::error(err.ok_or(Error::Unchecked(
                        CheckErrors::CouldNotDetermineResponseErrType,
                    ))?)?)
                },
                1 + ok_types.len() + err_types.len(),
            ))
        }
        TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(_))) => {
            let offset = buffer[value_index]
                .i32()
                .ok_or(Error::Wasm(WasmError::ValueTypeMismatch))?;
            let length = buffer[value_index + 1]
                .i32()
                .ok_or(Error::Wasm(WasmError::ValueTypeMismatch))?;
            let mut string_buffer: Vec<u8> = vec![0; length as usize];
            memory
                .read(store, offset as usize, &mut string_buffer)
                .map_err(|e| Error::Wasm(WasmError::UnableToReadMemory(e.into())))?;
            Ok((Some(Value::string_ascii_from_bytes(string_buffer)?), 2))
        }
        // A `NoType` will be a dummy value that should not be used.
        TypeSignature::NoType => Ok((None, 1)),
        TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(_))) => {
            let offset = buffer[value_index]
                .i32()
                .ok_or(Error::Wasm(WasmError::ValueTypeMismatch))?;
            let length = buffer[value_index + 1]
                .i32()
                .ok_or(Error::Wasm(WasmError::ValueTypeMismatch))?;
            let mut string_buffer: Vec<u8> = vec![0; length as usize];
            memory
                .read(store, offset as usize, &mut string_buffer)
                .map_err(|e| Error::Wasm(WasmError::UnableToReadMemory(e.into())))?;
            Ok((
                Some(Value::string_utf8_from_unicode_scalars(string_buffer)?),
                2,
            ))
        }
        TypeSignature::SequenceType(SequenceSubtype::BufferType(_buffer_length)) => {
            let offset = buffer[value_index]
                .i32()
                .ok_or(Error::Wasm(WasmError::ValueTypeMismatch))?;
            let length = buffer[value_index + 1]
                .i32()
                .ok_or(Error::Wasm(WasmError::ValueTypeMismatch))?;
            let mut buff: Vec<u8> = vec![0; length as usize];
            memory
                .read(store, offset as usize, &mut buff)
                .map_err(|e| Error::Wasm(WasmError::UnableToReadMemory(e.into())))?;
            Ok((Some(Value::buff_from(buff)?), 2))
        }
        TypeSignature::SequenceType(SequenceSubtype::ListType(_)) => {
            let offset = buffer[value_index]
                .i32()
                .ok_or(Error::Wasm(WasmError::ValueTypeMismatch))?;
            let length = buffer[value_index + 1]
                .i32()
                .ok_or(Error::Wasm(WasmError::ValueTypeMismatch))?;

            let value = read_from_wasm(memory, store, type_sig, offset, length, epoch)?;
            Ok((Some(value), 2))
        }
        TypeSignature::PrincipalType
        | TypeSignature::CallableType(_)
        | TypeSignature::TraitReferenceType(_) => {
            let offset = buffer[value_index]
                .i32()
                .ok_or(Error::Wasm(WasmError::ValueTypeMismatch))?;
            let mut principal_bytes: [u8; 1 + PRINCIPAL_HASH_BYTES] = [0; 1 + PRINCIPAL_HASH_BYTES];
            memory
                .read(
                    store.as_context_mut(),
                    offset as usize,
                    &mut principal_bytes,
                )
                .map_err(|e| Error::Wasm(WasmError::UnableToReadMemory(e.into())))?;
            let mut buffer: [u8; CONTRACT_NAME_LENGTH_BYTES] = [0; CONTRACT_NAME_LENGTH_BYTES];
            memory
                .read(store.as_context_mut(), offset as usize + 21, &mut buffer)
                .map_err(|e| Error::Wasm(WasmError::UnableToReadMemory(e.into())))?;
            let standard = StandardPrincipalData::new(
                principal_bytes[0],
                principal_bytes[1..].try_into().map_err(|_| {
                    Error::Wasm(WasmError::WasmGeneratorError(
                        "Could not decode principal".into(),
                    ))
                })?,
            )?;
            let contract_name_length = buffer[0] as usize;
            if contract_name_length == 0 {
                Ok((Some(Value::Principal(PrincipalData::Standard(standard))), 2))
            } else {
                let mut contract_name: Vec<u8> = vec![0; contract_name_length];
                memory
                    .read(
                        store,
                        (offset + STANDARD_PRINCIPAL_BYTES as i32) as usize,
                        &mut contract_name,
                    )
                    .map_err(|e| Error::Wasm(WasmError::UnableToReadMemory(e.into())))?;
                let qualified_id = QualifiedContractIdentifier {
                    issuer: standard,
                    name: ContractName::try_from(
                        String::from_utf8(contract_name)
                            .map_err(|e| Error::Wasm(WasmError::UnableToReadIdentifier(e)))?,
                    )?,
                };
                Ok((
                    Some(
                        if let TypeSignature::CallableType(CallableSubtype::Trait(
                            trait_identifier,
                        )) = type_sig
                        {
                            Value::CallableContract(CallableData {
                                contract_identifier: qualified_id,
                                trait_identifier: Some(trait_identifier.clone()),
                            })
                        } else {
                            Value::Principal(PrincipalData::Contract(qualified_id))
                        },
                    ),
                    2,
                ))
            }
        }
        TypeSignature::TupleType(t) => {
            let mut index = value_index;
            let mut data_map = Vec::new();
            for (name, ty) in t.get_type_map() {
                let (value, increment) =
                    wasm_to_clarity_value(ty, index, buffer, memory, store, epoch)?;
                data_map.push((
                    name.clone(),
                    value.ok_or_else(|| {
                        Error::Unchecked(CheckErrors::BadTupleConstruction(format!(
                            "Failed to convert Wasm value into Clarity value for field `{}`",
                            name
                        )))
                    })?,
                ));
                index += increment;
            }
            let tuple = TupleData::from_data(data_map)?;
            Ok((Some(tuple.into()), index - value_index))
        }
        TypeSignature::ListUnionType(_subtypes) => {
            Err(Error::Wasm(WasmError::InvalidListUnionTypeInValue))
        }
    }
}

/// Read a value from the Wasm memory at `offset` with `length` given the
/// provided Clarity `TypeSignature`.
///
/// In-memory values require one extra level
/// of indirection, so this function will read the offset and length from the
/// memory, then read the actual value.
pub fn read_from_wasm_indirect(
    memory: Memory,
    store: &mut impl AsContextMut,
    ty: &TypeSignature,
    mut offset: i32,
    epoch: StacksEpochId,
) -> Result<Value, Error> {
    let mut length = get_type_size(ty);

    // For in-memory types, first read the offset and length from the memory,
    // then read the actual value.
    if is_in_memory_type(ty) {
        (offset, length) = read_indirect_offset_and_length(memory, store, offset)?;
    };

    read_from_wasm(memory, store, ty, offset, length, epoch)
}

/// Read a value from the Wasm memory at `offset` with `length`, given the
/// provided Clarity `TypeSignature`.
pub fn read_from_wasm(
    memory: Memory,
    store: &mut impl AsContextMut,
    ty: &TypeSignature,
    offset: i32,
    length: i32,
    epoch: StacksEpochId,
) -> Result<Value, Error> {
    match ty {
        TypeSignature::UIntType => {
            debug_assert!(
                length == 16,
                "expected uint length to be 16 bytes, found {length}"
            );
            let mut buffer: [u8; 8] = [0; 8];
            memory
                .read(store.as_context_mut(), offset as usize, &mut buffer)
                .map_err(|e| Error::Wasm(WasmError::Runtime(e.into())))?;
            let low = u64::from_le_bytes(buffer) as u128;
            memory
                .read(store, (offset + 8) as usize, &mut buffer)
                .map_err(|e| Error::Wasm(WasmError::Runtime(e.into())))?;
            let high = u64::from_le_bytes(buffer) as u128;
            Ok(Value::UInt((high << 64) | low))
        }
        TypeSignature::IntType => {
            debug_assert!(
                length == 16,
                "expected int length to be 16 bytes, found {length}"
            );
            let mut buffer: [u8; 8] = [0; 8];
            memory
                .read(store.as_context_mut(), offset as usize, &mut buffer)
                .map_err(|e| Error::Wasm(WasmError::Runtime(e.into())))?;
            let low = u64::from_le_bytes(buffer) as u128;
            memory
                .read(store, (offset + 8) as usize, &mut buffer)
                .map_err(|e| Error::Wasm(WasmError::Runtime(e.into())))?;
            let high = u64::from_le_bytes(buffer) as u128;
            Ok(Value::Int(((high << 64) | low) as i128))
        }
        TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(
            type_length,
        ))) => {
            debug_assert!(
                type_length >= &BufferLength::try_from(length as u32)?,
                "expected string length to be less than the type length"
            );
            let mut buffer: Vec<u8> = vec![0; length as usize];
            memory
                .read(store, offset as usize, &mut buffer)
                .map_err(|e| Error::Wasm(WasmError::Runtime(e.into())))?;
            Value::string_ascii_from_bytes(buffer)
        }
        TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(_s))) => {
            let mut buffer: Vec<u8> = vec![0; length as usize];
            memory
                .read(store, offset as usize, &mut buffer)
                .map_err(|e| Error::Wasm(WasmError::Runtime(e.into())))?;
            Value::string_utf8_from_unicode_scalars(buffer)
        }
        TypeSignature::PrincipalType
        | TypeSignature::CallableType(_)
        | TypeSignature::TraitReferenceType(_) => {
            debug_assert!(
                length >= STANDARD_PRINCIPAL_BYTES as i32 && length <= PRINCIPAL_BYTES_MAX as i32
            );
            let mut current_offset = offset as usize;
            let mut version: [u8; PRINCIPAL_VERSION_BYTES] = [0; PRINCIPAL_VERSION_BYTES];
            let mut hash: [u8; PRINCIPAL_HASH_BYTES] = [0; PRINCIPAL_HASH_BYTES];
            memory
                .read(store.as_context_mut(), current_offset, &mut version)
                .map_err(|e| Error::Wasm(WasmError::Runtime(e.into())))?;
            current_offset += PRINCIPAL_VERSION_BYTES;
            memory
                .read(store.as_context_mut(), current_offset, &mut hash)
                .map_err(|e| Error::Wasm(WasmError::Runtime(e.into())))?;
            current_offset += PRINCIPAL_HASH_BYTES;
            let principal = StandardPrincipalData::new(version[0], hash)?;
            let mut contract_length_buf: [u8; CONTRACT_NAME_LENGTH_BYTES] =
                [0; CONTRACT_NAME_LENGTH_BYTES];
            memory
                .read(
                    store.as_context_mut(),
                    current_offset,
                    &mut contract_length_buf,
                )
                .map_err(|e| Error::Wasm(WasmError::Runtime(e.into())))?;
            current_offset += CONTRACT_NAME_LENGTH_BYTES;
            let contract_length = contract_length_buf[0];
            if contract_length == 0 {
                Ok(Value::Principal(principal.into()))
            } else {
                let mut contract_name: Vec<u8> = vec![0; contract_length as usize];
                memory
                    .read(store, current_offset, &mut contract_name)
                    .map_err(|e| Error::Wasm(WasmError::Runtime(e.into())))?;
                let contract_name = String::from_utf8(contract_name)
                    .map_err(|e| Error::Wasm(WasmError::Runtime(e.into())))?;
                let qualified_id = QualifiedContractIdentifier {
                    issuer: principal,
                    name: ContractName::try_from(contract_name)?,
                };
                Ok(
                    if let TypeSignature::CallableType(CallableSubtype::Trait(trait_identifier)) =
                        ty
                    {
                        Value::CallableContract(CallableData {
                            contract_identifier: qualified_id,
                            trait_identifier: Some(trait_identifier.clone()),
                        })
                    } else {
                        Value::Principal(PrincipalData::Contract(qualified_id))
                    },
                )
            }
        }
        TypeSignature::SequenceType(SequenceSubtype::BufferType(_b)) => {
            let mut buffer: Vec<u8> = vec![0; length as usize];
            memory
                .read(store, offset as usize, &mut buffer)
                .map_err(|e| Error::Wasm(WasmError::Runtime(e.into())))?;
            Value::buff_from(buffer)
        }
        TypeSignature::SequenceType(SequenceSubtype::ListType(list)) => {
            let elem_ty = list.get_list_item_type();
            let elem_length = get_type_size(elem_ty);
            let end = offset + length;
            let mut buffer: Vec<Value> = Vec::new();
            let mut current_offset = offset;
            while current_offset < end {
                let elem = read_from_wasm_indirect(memory, store, elem_ty, current_offset, epoch)?;
                buffer.push(elem);
                current_offset += elem_length;
            }
            Value::cons_list_unsanitized(buffer)
        }
        TypeSignature::BoolType => {
            debug_assert!(
                length == 4,
                "expected bool length to be 4 bytes, found {length}"
            );
            let mut buffer: [u8; 4] = [0; 4];
            memory
                .read(store.as_context_mut(), offset as usize, &mut buffer)
                .map_err(|e| Error::Wasm(WasmError::Runtime(e.into())))?;
            let bool_val = u32::from_le_bytes(buffer);
            Ok(Value::Bool(bool_val != 0))
        }
        TypeSignature::TupleType(type_sig) => {
            let mut data = Vec::new();
            let mut current_offset = offset;
            for (field_key, field_ty) in type_sig.get_type_map() {
                let field_length = get_type_size(field_ty);
                let field_value =
                    read_from_wasm_indirect(memory, store, field_ty, current_offset, epoch)?;
                data.push((field_key.clone(), field_value));
                current_offset += field_length;
            }
            Ok(Value::Tuple(TupleData::from_data(data)?))
        }
        TypeSignature::ResponseType(response_type) => {
            let mut current_offset = offset;

            // Read the indicator
            let mut indicator_bytes = [0u8; 4];
            memory
                .read(
                    store.as_context_mut(),
                    current_offset as usize,
                    &mut indicator_bytes,
                )
                .map_err(|e| Error::Wasm(WasmError::Runtime(e.into())))?;
            current_offset += 4;
            let indicator = i32::from_le_bytes(indicator_bytes);

            // Read the ok or err value, depending on the indicator
            match indicator {
                0 => {
                    current_offset += get_type_size(&response_type.0);
                    let err_value = read_from_wasm_indirect(
                        memory,
                        store,
                        &response_type.1,
                        current_offset,
                        epoch,
                    )?;
                    Value::error(err_value).map_err(|_| Error::Wasm(WasmError::ValueTypeMismatch))
                }
                1 => {
                    let ok_value = read_from_wasm_indirect(
                        memory,
                        store,
                        &response_type.0,
                        current_offset,
                        epoch,
                    )?;
                    Value::okay(ok_value).map_err(|_| Error::Wasm(WasmError::ValueTypeMismatch))
                }
                _ => Err(Error::Wasm(WasmError::InvalidIndicator(indicator))),
            }
        }
        TypeSignature::OptionalType(type_sig) => {
            let mut current_offset = offset;

            // Read the indicator
            let mut indicator_bytes = [0u8; 4];
            memory
                .read(
                    store.as_context_mut(),
                    current_offset as usize,
                    &mut indicator_bytes,
                )
                .map_err(|e| Error::Wasm(WasmError::Runtime(e.into())))?;
            current_offset += 4;
            let indicator = i32::from_le_bytes(indicator_bytes);

            match indicator {
                0 => Ok(Value::none()),
                1 => {
                    let value =
                        read_from_wasm_indirect(memory, store, type_sig, current_offset, epoch)?;
                    Ok(
                        Value::some(value)
                            .map_err(|_| Error::Wasm(WasmError::ValueTypeMismatch))?,
                    )
                }
                _ => Err(Error::Wasm(WasmError::InvalidIndicator(indicator))),
            }
        }
        TypeSignature::NoType => Err(Error::Wasm(WasmError::InvalidNoTypeInValue)),
        TypeSignature::ListUnionType(_subtypes) => {
            Err(Error::Wasm(WasmError::InvalidListUnionTypeInValue))
        }
    }
}

pub fn read_indirect_offset_and_length(
    memory: Memory,
    store: &mut impl AsContextMut,
    offset: i32,
) -> Result<(i32, i32), Error> {
    let mut buffer: [u8; 4] = [0; 4];
    memory
        .read(store.as_context_mut(), offset as usize, &mut buffer)
        .map_err(|e| Error::Wasm(WasmError::Runtime(e.into())))?;
    let indirect_offset = i32::from_le_bytes(buffer);
    memory
        .read(store.as_context_mut(), (offset + 4) as usize, &mut buffer)
        .map_err(|e| Error::Wasm(WasmError::Runtime(e.into())))?;
    let length = i32::from_le_bytes(buffer);
    Ok((indirect_offset, length))
}

/// Return the number of bytes required to representation of a value of the
/// type `ty`.
///
/// For in-memory types, this is just the size of the offset and
/// length. For non-in-memory types, this is the size of the value itself.
pub fn get_type_size(ty: &TypeSignature) -> i32 {
    match ty {
        TypeSignature::IntType | TypeSignature::UIntType => 16, // low: i64, high: i64
        TypeSignature::BoolType => 4,                           // i32
        TypeSignature::PrincipalType
        | TypeSignature::SequenceType(_)
        | TypeSignature::CallableType(_)
        | TypeSignature::TraitReferenceType(_) => 8, // offset: i32, length: i32
        TypeSignature::OptionalType(inner) => 4 + get_type_size(inner), // indicator: i32, value: inner
        TypeSignature::TupleType(tuple_ty) => {
            let mut size = 0;
            for inner_type in tuple_ty.get_type_map().values() {
                size += get_type_size(inner_type);
            }
            size
        }
        TypeSignature::ResponseType(inner_types) => {
            // indicator: i32, ok_val: inner_types.0, err_val: inner_types.1
            4 + get_type_size(&inner_types.0) + get_type_size(&inner_types.1)
        }
        TypeSignature::NoType => 4, // i32
        TypeSignature::ListUnionType(_) => {
            unreachable!("not a value type")
        }
    }
}

/// Return the number of bytes required to store a value of the type `ty`.
pub fn get_type_in_memory_size(ty: &TypeSignature, include_repr: bool) -> i32 {
    match ty {
        TypeSignature::IntType | TypeSignature::UIntType => 16, // i64_low + i64_high
        TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(length))) => {
            let mut size = u32::from(length) as i32;
            if include_repr {
                size += 8; // offset + length
            }
            size
        }
        TypeSignature::PrincipalType
        | TypeSignature::CallableType(_)
        | TypeSignature::TraitReferenceType(_) => {
            // Standard principal is a 1 byte version and a 20 byte Hash160.
            // Then there is an int32 for the contract name length, followed by
            // the contract name, which has a max length of 128.
            let mut size = PRINCIPAL_BYTES_MAX as i32;
            if include_repr {
                size += 8; // offset + length
            }
            size
        }
        TypeSignature::OptionalType(inner) => 4 + get_type_in_memory_size(inner, include_repr),
        TypeSignature::SequenceType(SequenceSubtype::ListType(list_data)) => {
            if include_repr {
                8 // offset + length
                 + list_data.get_max_len() as i32
                    * get_type_in_memory_size(list_data.get_list_item_type(), true)
            } else {
                list_data.get_max_len() as i32 * get_type_size(list_data.get_list_item_type())
            }
        }
        TypeSignature::SequenceType(SequenceSubtype::BufferType(length)) => {
            let mut size = u32::from(length) as i32;
            if include_repr {
                size += 8; // offset + length
            }
            size
        }
        TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(length))) => {
            let mut size = u32::from(length) as i32 * 4;
            if include_repr {
                size += 8; // offset + length
            }
            size
        }
        TypeSignature::NoType => 4,   // i32
        TypeSignature::BoolType => 4, // i32
        TypeSignature::TupleType(tuple_ty) => {
            let mut size = 0;
            for inner_type in tuple_ty.get_type_map().values() {
                size += get_type_in_memory_size(inner_type, include_repr);
            }
            size
        }
        TypeSignature::ResponseType(res_types) => {
            // indicator: i32, ok_val: inner_types.0, err_val: inner_types.1
            4 + get_type_in_memory_size(&res_types.0, include_repr)
                + get_type_in_memory_size(&res_types.1, include_repr)
        }
        TypeSignature::ListUnionType(_) => unreachable!("not a value type"),
    }
}

/// Push a placeholder value for Wasm type `ty` onto the data stack.
pub fn placeholder_for_type(ty: ValType) -> Val {
    match ty {
        ValType::I32 => Val::I32(0),
        ValType::I64 => Val::I64(0),
        ValType::F32 => Val::F32(0),
        ValType::F64 => Val::F64(0),
        ValType::V128 => Val::V128(0.into()),
        ValType::ExternRef => Val::ExternRef(None),
        ValType::FuncRef => Val::FuncRef(None),
    }
}

/// Write a value to the Wasm memory at `offset` given the provided Clarity
/// `TypeSignature`.
///
/// If the value is an in-memory type, then it will be written
/// to the memory at `in_mem_offset`, and if `include_repr` is true, the offset
/// and length of the value will be written to the memory at `offset`.
/// Returns the number of bytes written at `offset` and at `in_mem_offset`.
pub fn write_to_wasm(
    mut store: impl AsContextMut,
    memory: Memory,
    ty: &TypeSignature,
    offset: i32,
    in_mem_offset: i32,
    value: &Value,
    include_repr: bool,
) -> Result<(i32, i32), Error> {
    match ty {
        TypeSignature::IntType => {
            let mut buffer: [u8; 8] = [0; 8];
            let i = value_as_i128(value)?;
            let high = (i >> 64) as u64;
            let low = (i & 0xffff_ffff_ffff_ffff) as u64;
            buffer.copy_from_slice(&low.to_le_bytes());
            memory
                .write(&mut store, offset as usize, &buffer)
                .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
            buffer.copy_from_slice(&high.to_le_bytes());
            memory
                .write(&mut store, (offset + 8) as usize, &buffer)
                .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
            Ok((16, 0))
        }
        TypeSignature::UIntType => {
            let mut buffer: [u8; 8] = [0; 8];
            let i = value_as_u128(value)?;
            let high = (i >> 64) as u64;
            let low = (i & 0xffff_ffff_ffff_ffff) as u64;
            buffer.copy_from_slice(&low.to_le_bytes());
            memory
                .write(&mut store, offset as usize, &buffer)
                .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
            buffer.copy_from_slice(&high.to_le_bytes());
            memory
                .write(&mut store, (offset + 8) as usize, &buffer)
                .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
            Ok((16, 0))
        }
        TypeSignature::SequenceType(SequenceSubtype::BufferType(_length)) => {
            let buffdata = value_as_buffer(value.clone())?;
            let mut written = 0;
            let mut in_mem_written = 0;

            // Write the value to `in_mem_offset`
            memory
                .write(
                    &mut store,
                    (in_mem_offset + in_mem_written) as usize,
                    &buffdata.data,
                )
                .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
            in_mem_written += buffdata.data.len() as i32;

            if include_repr {
                // Write the representation (offset and length) of the value to
                // `offset`.
                let offset_buffer = in_mem_offset.to_le_bytes();
                memory
                    .write(&mut store, (offset) as usize, &offset_buffer)
                    .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
                written += 4;
                let len_buffer = in_mem_written.to_le_bytes();
                memory
                    .write(&mut store, (offset + written) as usize, &len_buffer)
                    .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
                written += 4;
            }

            Ok((written, in_mem_written))
        }
        TypeSignature::SequenceType(SequenceSubtype::StringType(string_subtype)) => {
            let string = match string_subtype {
                StringSubtype::ASCII(_length) => value_as_string_ascii(value.clone())?.data,
                StringSubtype::UTF8(_length) => {
                    let Value::Sequence(SequenceData::String(CharType::UTF8(utf8_data))) = value
                    else {
                        unreachable!("A string-utf8 type should contain a string-utf8 value")
                    };
                    String::from_utf8(utf8_data.items().iter().flatten().copied().collect())
                        .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?
                        .chars()
                        .flat_map(|c| (c as u32).to_be_bytes())
                        .collect()
                }
            };
            let mut written = 0;
            let mut in_mem_written = 0;

            // Write the value to `in_mem_offset`
            memory
                .write(
                    &mut store,
                    (in_mem_offset + in_mem_written) as usize,
                    &string,
                )
                .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
            in_mem_written += string.len() as i32;

            if include_repr {
                // Write the representation (offset and length) of the value to
                // `offset`.
                let offset_buffer = in_mem_offset.to_le_bytes();
                memory
                    .write(&mut store, (offset) as usize, &offset_buffer)
                    .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
                written += 4;
                let len_buffer = in_mem_written.to_le_bytes();
                memory
                    .write(&mut store, (offset + written) as usize, &len_buffer)
                    .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
                written += 4;
            }

            Ok((written, in_mem_written))
        }
        TypeSignature::SequenceType(SequenceSubtype::ListType(list)) => {
            let mut written = 0;
            let list_data = value_as_list(value)?;
            let elem_ty = list.get_list_item_type();
            // For a list, the values are written to the memory at
            // `in_mem_offset`, and the representation (offset and length) is
            // written to the memory at `offset`. The `in_mem_offset` for the
            // list elements should be after their representations.
            let val_offset = in_mem_offset;
            let val_in_mem_offset =
                in_mem_offset + list_data.data.len() as i32 * get_type_size(elem_ty);
            let mut val_written = 0;
            let mut val_in_mem_written = 0;
            for elem in &list_data.data {
                let (new_written, new_in_mem_written) = write_to_wasm(
                    store.as_context_mut(),
                    memory,
                    elem_ty,
                    val_offset + val_written,
                    val_in_mem_offset + val_in_mem_written,
                    elem,
                    true,
                )?;
                val_written += new_written;
                val_in_mem_written += new_in_mem_written;
            }

            if include_repr {
                // Write the representation (offset and length) of the value to
                // `offset`.
                let offset_buffer = in_mem_offset.to_le_bytes();
                memory
                    .write(&mut store, (offset) as usize, &offset_buffer)
                    .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
                written += 4;
                let len_buffer = val_written.to_le_bytes();
                memory
                    .write(&mut store, (offset + 4) as usize, &len_buffer)
                    .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
                written += 4;
            }

            Ok((written, val_written + val_in_mem_written))
        }
        TypeSignature::ResponseType(inner_types) => {
            let mut written = 0;
            let mut in_mem_written = 0;
            let res = value_as_response(value)?;
            let indicator = if res.committed { 1i32 } else { 0i32 };
            let indicator_bytes = indicator.to_le_bytes();
            memory
                .write(&mut store, (offset) as usize, &indicator_bytes)
                .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
            written += 4;

            if res.committed {
                let (new_written, new_in_mem_written) = write_to_wasm(
                    store,
                    memory,
                    &inner_types.0,
                    offset + written,
                    in_mem_offset,
                    &res.data,
                    true,
                )?;
                written += new_written;
                in_mem_written += new_in_mem_written;

                // Skip space for the err value
                written += get_type_size(&inner_types.1);
            } else {
                // Skip space for the ok value
                written += get_type_size(&inner_types.0);

                let (new_written, new_in_mem_written) = write_to_wasm(
                    store,
                    memory,
                    &inner_types.1,
                    offset + written,
                    in_mem_offset,
                    &res.data,
                    true,
                )?;
                written += new_written;
                in_mem_written += new_in_mem_written;
            }
            Ok((written, in_mem_written))
        }
        TypeSignature::BoolType => {
            let bool_val = value_as_bool(value)?;
            let val = if bool_val { 1u32 } else { 0u32 };
            let val_bytes = val.to_le_bytes();
            memory
                .write(&mut store, (offset) as usize, &val_bytes)
                .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
            Ok((4, 0))
        }
        TypeSignature::NoType => {
            let val_bytes = [0u8; 4];
            memory
                .write(&mut store, (offset) as usize, &val_bytes)
                .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
            Ok((4, 0))
        }
        TypeSignature::OptionalType(inner_ty) => {
            let mut written = 0;
            let mut in_mem_written = 0;
            let opt_data = value_as_optional(value)?;
            let indicator = if opt_data.data.is_some() { 1i32 } else { 0i32 };
            let indicator_bytes = indicator.to_le_bytes();
            memory
                .write(&mut store, (offset) as usize, &indicator_bytes)
                .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
            written += 4;
            if let Some(inner) = opt_data.data.as_ref() {
                let (new_written, new_in_mem_written) = write_to_wasm(
                    store,
                    memory,
                    inner_ty,
                    offset + written,
                    in_mem_offset,
                    inner,
                    true,
                )?;
                written += new_written;
                in_mem_written += new_in_mem_written;
            } else {
                written += get_type_size(inner_ty);
            }
            Ok((written, in_mem_written))
        }
        TypeSignature::PrincipalType
        | TypeSignature::CallableType(_)
        | TypeSignature::TraitReferenceType(_) => {
            let principal = value_as_principal(value)?;
            let (standard, contract_name) = match principal {
                PrincipalData::Standard(s) => (s, ""),
                PrincipalData::Contract(contract_identifier) => (
                    &contract_identifier.issuer,
                    contract_identifier.name.as_str(),
                ),
            };
            let mut written = 0;
            let mut in_mem_written = 0;

            // Write the value to in_mem_offset
            memory
                .write(
                    &mut store,
                    (in_mem_offset + in_mem_written) as usize,
                    &[standard.version()],
                )
                .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
            in_mem_written += 1;
            memory
                .write(
                    &mut store,
                    (in_mem_offset + in_mem_written) as usize,
                    &standard.1,
                )
                .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
            in_mem_written += standard.1.len() as i32;
            if !contract_name.is_empty() {
                let len_buffer = [contract_name.len() as u8];
                memory
                    .write(
                        &mut store,
                        (in_mem_offset + in_mem_written) as usize,
                        &len_buffer,
                    )
                    .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
                in_mem_written += 1;
                let bytes = contract_name.as_bytes();
                memory
                    .write(&mut store, (in_mem_offset + in_mem_written) as usize, bytes)
                    .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
                in_mem_written += bytes.len() as i32;
            } else {
                let len_buffer = [0u8];
                memory
                    .write(
                        &mut store,
                        (in_mem_offset + in_mem_written) as usize,
                        &len_buffer,
                    )
                    .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
                in_mem_written += 1;
            }

            if include_repr {
                // Write the representation (offset and length of the value) to the
                // offset
                let offset_buffer = in_mem_offset.to_le_bytes();
                memory
                    .write(&mut store, (offset) as usize, &offset_buffer)
                    .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
                written += 4;
                let len_buffer = in_mem_written.to_le_bytes();
                memory
                    .write(&mut store, (offset + written) as usize, &len_buffer)
                    .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
                written += 4;
            }

            Ok((written, in_mem_written))
        }
        TypeSignature::TupleType(type_sig) => {
            let tuple_data = value_as_tuple(value)?;
            let mut written = 0;
            let mut in_mem_written = 0;

            for (key, val_type) in type_sig.get_type_map() {
                let val = tuple_data
                    .data_map
                    .get(key)
                    .ok_or(Error::Wasm(WasmError::ValueTypeMismatch))?;
                let (new_written, new_in_mem_written) = write_to_wasm(
                    store.as_context_mut(),
                    memory,
                    val_type,
                    offset + written,
                    in_mem_offset + in_mem_written,
                    val,
                    true,
                )?;
                written += new_written;
                in_mem_written += new_in_mem_written;
            }

            Ok((written, in_mem_written))
        }
        TypeSignature::ListUnionType(_) => {
            unreachable!("not a value type")
        }
    }
}

pub fn value_as_bool(value: &Value) -> Result<bool, Error> {
    match value {
        Value::Bool(b) => Ok(*b),
        _ => Err(Error::Wasm(WasmError::ValueTypeMismatch)),
    }
}

pub fn value_as_i128(value: &Value) -> Result<i128, Error> {
    match value {
        Value::Int(n) => Ok(*n),
        _ => Err(Error::Wasm(WasmError::ValueTypeMismatch)),
    }
}

pub fn value_as_u128(value: &Value) -> Result<u128, Error> {
    match value {
        Value::UInt(n) => Ok(*n),
        _ => Err(Error::Wasm(WasmError::ValueTypeMismatch)),
    }
}

pub fn value_as_principal(value: &Value) -> Result<&PrincipalData, Error> {
    match value {
        Value::Principal(p) => Ok(p),
        _ => Err(Error::Wasm(WasmError::ValueTypeMismatch)),
    }
}

pub fn value_as_buffer(value: Value) -> Result<BuffData, Error> {
    match value {
        Value::Sequence(SequenceData::Buffer(buffdata)) => Ok(buffdata),
        _ => Err(Error::Wasm(WasmError::ValueTypeMismatch)),
    }
}

pub fn value_as_optional(value: &Value) -> Result<&OptionalData, Error> {
    match value {
        Value::Optional(opt_data) => Ok(opt_data),
        _ => Err(Error::Wasm(WasmError::ValueTypeMismatch)),
    }
}

pub fn value_as_response(value: &Value) -> Result<&ResponseData, Error> {
    match value {
        Value::Response(res_data) => Ok(res_data),
        _ => Err(Error::Wasm(WasmError::ValueTypeMismatch)),
    }
}

pub fn value_as_string_ascii(value: Value) -> Result<ASCIIData, Error> {
    match value {
        Value::Sequence(SequenceData::String(CharType::ASCII(string_data))) => Ok(string_data),
        _ => Err(Error::Wasm(WasmError::ValueTypeMismatch)),
    }
}

pub fn value_as_tuple(value: &Value) -> Result<&TupleData, Error> {
    match value {
        Value::Tuple(d) => Ok(d),
        _ => Err(Error::Wasm(WasmError::ValueTypeMismatch)),
    }
}

pub fn value_as_list(value: &Value) -> Result<&ListData, Error> {
    match value {
        Value::Sequence(SequenceData::List(list_data)) => Ok(list_data),
        _ => Err(Error::Wasm(WasmError::ValueTypeMismatch)),
    }
}

/// Read bytes from the WASM memory at `offset` with `length`
pub fn read_bytes_from_wasm(
    memory: Memory,
    store: &mut impl AsContextMut,
    offset: i32,
    length: i32,
) -> Result<Vec<u8>, Error> {
    let mut buffer: Vec<u8> = vec![0; length as usize];
    memory
        .read(store, offset as usize, &mut buffer)
        .map_err(|e| Error::Wasm(WasmError::Runtime(e.into())))?;
    Ok(buffer)
}

/// Read an identifier (string) from the WASM memory at `offset` with `length`.
pub fn read_identifier_from_wasm(
    memory: Memory,
    store: &mut impl AsContextMut,
    offset: i32,
    length: i32,
) -> Result<String, Error> {
    let buffer = read_bytes_from_wasm(memory, store, offset, length)?;
    String::from_utf8(buffer).map_err(|e| Error::Wasm(WasmError::UnableToReadIdentifier(e)))
}

/// Return true if the value of the given type stays in memory, and false if
/// it is stored on the data stack.
pub fn is_in_memory_type(ty: &TypeSignature) -> bool {
    match ty {
        TypeSignature::NoType
        | TypeSignature::IntType
        | TypeSignature::UIntType
        | TypeSignature::BoolType
        | TypeSignature::TupleType(_)
        | TypeSignature::OptionalType(_)
        | TypeSignature::ResponseType(_) => false,
        TypeSignature::SequenceType(_)
        | TypeSignature::PrincipalType
        | TypeSignature::CallableType(_)
        | TypeSignature::TraitReferenceType(_) => true,
        TypeSignature::ListUnionType(_) => unreachable!("not a value type"),
    }
}

#[allow(clippy::unimplemented)]
fn clar2wasm_ty(ty: &TypeSignature) -> Vec<ValType> {
    match ty {
        TypeSignature::NoType => vec![ValType::I32], // TODO: issue #445. Can this just be empty?
        TypeSignature::IntType => vec![ValType::I64, ValType::I64],
        TypeSignature::UIntType => vec![ValType::I64, ValType::I64],
        TypeSignature::ResponseType(inner_types) => {
            let mut types = vec![ValType::I32];
            types.extend(clar2wasm_ty(&inner_types.0));
            types.extend(clar2wasm_ty(&inner_types.1));
            types
        }
        TypeSignature::SequenceType(_) => vec![
            ValType::I32, // offset
            ValType::I32, // length
        ],
        TypeSignature::BoolType => vec![ValType::I32],
        TypeSignature::PrincipalType | TypeSignature::CallableType(_) => vec![
            ValType::I32, // offset
            ValType::I32, // length
        ],
        TypeSignature::OptionalType(inner_ty) => {
            let mut types = vec![ValType::I32];
            types.extend(clar2wasm_ty(inner_ty));
            types
        }
        TypeSignature::TupleType(inner_types) => {
            let mut types = vec![];
            for inner_type in inner_types.get_type_map().values() {
                types.extend(clar2wasm_ty(inner_type));
            }
            types
        }
        _ => unimplemented!("{:?}", ty),
    }
}

/// Call a function in the contract.
#[allow(clippy::too_many_arguments)]
pub fn call_function<'a>(
    function_name: &str,
    args: &[Value],
    global_context: &'a mut GlobalContext,
    contract_context: &'a ContractContext,
    call_stack: &'a mut CallStack,
    sender: Option<PrincipalData>,
    caller: Option<PrincipalData>,
    sponsor: Option<PrincipalData>,
) -> Result<Value, Error> {
    let epoch = global_context.epoch_id;
    let clarity_version = *contract_context.get_clarity_version();
    let engine = global_context.engine.clone();
    let context = ClarityWasmContext::new_run(
        global_context,
        contract_context,
        call_stack,
        sender,
        caller,
        sponsor,
        None,
    );

    let func_types = context
        .contract_context()
        .lookup_function(function_name)
        .ok_or(CheckErrors::UndefinedFunction(function_name.to_string()))?;
    let module = context
        .contract_context()
        .with_wasm_module(|wasm_module| unsafe {
            Module::deserialize(&engine, wasm_module)
                .map_err(|e| Error::Wasm(WasmError::UnableToLoadModule(e)))
        })?;
    let mut store = Store::new(&engine, context);
    let mut linker = Linker::new(&engine);

    // Link in the host interface functions.
    link_host_functions(&mut linker)?;
    linker
        .define_cost_globals(&mut store)
        .map_err(|e| Error::Wasm(WasmError::UnableToLoadModule(e)))?;

    let instance = linker
        .instantiate(&mut store, &module)
        .map_err(|e| Error::Wasm(WasmError::UnableToLoadModule(e)))?;

    // Call the specified function
    let func = instance
        .get_func(&mut store, function_name)
        .ok_or(CheckErrors::UndefinedFunction(function_name.to_string()))?;

    // Access the global stack pointer from the instance
    let stack_pointer = instance
        .get_global(&mut store, "stack-pointer")
        .ok_or(Error::Wasm(WasmError::GlobalNotFound(
            "stack-pointer".to_string(),
        )))?;
    let mut offset = stack_pointer
        .get(&mut store)
        .i32()
        .ok_or(Error::Wasm(WasmError::ValueTypeMismatch))?;

    let memory = instance
        .get_memory(&mut store, "memory")
        .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

    // Determine how much space is needed for arguments
    let mut arg_size = 0;
    for arg in func_types.get_arg_types() {
        arg_size += get_type_in_memory_size(arg, false);
    }
    let mut in_mem_offset = offset + arg_size;

    // Convert the args into wasmtime values
    let mut wasm_args = vec![];
    for (arg, ty) in args.iter().zip(func_types.get_arg_types()) {
        let (arg_vec, new_offset, new_in_mem_offset) =
            pass_argument_to_wasm(memory, &mut store, ty, arg, offset, in_mem_offset)?;
        wasm_args.extend(arg_vec);
        offset = new_offset;
        in_mem_offset = new_in_mem_offset;
    }

    // Reserve stack space for the return value, if necessary.
    let return_type = func_types
        .get_return_type()
        .as_ref()
        .ok_or(Error::Wasm(WasmError::ExpectedReturnValue))?
        .clone();
    let (mut results, offset) = reserve_space_for_return(in_mem_offset, &return_type)?;

    // Update the stack pointer after space is reserved for the arguments and
    // return values.
    stack_pointer
        .set(&mut store, Val::I32(offset))
        .map_err(|e| Error::Wasm(WasmError::Runtime(e)))?;

    // Call the function
    func.call(&mut store, &wasm_args, &mut results)
        .map_err(|e| {
            error_mapping::resolve_error(e, instance, &mut store, &epoch, &clarity_version)
        })?;

    // If the function returns a value, translate it into a Clarity `Value`
    wasm_to_clarity_value(&return_type, 0, &results, memory, &mut &mut store, epoch)
        .map(|(val, _offset)| val)
        .and_then(|option_value| {
            option_value.ok_or_else(|| Error::Wasm(WasmError::ExpectedReturnValue))
        })
}

/// Convert a Clarity `Value` into one or more Wasm `Val`. If this value
/// requires writing into the Wasm memory, write it to the provided `offset`.
/// Return a vector of `Val`s that can be passed to a Wasm function, and the
/// two offsets, adjusted to the next available memory location.
fn pass_argument_to_wasm(
    memory: Memory,
    mut store: impl AsContextMut,
    ty: &TypeSignature,
    value: &Value,
    offset: i32,
    in_mem_offset: i32,
) -> Result<(Vec<Val>, i32, i32), Error> {
    match value {
        Value::UInt(n) => {
            let high = (n >> 64) as u64;
            let low = (n & 0xffff_ffff_ffff_ffff) as u64;
            let buffer = vec![Val::I64(low as i64), Val::I64(high as i64)];
            Ok((buffer, offset, in_mem_offset))
        }
        Value::Int(n) => {
            let high = (n >> 64) as u64;
            let low = (n & 0xffff_ffff_ffff_ffff) as u64;
            let buffer = vec![Val::I64(low as i64), Val::I64(high as i64)];
            Ok((buffer, offset, in_mem_offset))
        }
        Value::Bool(b) => Ok((
            vec![Val::I32(if *b { 1 } else { 0 })],
            offset,
            in_mem_offset,
        )),
        Value::Optional(o) => {
            let TypeSignature::OptionalType(inner_ty) = ty else {
                return Err(Error::Wasm(WasmError::ValueTypeMismatch));
            };

            if let Some(inner_value) = o.data.as_ref() {
                let mut buffer = vec![Val::I32(1)];
                let (inner_buffer, new_offset, new_in_mem_offset) = pass_argument_to_wasm(
                    memory,
                    store,
                    inner_ty,
                    inner_value,
                    offset,
                    in_mem_offset,
                )?;
                buffer.extend(inner_buffer);
                Ok((buffer, new_offset, new_in_mem_offset))
            } else {
                let buffer = clar2wasm_ty(ty)
                    .into_iter()
                    .map(|vt| match vt {
                        ValType::I32 => Val::I32(0),
                        ValType::I64 => Val::I64(0),
                        _ => unreachable!("No other types used in Clarity-Wasm"),
                    })
                    .collect();
                Ok((buffer, offset, in_mem_offset))
            }
        }
        Value::Response(r) => {
            let TypeSignature::ResponseType(inner_tys) = ty else {
                return Err(Error::Wasm(WasmError::ValueTypeMismatch));
            };
            let mut buffer = vec![Val::I32(r.committed as i32)];
            let (value_buffer, new_offset, new_in_mem_offset) = pass_argument_to_wasm(
                memory,
                store,
                if r.committed {
                    &inner_tys.0
                } else {
                    &inner_tys.1
                },
                &r.data,
                offset,
                in_mem_offset,
            )?;
            let empty_buffer = clar2wasm_ty(if r.committed {
                &inner_tys.1
            } else {
                &inner_tys.0
            })
            .into_iter()
            .map(|vt| match vt {
                ValType::I32 => Val::I32(0),
                ValType::I64 => Val::I64(0),
                _ => unreachable!("No other types used in Clarity-Wasm"),
            });

            if r.committed {
                buffer.extend(value_buffer);
                buffer.extend(empty_buffer);
            } else {
                buffer.extend(empty_buffer);
                buffer.extend(value_buffer);
            }

            Ok((buffer, new_offset, new_in_mem_offset))
        }
        Value::Sequence(SequenceData::String(CharType::ASCII(s))) => {
            // For a string, write the bytes into the memory, then pass the
            // offset and length to the Wasm function.
            let buffer = vec![Val::I32(in_mem_offset), Val::I32(s.data.len() as i32)];
            memory
                .write(
                    store.as_context_mut(),
                    in_mem_offset as usize,
                    s.data.as_slice(),
                )
                .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
            let adjusted_in_mem_offset = in_mem_offset + s.data.len() as i32;
            Ok((buffer, offset, adjusted_in_mem_offset))
        }
        Value::Sequence(SequenceData::String(CharType::UTF8(s))) => {
            // For a utf8 string, convert the chars to big-endian i32, convert this into a list of
            // bytes, then pass the offset and length to the wasm function
            let bytes: Vec<u8> = String::from_utf8(s.items().iter().flatten().copied().collect())
                .map_err(|e| Error::Wasm(WasmError::WasmGeneratorError(e.to_string())))?
                .chars()
                .flat_map(|c| (c as u32).to_be_bytes())
                .collect();
            let buffer = vec![Val::I32(in_mem_offset), Val::I32(bytes.len() as i32)];
            memory
                .write(&mut store, in_mem_offset as usize, &bytes)
                .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
            let adjusted_in_mem_offset = in_mem_offset + bytes.len() as i32;
            Ok((buffer, offset, adjusted_in_mem_offset))
        }
        Value::Sequence(SequenceData::Buffer(b)) => {
            // For a buffer, write the bytes into the memory, then pass the
            // offset and length to the Wasm function.
            let buffer = vec![Val::I32(in_mem_offset), Val::I32(b.data.len() as i32)];
            memory
                .write(
                    store.as_context_mut(),
                    in_mem_offset as usize,
                    b.data.as_slice(),
                )
                .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
            let adjusted_in_mem_offset = in_mem_offset + b.data.len() as i32;
            Ok((buffer, offset, adjusted_in_mem_offset))
        }
        Value::Sequence(SequenceData::List(l)) => {
            let TypeSignature::SequenceType(SequenceSubtype::ListType(ltd)) = ty else {
                return Err(Error::Wasm(WasmError::ValueTypeMismatch));
            };

            let mut buffer = vec![Val::I32(offset)];
            let mut written = 0;
            let mut in_mem_written = 0;
            for item in &l.data {
                let (len, in_mem_len) = write_to_wasm(
                    &mut store,
                    memory,
                    ltd.get_list_item_type(),
                    offset + written,
                    in_mem_offset + in_mem_written,
                    item,
                    true,
                )?;
                written += len;
                in_mem_written += in_mem_len;
            }
            buffer.push(Val::I32(written));
            Ok((buffer, offset + written, in_mem_offset + in_mem_written))
        }
        Value::Principal(PrincipalData::Standard(data)) => {
            let mut bytes: Vec<u8> = Vec::with_capacity(22);
            let v = data.version();
            let h = &data.1;
            bytes.push(v);
            bytes.extend(h);
            bytes.push(0);
            let buffer = vec![Val::I32(in_mem_offset), Val::I32(bytes.len() as i32)];
            memory
                .write(&mut store, in_mem_offset as usize, &bytes)
                .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
            let adjusted_in_mem_offset = in_mem_offset + bytes.len() as i32;
            Ok((buffer, offset, adjusted_in_mem_offset))
        }
        Value::Principal(PrincipalData::Contract(p))
        | Value::CallableContract(CallableData {
            contract_identifier: p,
            ..
        }) => {
            // Callable types can just ignore the optional trait identifier, and
            // is handled like a qualified contract
            let QualifiedContractIdentifier { issuer, name } = p;
            let v = issuer.version();
            let h = &issuer.1;
            let bytes: Vec<u8> = std::iter::once(v)
                .chain(h.iter().copied())
                .chain(std::iter::once(name.len()))
                .chain(name.as_bytes().iter().copied())
                .collect();
            let buffer = vec![Val::I32(in_mem_offset), Val::I32(bytes.len() as i32)];
            memory
                .write(&mut store, in_mem_offset as usize, &bytes)
                .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
            let adjusted_in_mem_offset = in_mem_offset + bytes.len() as i32;
            Ok((buffer, offset, adjusted_in_mem_offset))
        }
        Value::Tuple(TupleData { data_map, .. }) => {
            let TypeSignature::TupleType(tuple_ty) = ty else {
                return Err(Error::Wasm(WasmError::ValueTypeMismatch));
            };

            let mut buffer = vec![];
            let mut offset = offset;
            let mut in_mem_offset = in_mem_offset;
            for (name, ty) in tuple_ty.get_type_map() {
                let b;
                (b, offset, in_mem_offset) = pass_argument_to_wasm(
                    memory,
                    store.as_context_mut(),
                    ty,
                    &data_map[name],
                    offset,
                    in_mem_offset,
                )?;
                buffer.extend(b);
            }
            Ok((buffer, offset, in_mem_offset))
        }
    }
}

/// Reserve space on the Wasm stack for the return value of a function, if
/// needed, and return a vector of `Val`s that can be passed to `call`, as a
/// place to store the return value, along with the new offset, which is the
/// next available memory location.
fn reserve_space_for_return(
    offset: i32,
    return_type: &TypeSignature,
) -> Result<(Vec<Val>, i32), Error> {
    match return_type {
        TypeSignature::UIntType | TypeSignature::IntType => {
            Ok((vec![Val::I64(0), Val::I64(0)], offset))
        }
        TypeSignature::BoolType => Ok((vec![Val::I32(0)], offset)),
        TypeSignature::OptionalType(optional) => {
            let mut vals = vec![Val::I32(0)];
            let (opt_vals, adjusted) = reserve_space_for_return(offset, optional)?;
            vals.extend(opt_vals);
            Ok((vals, adjusted))
        }
        TypeSignature::ResponseType(response) => {
            let mut vals = vec![Val::I32(0)];
            let (mut subexpr_values, mut adjusted) = reserve_space_for_return(offset, &response.0)?;
            vals.extend(subexpr_values);
            (subexpr_values, adjusted) = reserve_space_for_return(adjusted, &response.1)?;
            vals.extend(subexpr_values);
            Ok((vals, adjusted))
        }
        TypeSignature::NoType => Ok((vec![Val::I32(0)], offset)),
        TypeSignature::SequenceType(_)
        | TypeSignature::PrincipalType
        | TypeSignature::CallableType(_)
        | TypeSignature::TraitReferenceType(_) => {
            // All in-memory types return an offset and length.˝
            let length = get_type_in_memory_size(return_type, false);

            // Return values will be offset and length
            Ok((vec![Val::I32(0), Val::I32(0)], offset + length))
        }
        TypeSignature::TupleType(type_sig) => {
            let mut vals = vec![];
            let mut adjusted = offset;
            for ty in type_sig.get_type_map().values() {
                let (subexpr_values, new_offset) = reserve_space_for_return(adjusted, ty)?;
                vals.extend(subexpr_values);
                adjusted = new_offset;
            }
            Ok((vals, adjusted))
        }
        TypeSignature::ListUnionType(_) => {
            unreachable!("not a valid return type");
        }
    }
}

/// Serializes a [TraitIdentifier] to bytes with this format:
/// issuer principal as 21 bytes + contract name length as byte + contract name as bytes + trait name length as byte + trait name as bytes
pub fn trait_identifier_as_bytes(
    TraitIdentifier {
        name: trait_name,
        contract_identifier:
            QualifiedContractIdentifier {
                issuer,
                name: contract_name,
            },
    }: &TraitIdentifier,
) -> Vec<u8> {
    let mut res = Vec::with_capacity(
        1 + 20 + 1 + contract_name.len() as usize + 1 + trait_name.len() as usize,
    );

    // serialize issuer: 1 byte version + 20 bytes
    res.push(issuer.version());
    res.extend(issuer.1);

    // serialize contract_name: 1 byte name length + name bytes
    res.push(contract_name.len());
    res.extend(contract_name.bytes());

    // serialize trait name: 1 byte name length + name bytes
    res.push(trait_name.len());
    res.extend(trait_name.bytes());

    res
}

/// Tries to deserialize bytes into a [TraitIdentifier].
/// This is the opposite of the function [trait_identifier_as_bytes].
pub fn trait_identifier_from_bytes(bytes: &[u8]) -> Result<TraitIdentifier, Error> {
    let not_enough_bytes = || {
        Error::Wasm(WasmError::Expect(
            "Not enough bytes for a trait deserialization".to_owned(),
        ))
    };

    // deserilize issuer
    let (version, bytes) = bytes.split_first().ok_or_else(not_enough_bytes)?;
    let (issuer_bytes, bytes) = bytes.split_at_checked(20).ok_or_else(not_enough_bytes)?;

    // we can unwrap here since we took the exact number of bytes to create a Principal.
    #[allow(clippy::unwrap_used)]
    let issuer = StandardPrincipalData::new(*version, issuer_bytes.try_into().unwrap())?;

    // deserialize contract name
    let (contract_name_len, bytes) = bytes.split_first().ok_or_else(not_enough_bytes)?;
    let (contract_name_bytes, bytes) = bytes
        .split_at_checked(*contract_name_len as usize)
        .ok_or_else(not_enough_bytes)?;
    let contract_name: ContractName = String::from_utf8(contract_name_bytes.to_owned())
        .map_err(|err| Error::Wasm(WasmError::UnableToReadIdentifier(err)))?
        .try_into()?;

    // deserialize trait name
    let (trait_name_len, bytes) = bytes.split_first().ok_or_else(not_enough_bytes)?;
    if bytes.len() != *trait_name_len as usize {
        return Err(not_enough_bytes());
    }
    let trait_name: ClarityName = String::from_utf8(bytes.to_owned())
        .map_err(|err| Error::Wasm(WasmError::UnableToReadIdentifier(err)))?
        .try_into()?;

    Ok(TraitIdentifier::new(issuer, contract_name, trait_name))
}

pub fn signature_from_string(
    val: &str,
    version: ClarityVersion,
    epoch: StacksEpochId,
) -> Result<TypeSignature, Error> {
    let expr = build_ast(
        &QualifiedContractIdentifier::transient(),
        val,
        &mut (),
        version,
        epoch,
    )?
    .expressions;
    let expr = expr.first().ok_or(CheckErrors::InvalidTypeDescription)?;
    Ok(TypeSignature::parse_type_repr(
        StacksEpochId::latest(),
        expr,
        &mut (),
    )?)
}

pub fn get_global(module: &walrus::Module, name: &str) -> Result<GlobalId, GeneratorError> {
    module
        .globals
        .iter()
        .find(|global| {
            global
                .name
                .as_ref()
                .is_some_and(|other_name| name == other_name)
        })
        .map(|global| global.id())
        .ok_or_else(|| {
            GeneratorError::InternalError(format!("Expected to find a global named ${name}"))
        })
}

pub enum ArgumentCountCheck {
    Exact,
    AtLeast,
    AtMost,
}

pub fn check_argument_count(
    generator: &mut WasmGenerator,
    builder: &mut InstrSeqBuilder,
    expected: usize,
    actual: usize,
    check: ArgumentCountCheck,
) -> Result<(), GeneratorError> {
    let expected = expected as u32;
    let actual = actual as u32;
    let mut handle_mismatch = |error_map: ErrorMap| -> Result<(), GeneratorError> {
        let (arg_name_offset_start, arg_name_len_expected) =
            generator.add_bytes_literal(&expected.to_le_bytes())?;
        let (_, arg_name_len_got) = generator.add_bytes_literal(&actual.to_le_bytes())?;
        builder
            .i32_const(arg_name_offset_start as i32)
            .global_set(get_global(&generator.module, "runtime-error-arg-offset")?)
            .i32_const((arg_name_len_expected + arg_name_len_got) as i32)
            .global_set(get_global(&generator.module, "runtime-error-arg-len")?)
            .i32_const(error_map as i32)
            .call(generator.func_by_name("stdlib.runtime-error"));
        Ok(())
    };

    match check {
        ArgumentCountCheck::Exact => {
            if expected != actual {
                handle_mismatch(ErrorMap::ArgumentCountMismatch)?;
                return Err(GeneratorError::ArgumentCountMismatch);
            }
        }
        ArgumentCountCheck::AtLeast => {
            if expected > actual {
                handle_mismatch(ErrorMap::ArgumentCountAtLeast)?;
                return Err(GeneratorError::ArgumentCountMismatch);
            }
        }
        ArgumentCountCheck::AtMost => {
            if expected < actual {
                handle_mismatch(ErrorMap::ArgumentCountAtMost)?;
                return Err(GeneratorError::ArgumentCountMismatch);
            }
        }
    }
    Ok(())
}

#[macro_export]
macro_rules! check_args {
    ($generator:expr, $builder:expr, $expected:expr, $actual:expr, $check:expr) => {
        if check_argument_count($generator, $builder, $expected, $actual, $check).is_err() {
            // short cutting traverse functions
            $builder.unreachable();
            return Ok(());
        }
    };
}

#[cfg(test)]
mod tests {

    use clarity::vm::types::{StandardPrincipalData, TraitIdentifier};
    use clarity::vm::{ClarityName, ContractName};
    use proptest::prelude::*;

    use crate::wasm_utils::{trait_identifier_as_bytes, trait_identifier_from_bytes};

    proptest! {
        #[test]
        fn serialize_deserialize_trait_id(
            issuer in (0u8..32, proptest::array::uniform20(any::<u8>()))
                .prop_map(|(v, bs)| StandardPrincipalData::new_unsafe(v, bs)),
            contract_name in "[a-zA-Z]([a-zA-Z0-9]|[-_]){0,127}"
                .prop_map(|name| ContractName::try_from(name).unwrap()),
            trait_name in "[a-zA-Z]([a-zA-Z0-9]|[-_!?+<>=/*]){0,127}"
                .prop_map(|name| ClarityName::try_from(name).unwrap())
        ) {
            let trait_id = TraitIdentifier::new(issuer, contract_name, trait_name);

            assert_eq!(
                trait_identifier_from_bytes(&trait_identifier_as_bytes(&trait_id))
                    .expect("Could not deserialize the trait identifier"),
                trait_id
            );
        }
    }
}
