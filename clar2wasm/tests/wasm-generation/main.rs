#![cfg(test)]
pub mod arithmetic;
pub mod bindings;
pub mod bitwise;
pub mod blockinfo;
pub mod comparison;
pub mod conditionals;
pub mod consensus_buff;
pub mod constants;
pub mod contracts;
pub mod control_flow;
pub mod copy;
pub mod default_to;
pub mod equal;
pub mod function_calls;
pub mod functions;
pub mod hashing;
pub mod maps;
pub mod noop;
pub mod optional;
pub mod principal;
pub mod print;
pub mod regression;
pub mod response;
pub mod secp256k1;
pub mod sequences;
pub mod serialization_size;
pub mod stx;
pub mod tokens;
pub mod traits;
pub mod tuple;
pub mod values;

use std::env;
use std::ops::Deref;

const DEFAULT_CASES: u32 = 10;

fn runtime_config() -> ProptestConfig {
    let cases_string = env::var("PROPTEST_CASES").unwrap_or_default();
    let cases = cases_string.parse().unwrap_or(DEFAULT_CASES);

    ProptestConfig {
        cases,
        ..Default::default()
    }
}

use clarity::vm::types::{
    ASCIIData, BuffData, CharType, ListData, ListTypeData, OptionalData, PrincipalData,
    QualifiedContractIdentifier, ResponseData, SequenceData, SequenceSubtype,
    StandardPrincipalData, StringSubtype, StringUTF8Length, TupleData, TupleTypeSignature,
    TypeSignature, UTF8Data, Value, MAX_VALUE_SIZE,
};
use clarity::vm::ContractName;
use proptest::prelude::*;

pub fn prop_signature() -> impl Strategy<Value = TypeSignature> {
    let leaf = prop_oneof![
        Just(TypeSignature::IntType),
        Just(TypeSignature::UIntType),
        Just(TypeSignature::BoolType),
        (0u32..128).prop_map(|s| TypeSignature::SequenceType(SequenceSubtype::BufferType(
            s.try_into().unwrap()
        ))),
        (0u32..128).prop_map(|s| TypeSignature::SequenceType(SequenceSubtype::StringType(
            StringSubtype::ASCII(s.try_into().unwrap())
        ))),
        Just(TypeSignature::PrincipalType),
        (0u32..32).prop_map(|s| TypeSignature::SequenceType(SequenceSubtype::StringType(
            StringSubtype::UTF8(s.try_into().unwrap())
        )))
    ];
    leaf.prop_recursive(5, 64, 10, |inner| {
        prop_oneof![
            // optional type: 10% NoType + 90% any other type
            prop_oneof![
                1 => Just(TypeSignature::NoType),
                9 => inner.clone(),
            ]
            .prop_map(|t| TypeSignature::new_option(t.clone()).unwrap_or(t)),
            // response type: 20% (NoType, any) + 20% (any, NoType) + 60% (any, any)
            prop_oneof![
                1 => inner.clone().prop_map(|ok_ty| TypeSignature::new_response(ok_ty.clone(), TypeSignature::NoType).unwrap_or(ok_ty)),
                1 => inner.clone().prop_map(|err_ty| TypeSignature::new_response(TypeSignature::NoType, err_ty.clone()).unwrap_or(err_ty)),
                3 => (inner.clone(), inner.clone()).prop_map(|(ok_ty, err_ty)| TypeSignature::new_response(ok_ty.clone(), err_ty).unwrap_or(ok_ty)),
            ],
            // tuple type
            prop::collection::btree_map(
                r#"[a-zA-Z]{1,16}"#.prop_map(|name| name.try_into().unwrap()),
                inner.clone(),
                1..8
            )
            .prop_map(|btree| {
                let fallback = btree.iter().next().unwrap().1.clone();
                TupleTypeSignature::try_from(btree).map(TypeSignature::TupleType).unwrap_or(fallback)
            }),
            // list type
            (8u32..32, inner.clone()).prop_map(|(s, ty)| TypeSignature::list_of(ty.clone(), s).unwrap_or(ty)),
        ]
    })
}

#[derive(Clone, PartialEq, Eq)]
pub struct PropValue(Value);

impl From<Value> for PropValue {
    fn from(value: Value) -> Self {
        PropValue(value)
    }
}

impl From<PropValue> for Value {
    fn from(value: PropValue) -> Self {
        value.0
    }
}

impl Deref for PropValue {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.inner()
    }
}

impl std::fmt::Debug for PropValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PropValue")
            .field("value", &self.to_string())
            .field("type", &self.type_string())
            .finish()
    }
}

impl std::fmt::Display for PropValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.0 {
            Value::Sequence(SequenceData::String(clarity::vm::types::CharType::ASCII(
                ASCIIData { data },
            ))) => {
                write!(f, "\"")?;
                for b in data {
                    if [b'\\', b'"'].contains(b) {
                        write!(f, "\\")?;
                    }
                    write!(f, "{}", *b as char)?;
                }
                write!(f, "\"")
            }
            Value::Sequence(SequenceData::String(CharType::UTF8(UTF8Data { data }))) => {
                write!(f, "u\"")?;
                for bytes in data {
                    // SAFETY: a utf8 sequence always contains a valid sequence of utf8 chars as vec of bytes
                    let c = unsafe { std::str::from_utf8_unchecked(bytes).chars().next().unwrap() };
                    match c {
                        '\\' | '\"' => write!(f, "\\{c}")?,
                        _ if c.is_ascii_graphic() => write!(f, "{c}")?,
                        _ => write!(f, r#"\u{{{:X}}}"#, c as u32)?,
                    }
                }
                write!(f, "\"")
            }
            Value::Principal(p) => write!(f, "'{p}"),
            Value::Optional(OptionalData { data }) => match data {
                Some(inner) => write!(f, "(some {})", PropValue(*inner.clone())),
                None => write!(f, "none"),
            },
            Value::Response(ResponseData { committed, data }) => {
                if *committed {
                    write!(f, "(ok {})", PropValue(*data.clone()))
                } else {
                    write!(f, "(err {})", PropValue(*data.clone()))
                }
            }
            Value::Sequence(SequenceData::List(ListData { data, .. })) => {
                write!(f, "(list")?;
                for d in data {
                    write!(f, " ")?;
                    write!(f, "{}", PropValue(d.clone()))?;
                }
                write!(f, ")")
            }
            Value::Tuple(data) => {
                write!(f, "(tuple")?;
                for (key, value) in &data.data_map {
                    write!(f, " ")?;
                    write!(f, "({} {})", &**key, PropValue(value.clone()))?;
                }
                write!(f, ")")
            }
            otherwise => write!(f, "{otherwise}"),
        }
    }
}

impl PropValue {
    pub fn any() -> impl Strategy<Value = Self> {
        prop_signature().prop_flat_map(prop_value).prop_map_into()
    }

    pub fn from_type(ty: TypeSignature) -> impl Strategy<Value = Self> {
        prop_value(ty).prop_map_into()
    }

    pub fn many_from_type(ty: TypeSignature, count: usize) -> impl Strategy<Value = Vec<Self>> {
        prop::collection::vec(Self::from_type(ty.clone()), count)
    }

    pub fn any_sequence(size: usize) -> impl Strategy<Value = Self> {
        let any_list = prop_signature()
            .prop_filter("skip too large", move |ty| {
                TypeSignature::list_of(ty.clone(), size as u32).is_ok()
            })
            .prop_ind_flat_map2(move |ty| prop::collection::vec(prop_value(ty), size))
            .prop_map(move |(ty, vec)| {
                Value::Sequence(SequenceData::List(ListData {
                    data: vec,
                    type_signature: ListTypeData::new_list(ty, size as u32).unwrap(),
                }))
            });
        // TODO: add string-utf8
        prop_oneof![
            // 10% chance for a buffer
            1 => buffer(size as u32),
            // 10% chance for a string-ascii
            1 => string_ascii(size as u32),
            // 80% chance for a list
            8 => any_list
        ]
        .prop_map_into()
    }

    pub fn inner(&self) -> &Value {
        &self.0
    }
}

impl TryFrom<Vec<PropValue>> for PropValue {
    type Error = clarity::vm::errors::Error;

    fn try_from(values: Vec<PropValue>) -> Result<Self, Self::Error> {
        let values = values.into_iter().map(Value::from).collect();
        Value::cons_list_unsanitized(values).map(PropValue::from)
    }
}

fn prop_value(ty: TypeSignature) -> impl Strategy<Value = Value> {
    match ty {
        TypeSignature::NoType => unreachable!(),
        TypeSignature::IntType => int().boxed(),
        TypeSignature::UIntType => uint().boxed(),
        TypeSignature::BoolType => bool().boxed(),
        TypeSignature::OptionalType(ty) => optional(*ty).boxed(),
        TypeSignature::ResponseType(ok_err) => response(ok_err.0, ok_err.1).boxed(),
        TypeSignature::SequenceType(SequenceSubtype::BufferType(size)) => {
            buffer(size.into()).boxed()
        }
        TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(size))) => {
            string_ascii(size.into()).boxed()
        }
        TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(size))) => {
            string_utf8(size.into()).boxed()
        }
        TypeSignature::SequenceType(SequenceSubtype::ListType(list_type_data)) => {
            list(list_type_data).boxed()
        }
        TypeSignature::TupleType(tuple_ty) => tuple(tuple_ty).boxed(),
        TypeSignature::PrincipalType => {
            prop_oneof![standard_principal(), qualified_principal()].boxed()
        }
        // TODO
        TypeSignature::ListUnionType(_) => todo!(),
        TypeSignature::CallableType(_) => todo!(),
        TypeSignature::TraitReferenceType(_) => todo!(),
    }
}

fn int() -> impl Strategy<Value = Value> {
    any::<i128>().prop_map(Value::Int)
}

fn uint() -> impl Strategy<Value = Value> {
    any::<u128>().prop_map(Value::UInt)
}

fn bool() -> impl Strategy<Value = Value> {
    any::<bool>().prop_map(Value::Bool)
}

pub fn string_ascii(size: u32) -> impl Strategy<Value = Value> {
    let size = size as usize;
    prop::collection::vec(0x20u8..0x7e, size..=size).prop_map(|bytes| {
        Value::Sequence(SequenceData::String(clarity::vm::types::CharType::ASCII(
            clarity::vm::types::ASCIIData { data: bytes },
        )))
    })
}

pub fn string_utf8(size: u32) -> impl Strategy<Value = Value> {
    prop::collection::vec(any::<char>(), size as usize).prop_map(|chars| {
        let mut data = Vec::with_capacity(chars.len());
        for c in chars {
            let mut encoded_char = vec![0; c.len_utf8()];
            c.encode_utf8(encoded_char.as_mut());
            data.push(encoded_char);
        }
        Value::Sequence(SequenceData::String(CharType::UTF8(UTF8Data { data })))
    })
}

fn buffer(size: u32) -> impl Strategy<Value = Value> {
    let size = size as usize;
    prop::collection::vec(any::<u8>(), size..=size)
        .prop_map(|bytes| Value::Sequence(SequenceData::Buffer(BuffData { data: bytes })))
}

fn optional(inner_ty: TypeSignature) -> impl Strategy<Value = Value> {
    match inner_ty {
        TypeSignature::NoType => Just(Value::none()).boxed(),
        _ => prop::option::of(prop_value(inner_ty))
            .prop_map(|v| {
                Value::Optional(OptionalData {
                    data: v.map(Box::new),
                })
            })
            .boxed(),
    }
}

fn response(ok_ty: TypeSignature, err_ty: TypeSignature) -> impl Strategy<Value = Value> {
    match (ok_ty, err_ty) {
        (TypeSignature::NoType, err_ty) => prop_value(err_ty)
            .prop_map(|err| {
                Value::Response(ResponseData {
                    committed: false,
                    data: Box::new(err),
                })
            })
            .boxed(),
        (ok_ty, TypeSignature::NoType) => prop_value(ok_ty)
            .prop_map(|ok| {
                Value::Response(ResponseData {
                    committed: true,
                    data: Box::new(ok),
                })
            })
            .boxed(),
        (ok_ty, err_ty) => prop::result::maybe_err(prop_value(ok_ty), prop_value(err_ty))
            .prop_map(|res| {
                Value::Response(ResponseData {
                    committed: res.is_ok(),
                    data: res.map_or_else(Box::new, Box::new),
                })
            })
            .boxed(),
    }
}

fn list(list_type_data: ListTypeData) -> impl Strategy<Value = Value> {
    prop::collection::vec(
        prop_value(list_type_data.get_list_item_type().clone()),
        0..=list_type_data.get_max_len() as usize,
    )
    .prop_map(move |v| {
        Value::Sequence(SequenceData::List(ListData {
            data: v,
            type_signature: list_type_data.clone(),
        }))
    })
}

fn tuple(tuple_ty: TupleTypeSignature) -> impl Strategy<Value = Value> {
    let fields: Vec<_> = tuple_ty.get_type_map().keys().cloned().collect();
    let strategies: Vec<_> = tuple_ty
        .get_type_map()
        .values()
        .cloned()
        .map(prop_value)
        .collect();
    strategies.prop_map(move |vec_values| {
        TupleData {
            type_signature: tuple_ty.clone(),
            data_map: fields.clone().into_iter().zip(vec_values).collect(),
        }
        .into()
    })
}

fn standard_principal() -> impl Strategy<Value = Value> {
    // Generate a version byte in the range [0, 31] and a 20-byte vector for the hash.
    (0u8..32, prop::collection::vec(any::<u8>(), 20))
        .prop_map(|(v, hash)| {
            // Since the generated vector always has exactly 20 bytes,
            // the conversion to [u8; 20] will not fail.
            let hash_array: [u8; 20] = hash.try_into().expect("Expected 20-byte vector for hash");
            // Create a StandardPrincipalData instance. This unwrap is safe since the constructor
            // is designed to succeed with valid inputs.
            let principal = StandardPrincipalData::new(v, hash_array)
                .expect("Failed to create StandardPrincipalData");
            Value::Principal(PrincipalData::Standard(principal))
        })
        .no_shrink()
}

fn qualified_principal() -> impl Strategy<Value = Value> {
    (standard_principal(), "[a-zA-Z]{1,40}").prop_map(|(issuer_value, name)| {
        let Value::Principal(PrincipalData::Standard(issuer)) = issuer_value else {
            unreachable!()
        };
        let name = ContractName::from(&*name);
        Value::Principal(PrincipalData::Contract(QualifiedContractIdentifier {
            issuer,
            name,
        }))
    })
}

trait TypePrinter {
    fn type_string(&self) -> String;
}

impl TypePrinter for PropValue {
    fn type_string(&self) -> String {
        self.0.type_string()
    }
}

impl TypePrinter for Value {
    fn type_string(&self) -> String {
        match &self {
            Value::Int(_) => type_string(&TypeSignature::IntType),
            Value::UInt(_) => type_string(&TypeSignature::UIntType),
            Value::Bool(_) => type_string(&TypeSignature::BoolType),
            Value::Sequence(SequenceData::Buffer(length)) => {
                type_string(&TypeSignature::SequenceType(SequenceSubtype::BufferType(
                    length
                        .len()
                        .expect("Failed to get buffer length from sequence data"),
                )))
            }
            Value::Sequence(SequenceData::String(CharType::ASCII(data))) => type_string(
                &TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(
                    data.len()
                        .expect("Failed to get ASCII string length from sequence data"),
                ))),
            ),
            Value::Sequence(SequenceData::String(CharType::UTF8(data))) => type_string(
                &TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(
                    StringUTF8Length::try_from(u32::from(
                        data.len()
                            .expect("Failed to get UTF8 string length from sequence data"),
                    ))
                    .unwrap_or(StringUTF8Length::try_from(MAX_VALUE_SIZE / 4).unwrap()),
                ))),
            ),
            Value::Optional(inner) => inner.type_string(),
            Value::Response(inner) => inner.type_string(),
            Value::Sequence(SequenceData::List(list_data)) => list_data.type_string(),
            Value::Tuple(data) => data.type_string(),
            Value::Principal(_) => type_string(&TypeSignature::PrincipalType),
            Value::CallableContract(_) => type_string(&TypeSignature::PrincipalType),
        }
    }
}

impl TypePrinter for OptionalData {
    fn type_string(&self) -> String {
        let inner = match self.data {
            Some(ref inner) => inner.type_string(),
            None => "int".to_owned(), // We need to default to something here
        };
        format!("(optional {inner})")
    }
}

impl TypePrinter for ResponseData {
    fn type_string(&self) -> String {
        let (ok_string, err_string) = if self.committed {
            (self.data.type_string(), "int".to_owned())
        } else {
            ("int".to_owned(), self.data.type_string())
        };
        format!("(response {ok_string} {err_string})")
    }
}

impl TypePrinter for ListData {
    fn type_string(&self) -> String {
        format!(
            "(list {} {})",
            self.data.len(),
            type_string(self.type_signature.get_list_item_type())
        )
    }
}

impl TypePrinter for TupleData {
    fn type_string(&self) -> String {
        type_string(&TypeSignature::TupleType(self.type_signature.clone()))
    }
}

pub fn type_string(ty: &TypeSignature) -> String {
    match ty {
        TypeSignature::IntType => "int".to_owned(),
        TypeSignature::UIntType => "uint".to_owned(),
        TypeSignature::BoolType => "bool".to_owned(),
        TypeSignature::OptionalType(inner) => format!("(optional {})", type_string(inner)),
        TypeSignature::ResponseType(inner) => format!(
            "(response {} {})",
            type_string(&inner.0),
            type_string(&inner.1)
        ),
        TypeSignature::SequenceType(SequenceSubtype::BufferType(len)) => format!("(buff {len})"),
        TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(len))) => {
            format!("(string-ascii {len})")
        }
        TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(len))) => {
            format!("(string-utf8 {len})")
        }
        TypeSignature::SequenceType(SequenceSubtype::ListType(list_type_data)) => {
            format!(
                "(list {} {})",
                list_type_data.get_max_len(),
                type_string(list_type_data.get_list_item_type())
            )
        }
        TypeSignature::TupleType(tuple_ty) => {
            let tuple_ty = {
                let mut v: Vec<_> = tuple_ty.get_type_map().iter().collect();
                v.sort_unstable_by_key(|&(k, _)| k);
                v
            };
            let mut s = String::new();
            s.push('{');
            for (key, value) in tuple_ty {
                s.push_str(key);
                s.push_str(": ");
                s.push_str(&type_string(value));
                s.push(',');
            }
            s.push('}');
            s
        }
        TypeSignature::PrincipalType => "principal".to_owned(),
        TypeSignature::CallableType(_) => "principal".to_owned(),
        TypeSignature::TraitReferenceType(_) => "principal".to_owned(),
        TypeSignature::NoType => "int".to_owned(), // Use "int" as a default type
        TypeSignature::ListUnionType(_) => unreachable!(),
    }
}

#[cfg(test)]
mod tests {
    use clarity::vm::types::{PrincipalData, UTF8Data};

    use super::*;

    #[test]
    fn check_type_string() {
        assert_eq!(Value::Int(0).type_string(), "int");
        assert_eq!(Value::UInt(0).type_string(), "uint");
        assert_eq!(Value::Bool(false).type_string(), "bool");
        assert_eq!(
            Value::Sequence(SequenceData::Buffer(BuffData { data: vec![] })).type_string(),
            "(buff 0)"
        );
        assert_eq!(
            Value::Sequence(SequenceData::Buffer(BuffData {
                data: vec![1, 2, 3, 4, 5]
            }))
            .type_string(),
            "(buff 5)"
        );
        assert_eq!(
            Value::Sequence(SequenceData::String(CharType::ASCII(ASCIIData {
                data: vec![]
            })))
            .type_string(),
            "(string-ascii 0)"
        );
        assert_eq!(
            Value::Sequence(SequenceData::String(CharType::ASCII(ASCIIData {
                data: vec![0x68, 0x65, 0x6c, 0x6c, 0x6f]
            })))
            .type_string(),
            "(string-ascii 5)"
        );
        assert_eq!(
            Value::Sequence(SequenceData::String(CharType::UTF8(UTF8Data {
                data: vec![]
            })))
            .type_string(),
            "(string-utf8 0)"
        );
        assert_eq!(
            Value::Sequence(SequenceData::String(CharType::UTF8(UTF8Data {
                data: vec![vec![0x68], vec![0x65], vec![0x6c], vec![0x6c], vec![0x6f]]
            })))
            .type_string(),
            "(string-utf8 5)"
        );
        assert_eq!(
            Value::Optional(OptionalData { data: None }).type_string(),
            "(optional int)"
        );
        assert_eq!(
            Value::Optional(OptionalData {
                data: Some(Box::new(Value::UInt(0)))
            })
            .type_string(),
            "(optional uint)"
        );
        assert_eq!(
            Value::Response(ResponseData {
                committed: true,
                data: Box::new(Value::UInt(0))
            })
            .type_string(),
            "(response uint int)"
        );
        assert_eq!(
            Value::Response(ResponseData {
                committed: false,
                data: Box::new(Value::UInt(0))
            })
            .type_string(),
            "(response int uint)"
        );
        assert_eq!(
            Value::Sequence(SequenceData::List(ListData {
                data: vec![],
                type_signature: ListTypeData::new_list(TypeSignature::IntType, 0).unwrap()
            }))
            .type_string(),
            "(list 0 int)"
        );
        assert_eq!(
            Value::Sequence(SequenceData::List(ListData {
                data: vec![Value::Int(0), Value::Int(1), Value::Int(2)],
                type_signature: ListTypeData::new_list(TypeSignature::IntType, 3).unwrap()
            }))
            .type_string(),
            "(list 3 int)"
        );
        assert_eq!(
            Value::Tuple(
                TupleData::from_data(vec![
                    ("a".into(), Value::Int(42)),
                    ("b".into(), Value::UInt(42)),
                    ("c".into(), Value::Bool(true)),
                ])
                .unwrap()
            )
            .type_string(),
            "{a: int,b: uint,c: bool,}"
        );
        assert_eq!(
            Value::from(
                PrincipalData::parse_standard_principal(
                    "SM2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQVX8X0G"
                )
                .unwrap()
            )
            .type_string(),
            "principal"
        );
        assert_eq!(
            // (list (ok 0))
            Value::cons_list_unsanitized(vec![Value::okay(Value::Int(0)).unwrap()])
                .unwrap()
                .type_string(),
            "(list 1 (response int int))"
        );
    }
}
