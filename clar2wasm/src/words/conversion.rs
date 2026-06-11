use clarity::vm::types::{SequenceSubtype, StringSubtype, TypeSignature};
use clarity_types::ClarityName;

use super::{SimpleWord, Word};
use crate::cost::WordCharge;
use crate::wasm_generator::GeneratorError;

#[derive(Debug)]
pub struct StringToInt;

impl Word for StringToInt {
    fn name(&self) -> clarity::vm::ClarityName {
        ClarityName::from_literal("string-to-int?")
    }
}

impl SimpleWord for StringToInt {
    fn visit(
        &self,
        generator: &mut crate::wasm_generator::WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        arg_types: &[TypeSignature],
        _return_type: &TypeSignature,
    ) -> Result<(), crate::wasm_generator::GeneratorError> {
        self.charge(generator, builder, 0)?;

        let func_prefix = match &arg_types[0] {
            TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(_))) => {
                "string"
            }
            TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(_))) => {
                "utf8"
            }
            _ => {
                return Err(GeneratorError::TypeError(
                    "impossible type for string-to-int?".to_owned(),
                ))
            }
        };

        let func = generator.func_by_name(&format!("stdlib.{func_prefix}-to-int"));
        builder.call(func);

        Ok(())
    }
}

#[derive(Debug)]
pub struct StringToUint;

impl Word for StringToUint {
    fn name(&self) -> clarity::vm::ClarityName {
        ClarityName::from_literal("string-to-uint?")
    }
}

impl SimpleWord for StringToUint {
    fn visit(
        &self,
        generator: &mut crate::wasm_generator::WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        arg_types: &[TypeSignature],
        _return_type: &TypeSignature,
    ) -> Result<(), crate::wasm_generator::GeneratorError> {
        self.charge(generator, builder, 0)?;

        let func_prefix = match arg_types[0] {
            TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(_))) => {
                "string"
            }
            TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(_))) => {
                "utf8"
            }
            _ => {
                return Err(GeneratorError::TypeError(
                    "impossible type for string-to-int?".to_owned(),
                ))
            }
        };

        let func = generator.func_by_name(&format!("stdlib.{func_prefix}-to-uint"));

        builder.call(func);

        Ok(())
    }
}

#[derive(Debug)]
pub struct IntToAscii;

impl Word for IntToAscii {
    fn name(&self) -> clarity::vm::ClarityName {
        ClarityName::from_literal("int-to-ascii")
    }
}

impl SimpleWord for IntToAscii {
    fn visit(
        &self,
        generator: &mut crate::wasm_generator::WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        arg_types: &[TypeSignature],
        return_type: &TypeSignature,
    ) -> Result<(), crate::wasm_generator::GeneratorError> {
        self.charge(generator, builder, 0)?;

        let type_prefix = match arg_types[0] {
            TypeSignature::IntType => "int",
            TypeSignature::UIntType => "uint",
            _ => {
                return Err(GeneratorError::TypeError(
                    "invalid type for int-to-ascii".to_owned(),
                ));
            }
        };

        let (result_offset, _) =
            generator.create_call_stack_local(builder, return_type, false, true);
        builder.local_get(result_offset);

        let func = generator.func_by_name(&format!("stdlib.{type_prefix}-to-string"));

        builder.call(func);

        Ok(())
    }
}

#[derive(Debug)]
pub struct IntToUtf8;

impl Word for IntToUtf8 {
    fn name(&self) -> clarity::vm::ClarityName {
        ClarityName::from_literal("int-to-utf8")
    }
}

impl SimpleWord for IntToUtf8 {
    fn visit(
        &self,
        generator: &mut crate::wasm_generator::WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        arg_types: &[TypeSignature],
        return_type: &TypeSignature,
    ) -> Result<(), GeneratorError> {
        self.charge(generator, builder, 0)?;

        let type_prefix = match arg_types[0] {
            TypeSignature::IntType => "int",
            TypeSignature::UIntType => "uint",
            _ => {
                return Err(GeneratorError::TypeError(
                    "invalid type for int-to-utf8".to_owned(),
                ));
            }
        };

        let (result_offset, _) =
            generator.create_call_stack_local(builder, return_type, false, true);
        builder.local_get(result_offset);

        let func = generator.func_by_name(&format!("stdlib.{type_prefix}-to-utf8"));

        builder.call(func);

        Ok(())
    }
}

#[cfg(not(feature = "test-clarity-v1"))]
#[cfg(test)]
mod tests {
    #[cfg(test)]
    mod clarity_v2_v3 {
        use clarity::vm::types::{ASCIIData, CharType, SequenceData, UTF8Data};
        use clarity::vm::Value;

        use crate::tools::crosscheck;

        #[test]
        fn valid_string_to_int() {
            crosscheck(
                r#"(string-to-int? "1234567")"#,
                Ok(Some(Value::some(Value::Int(1234567)).unwrap())),
            )
        }

        #[test]
        fn valid_negative_string_to_int() {
            crosscheck(
                r#"(string-to-int? "-1234567")"#,
                Ok(Some(Value::some(Value::Int(-1234567)).unwrap())),
            )
        }

        #[test]
        fn invalid_string_to_int() {
            crosscheck(r#"(string-to-int? "0xabcd")"#, Ok(Some(Value::none())))
        }

        #[test]
        fn valid_string_to_uint() {
            crosscheck(
                r#"(string-to-uint? "98765")"#,
                Ok(Some(Value::some(Value::UInt(98765)).unwrap())),
            )
        }

        #[test]
        fn invalid_string_to_uint() {
            crosscheck(r#"(string-to-uint? "0xabcd")"#, Ok(Some(Value::none())))
        }

        #[test]
        fn valid_utf8_to_int() {
            crosscheck(
                r#"(string-to-int? u"1234567")"#,
                Ok(Some(Value::some(Value::Int(1234567)).unwrap())),
            )
        }

        #[test]
        fn valid_negative_utf8_to_int() {
            crosscheck(
                r#"(string-to-int? u"-1234567")"#,
                Ok(Some(Value::some(Value::Int(-1234567)).unwrap())),
            )
        }

        #[test]
        fn invalid_utf8_to_int() {
            crosscheck(r#"(string-to-int? u"0xabcd")"#, Ok(Some(Value::none())));
        }

        #[test]
        fn valid_utf8_to_uint() {
            crosscheck(
                r#"(string-to-uint? u"98765")"#,
                Ok(Some(Value::some(Value::UInt(98765)).unwrap())),
            )
        }

        #[test]
        fn invalid_utf8_to_uint() {
            crosscheck(r#"(string-to-uint? u"0xabcd")"#, Ok(Some(Value::none())))
        }

        #[test]
        fn uint_to_string() {
            crosscheck(
                r#"(int-to-ascii u42)"#,
                Ok(Some(Value::Sequence(SequenceData::String(
                    CharType::ASCII(ASCIIData {
                        data: "42".bytes().collect(),
                    }),
                )))),
            )
        }

        #[test]
        fn positive_int_to_string() {
            crosscheck(
                r#"(int-to-ascii 2048)"#,
                Ok(Some(Value::Sequence(SequenceData::String(
                    CharType::ASCII(ASCIIData {
                        data: "2048".bytes().collect(),
                    }),
                )))),
            )
        }

        #[test]
        fn negative_int_to_string() {
            crosscheck(
                r#"(int-to-ascii -2048)"#,
                Ok(Some(Value::Sequence(SequenceData::String(
                    CharType::ASCII(ASCIIData {
                        data: "-2048".bytes().collect(),
                    }),
                )))),
            )
        }

        #[test]
        fn uint_to_utf8() {
            crosscheck(
                r#"(int-to-utf8 u42)"#,
                Ok(Some(Value::Sequence(SequenceData::String(CharType::UTF8(
                    UTF8Data {
                        data: "42".bytes().map(|b| vec![b]).collect(),
                    },
                ))))),
            )
        }

        #[test]
        fn positive_int_to_utf8() {
            crosscheck(
                r#"(int-to-utf8 2048)"#,
                Ok(Some(Value::Sequence(SequenceData::String(CharType::UTF8(
                    UTF8Data {
                        data: "2048".bytes().map(|b| vec![b]).collect(),
                    },
                ))))),
            );
        }

        #[test]
        fn negative_int_to_utf8() {
            crosscheck(
                r#"(int-to-utf8 -2048)"#,
                Ok(Some(Value::Sequence(SequenceData::String(CharType::UTF8(
                    UTF8Data {
                        data: "-2048".bytes().map(|b| vec![b]).collect(),
                    },
                ))))),
            )
        }
    }
}
