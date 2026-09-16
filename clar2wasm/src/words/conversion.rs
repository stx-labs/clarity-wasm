use clarity::vm::types::{SequenceSubtype, StringSubtype, TypeSignature};
use clarity_types::ClarityName;
use walrus::ir::{BinaryOp, MemArg, StoreKind, UnaryOp};
use walrus::ValType;

use super::to_ascii::to_ascii_u128;
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

        let signed = match arg_types[0] {
            TypeSignature::IntType => true,
            TypeSignature::UIntType => false,
            _ => {
                return Err(GeneratorError::TypeError(
                    "invalid type for int-to-ascii".to_owned(),
                ));
            }
        };

        let lo = generator.borrow_local(ValType::I64);
        let hi = generator.borrow_local(ValType::I64);
        let length = generator.borrow_local(ValType::I32);

        builder.local_set(*hi).local_set(*lo);

        let negative = if signed {
            let negative = generator.borrow_local(ValType::I32);

            builder
                .local_get(*hi)
                .i64_const(0)
                .binop(BinaryOp::I64LtS)
                .local_set(*negative);

            // Convert the two-word signed value to its unsigned magnitude.
            builder
                .i64_const(0)
                .local_get(*lo)
                .binop(BinaryOp::I64Sub)
                .local_get(*lo)
                .local_get(*negative)
                .select(None)
                .local_set(*lo);
            builder
                .i64_const(0)
                .local_get(*hi)
                .local_get(*lo)
                .i64_const(0)
                .binop(BinaryOp::I64Ne)
                .unop(UnaryOp::I64ExtendUI32)
                .binop(BinaryOp::I64Add)
                .binop(BinaryOp::I64Sub)
                .local_get(*hi)
                .local_get(*negative)
                .select(None)
                .local_set(*hi);

            Some(negative)
        } else {
            None
        };

        let (result_offset, result_size) =
            generator.create_call_stack_local(builder, return_type, false, true);
        builder
            .local_get(result_offset)
            .i32_const(result_size)
            .binop(BinaryOp::I32Add)
            .local_set(result_offset)
            .i32_const(0)
            .local_set(*length);

        to_ascii_u128(generator, builder, *lo, *hi, result_offset, *length)?;

        if let Some(negative) = negative {
            let memory = generator.get_memory()?;

            builder.local_get(*negative).if_else(
                None,
                |then| {
                    then.local_get(result_offset)
                        .i32_const(1)
                        .binop(BinaryOp::I32Sub)
                        .local_tee(result_offset)
                        .i32_const(b'-' as i32)
                        .store(
                            memory,
                            StoreKind::I32_8 { atomic: false },
                            MemArg {
                                align: 1,
                                offset: 0,
                            },
                        )
                        .local_get(*length)
                        .i32_const(1)
                        .binop(BinaryOp::I32Add)
                        .local_set(*length);
                },
                |_else| {},
            );
        }

        builder.local_get(result_offset).local_get(*length);

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

        fn check_uint_to_ascii(num: u128) {
            crosscheck(
                &format!("(int-to-ascii u{num})"),
                Ok(Some(Value::Sequence(SequenceData::String(
                    CharType::ASCII(ASCIIData {
                        data: num.to_string().into_bytes(),
                    }),
                )))),
            )
        }

        fn check_int_to_ascii(num: i128) {
            crosscheck(
                &format!("(int-to-ascii {num})"),
                Ok(Some(Value::Sequence(SequenceData::String(
                    CharType::ASCII(ASCIIData {
                        data: num.to_string().into_bytes(),
                    }),
                )))),
            )
        }

        #[test]
        fn uint_to_ascii() {
            for num in [
                0,
                1,
                42,
                1024,
                184467440737095516156789,
                374467440737095681245698132,
            ] {
                check_uint_to_ascii(num);
            }

            for delta in -5..=5 {
                check_uint_to_ascii((u64::MAX as i128 + delta) as u128);
            }

            for delta in (0..=10).rev() {
                check_uint_to_ascii(u128::MAX - delta);
            }
        }

        #[test]
        fn int_to_ascii() {
            for num in [
                0,
                1,
                42,
                1024,
                184467440737095516156789,
                374467440737095681245698132,
                -1,
                -1024,
                -184467440737095516156789,
                -374467440737095681245698133,
                i128::MIN,
                i128::MAX,
            ] {
                check_int_to_ascii(num);
            }

            for delta in -5..=5 {
                check_int_to_ascii(i64::MAX as i128 + delta);
                check_int_to_ascii(i64::MIN as i128 + delta);
            }
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
