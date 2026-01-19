use clarity::vm::types::{TypeSignature, MAX_VALUE_SIZE};
use walrus::ir::{BinaryOp, InstrSeqType};

use super::{ComplexWord, Word};
use crate::check_args;
use crate::cost::WordCharge;
use crate::wasm_generator::{
    add_placeholder_for_clarity_type, clar2wasm_ty, drop_value, ArgumentsExt, GeneratorError,
    WasmGenerator,
};
use crate::wasm_utils::{check_argument_count, ArgumentCountCheck};

#[derive(Debug)]
pub struct ToConsensusBuff;

impl Word for ToConsensusBuff {
    fn name(&self) -> clarity::vm::ClarityName {
        "to-consensus-buff?".into()
    }
}

impl ComplexWord for ToConsensusBuff {
    fn traverse(
        &self,
        generator: &mut crate::wasm_generator::WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        expr: &clarity::vm::SymbolicExpression,
        args: &[clarity::vm::SymbolicExpression],
    ) -> Result<(), crate::wasm_generator::GeneratorError> {
        check_args!(generator, builder, 1, args.len(), ArgumentCountCheck::Exact);
        let length = generator.module.locals.add(walrus::ValType::I32);

        generator.traverse_args(builder, args)?;

        let ty = generator
            .get_expr_type(args.get_expr(0)?)
            .ok_or_else(|| {
                GeneratorError::TypeError(
                    "to-consensus-buff? value expression must be typed".to_owned(),
                )
            })?
            .clone();

        generator.serialization_size(builder, &ty)?;
        builder.local_set(length);

        self.charge(generator, builder, length)?;

        let expr_ty = generator
            .get_expr_type(expr)
            .ok_or_else(|| {
                GeneratorError::TypeError(
                    "to-consensus-buff? value expression must be typed".to_owned(),
                )
            })?
            .clone();
        let (offset, _) = generator.create_call_stack_local(builder, &expr_ty, false, true);

        // Write the serialized value to the top of the call stack
        generator.serialize_to_memory(builder, offset, 0, &ty)?;
        builder.drop();

        // Check if the serialized value size < MAX_VALUE_SIZE
        builder
            .local_get(length)
            .i32_const(MAX_VALUE_SIZE as i32)
            .binop(walrus::ir::BinaryOp::I32LeU)
            .if_else(
                InstrSeqType::new(
                    &mut generator.module.types,
                    &[],
                    &[
                        walrus::ValType::I32,
                        walrus::ValType::I32,
                        walrus::ValType::I32,
                    ],
                ),
                |then| {
                    then.local_get(offset)
                        .local_get(length)
                        .binop(walrus::ir::BinaryOp::I32Add)
                        .global_set(generator.stack_pointer);

                    then.i32_const(1).local_get(offset).local_get(length);
                },
                |else_| {
                    else_.i32_const(0).i32_const(0).i32_const(0);
                },
            );

        Ok(())
    }
}

#[derive(Debug)]
pub struct FromConsensusBuff;

impl Word for FromConsensusBuff {
    fn name(&self) -> clarity::vm::ClarityName {
        "from-consensus-buff?".into()
    }
}

impl ComplexWord for FromConsensusBuff {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &clarity::vm::SymbolicExpression,
        args: &[clarity::vm::SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 2, args.len(), ArgumentCountCheck::Exact);

        // Rather than parsing the type from args[0], we can just use the type
        // of this expression.
        let ty = generator
            .get_expr_type(_expr)
            .ok_or_else(|| {
                GeneratorError::TypeError(
                    "from-consensus-buff? value expression must be typed".to_owned(),
                )
            })?
            .clone();
        let wasm_result_ty = clar2wasm_ty(&ty);
        let value_ty = if let TypeSignature::OptionalType(ref inner) = ty {
            *inner.clone()
        } else {
            return Err(GeneratorError::TypeError(
                "from-consensus-buff? value expression must be an optional type".to_string(),
            ));
        };

        // Traverse the input buffer, leaving the offset and length on the stack.
        generator.traverse_expr(builder, args.get_expr(1)?)?;

        let length = generator.module.locals.add(walrus::ValType::I32);
        builder.local_tee(length);
        self.charge(generator, builder, length)?;

        // TODO: true, true is too big; see issue: #593
        let (offset_result, _len) = generator.create_call_stack_local(builder, &ty, true, true);
        let offset = generator.module.locals.add(walrus::ValType::I32);
        let end = generator.module.locals.add(walrus::ValType::I32);
        builder
            .local_set(end)
            .local_tee(offset)
            .local_get(end)
            .binop(BinaryOp::I32Add)
            .local_set(end);

        // Write the deserialized value on the stack at offset_result
        generator.deserialize_from_memory(builder, offset, end, offset_result, &value_ty)?;

        // If the entire buffer was not consumed, return none.
        builder
            .local_get(end)
            .local_get(offset)
            .binop(BinaryOp::I32Eq)
            .if_else(
                InstrSeqType::new(
                    &mut generator.module.types,
                    &wasm_result_ty,
                    &wasm_result_ty,
                ),
                |_| {
                    // Do nothing, leave the result as-is
                },
                |else_| {
                    // Drop the result and return none
                    drop_value(else_, &ty);
                    add_placeholder_for_clarity_type(else_, &ty);
                },
            );

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    //
    // Module with tests that should only be executed
    // when running Clarity::V2 or Clarity::V3.
    //
    #[cfg(any(feature = "test-clarity-v2", feature = "test-clarity-v3"))]
    #[cfg(test)]
    mod clarity_v2_v3 {

        use std::collections::BTreeSet;
        use std::fmt::Write as _;

        use clarity::vm::types::{BuffData, PrincipalData, SequenceData, TupleData};
        use clarity::vm::Value;
        use hex::FromHex as _;

        use crate::tools::{crosscheck, evaluate};

        #[test]
        fn to_consensus_buff_less_than_one_arg() {
            let result = evaluate("(to-consensus-buff?)");
            assert!(result.is_err());
            assert!(result
                .unwrap_err()
                .to_string()
                .contains("expecting 1 arguments, got 0"));
        }

        #[test]
        fn to_consensus_buff_more_than_one_arg() {
            let result = evaluate("(to-consensus-buff? 1 2)");
            assert!(result.is_err());
            assert!(result
                .unwrap_err()
                .to_string()
                .contains("expecting 1 arguments, got 2"));
        }

        #[test]
        fn to_consensus_buff_int() {
            crosscheck(
                r#"(to-consensus-buff? 42)"#,
                Ok(Some(
                    Value::some(Value::Sequence(SequenceData::Buffer(BuffData {
                        data: Vec::from_hex("000000000000000000000000000000002a").unwrap(),
                    })))
                    .unwrap(),
                )),
            )
        }

        #[test]
        fn to_consensus_buff_uint() {
            crosscheck(
                r#"(to-consensus-buff? u42)"#,
                Ok(Some(
                    Value::some(Value::Sequence(SequenceData::Buffer(BuffData {
                        data: Vec::from_hex("010000000000000000000000000000002a").unwrap(),
                    })))
                    .unwrap(),
                )),
            )
        }

        #[test]
        fn to_consensus_buff_bool() {
            crosscheck(
                "(to-consensus-buff? true)",
                Ok(Some(
                    Value::some(Value::Sequence(SequenceData::Buffer(BuffData {
                        data: Vec::from_hex("03").unwrap(),
                    })))
                    .unwrap(),
                )),
            );
            crosscheck(
                "(to-consensus-buff? false)",
                Ok(Some(
                    Value::some(Value::Sequence(SequenceData::Buffer(BuffData {
                        data: Vec::from_hex("04").unwrap(),
                    })))
                    .unwrap(),
                )),
            );
        }

        #[test]
        fn to_consensus_buff_optional() {
            crosscheck(
                r#"(to-consensus-buff? none)"#,
                Ok(Some(
                    Value::some(Value::Sequence(SequenceData::Buffer(BuffData {
                        data: Vec::from_hex("09").unwrap(),
                    })))
                    .unwrap(),
                )),
            );
            crosscheck(
                r#"(to-consensus-buff? (some 42))"#,
                Ok(Some(
                    Value::some(Value::Sequence(SequenceData::Buffer(BuffData {
                        data: Vec::from_hex("0a000000000000000000000000000000002a").unwrap(),
                    })))
                    .unwrap(),
                )),
            )
        }

        #[test]
        fn to_consensus_buff_response() {
            crosscheck(
                r#"(to-consensus-buff? (ok 42))"#,
                Ok(Some(
                    Value::some(Value::Sequence(SequenceData::Buffer(BuffData {
                        data: Vec::from_hex("07000000000000000000000000000000002a").unwrap(),
                    })))
                    .unwrap(),
                )),
            );
            crosscheck(
                r#"(to-consensus-buff? (err u123))"#,
                Ok(Some(
                    Value::some(Value::Sequence(SequenceData::Buffer(BuffData {
                        data: Vec::from_hex("08010000000000000000000000000000007b").unwrap(),
                    })))
                    .unwrap(),
                )),
            )
        }

        #[test]
        fn to_consensus_buff_tuple() {
            crosscheck(r#"(to-consensus-buff? {foo: 123, bar: u789})"#,
            Ok(Some(
                Value::some(Value::Sequence(SequenceData::Buffer(BuffData {
                    data: Vec::from_hex("0c0000000203626172010000000000000000000000000000031503666f6f000000000000000000000000000000007b").unwrap()
                }))).unwrap()
            ))
        )
        }

        #[test]
        fn to_consensus_buff_string_utf8() {
            crosscheck(
                r#"(to-consensus-buff? u"Hello, World!")"#,
                Ok(Some(
                    Value::some(Value::Sequence(SequenceData::Buffer(BuffData {
                        data: Vec::from_hex("0e0000000d48656c6c6f2c20576f726c6421").unwrap(),
                    })))
                    .unwrap(),
                )),
            )
        }

        #[test]
        fn to_consensus_buff_string_utf8_b() {
            // helŁo world 愛🦊
            crosscheck(
                r#"(to-consensus-buff? u"hel\u{0141}o world \u{611b}\u{1f98a}")"#,
                Ok(Some(
                    Value::some(Value::Sequence(SequenceData::Buffer(BuffData {
                        data: Vec::from_hex("0e0000001468656cc5816f20776f726c6420e6849bf09fa68a")
                            .unwrap(),
                    })))
                    .unwrap(),
                )),
            )
        }

        #[test]
        fn to_consensus_buff_string_utf8_empty() {
            crosscheck(
                r#"(to-consensus-buff? u"")"#,
                Ok(Some(
                    Value::some(Value::Sequence(SequenceData::Buffer(BuffData {
                        data: Vec::from_hex("0e00000000").unwrap(),
                    })))
                    .unwrap(),
                )),
            );
        }

        #[test]
        fn to_consensus_buff_string_ascii() {
            crosscheck(
                r#"(to-consensus-buff? "Hello, World!")"#,
                Ok(Some(
                    Value::some(Value::Sequence(SequenceData::Buffer(BuffData {
                        data: Vec::from_hex("0d0000000d48656c6c6f2c20576f726c6421").unwrap(),
                    })))
                    .unwrap(),
                )),
            )
        }

        #[test]
        fn to_consensus_buff_buffer() {
            crosscheck(
                r#"(to-consensus-buff? 0x12345678)"#,
                Ok(Some(
                    Value::some(Value::Sequence(SequenceData::Buffer(BuffData {
                        data: Vec::from_hex("020000000412345678").unwrap(),
                    })))
                    .unwrap(),
                )),
            )
        }

        #[test]
        fn to_consensus_buff_list() {
            crosscheck(r#"(to-consensus-buff? (list 1 2 3 4))"#,
            Ok(Some(
                Value::some(Value::Sequence(SequenceData::Buffer(BuffData {
                    data: Vec::from_hex("0b000000040000000000000000000000000000000001000000000000000000000000000000000200000000000000000000000000000000030000000000000000000000000000000004").unwrap()
                })))
                .unwrap()
            ))
        )
        }

        //--- `from-consensus-buff?` tests

        #[test]
        fn from_consensus_buff_less_than_two_args() {
            let result = evaluate("(from-consensus-buff? int)");
            assert!(result.is_err());
            assert!(result
                .unwrap_err()
                .to_string()
                .contains("expecting 2 arguments, got 1"));
        }

        #[test]
        fn from_consensus_buff_more_than_two_args() {
            let result = evaluate("(from-consensus-buff? int 0x000000000000000000000000000001e240 0x000000000000000000000000000001e240)");
            assert!(result.is_err());
            assert!(result
                .unwrap_err()
                .to_string()
                .contains("expecting 2 arguments, got 3"));
        }

        #[test]
        fn from_consensus_buff_int() {
            crosscheck(
                r#"(from-consensus-buff? int 0x000000000000000000000000000001e240)"#,
                Ok(Some(Value::some(Value::Int(123456)).unwrap())),
            )
        }

        #[test]
        fn from_consensus_buff_int_bad_prefix() {
            crosscheck(
                r#"(from-consensus-buff? int 0x0100000000000000000000000001e240)"#,
                Ok(Some(Value::none())),
            )
        }

        #[test]
        fn from_consensus_buff_int_short() {
            crosscheck(
                r#"(from-consensus-buff? int 0x0000000000000000000000000001e240)"#,
                Ok(Some(Value::none())),
            )
        }

        #[test]
        fn from_consensus_buff_int_long() {
            crosscheck(
                r#"(from-consensus-buff? int 0x000000000000000000000000000001e24000)"#,
                Ok(Some(Value::none())),
            )
        }

        #[test]
        fn from_consensus_buff_uint() {
            crosscheck(
                r#"(from-consensus-buff? uint 0x010000000000000000000000000001e240)"#,
                Ok(Some(Value::some(Value::UInt(123456)).unwrap())),
            );
        }

        #[test]
        fn from_consensus_buff_uint_bad_prefix() {
            crosscheck(
                r#"(from-consensus-buff? uint 0x0000000000000000000000000001e240)"#,
                Ok(Some(Value::none())),
            )
        }

        #[test]
        fn from_consensus_buff_uint_short() {
            crosscheck(
                r#"(from-consensus-buff? uint 0x0100000000000000000000000001e240)"#,
                Ok(Some(Value::none())),
            )
        }

        #[test]
        fn from_consensus_buff_uint_long() {
            crosscheck(
                r#"(from-consensus-buff? uint 0x010000000000000000000000000001e24000)"#,
                Ok(Some(Value::none())),
            )
        }

        #[test]
        fn from_consensus_buff_standard_principal() {
            crosscheck(
                r#"(from-consensus-buff? principal 0x051a7321b74e2b6a7e949e6c4ad313035b1665095017)"#,
                Ok(Some(
                    Value::some(Value::Principal(
                        PrincipalData::parse_standard_principal(
                            "ST1SJ3DTE5DN7X54YDH5D64R3BCB6A2AG2ZQ8YPD5",
                        )
                        .unwrap()
                        .into(),
                    ))
                    .unwrap(),
                )),
            )
        }

        #[test]
        fn from_consensus_buff_principal_bad_prefix() {
            crosscheck(
                r#"(from-consensus-buff? principal 0x071a7321b74e2b6a7e949e6c4ad313035b1665095017)"#,
                Ok(Some(Value::none())),
            )
        }

        #[test]
        fn from_consensus_buff_standard_principal_short() {
            crosscheck(
                r#"(from-consensus-buff? principal 0x051a7321b74e2b6a7e949e6c4ad313035b16650950)"#,
                Ok(Some(Value::none())),
            )
        }

        #[test]
        fn from_consensus_buff_standard_principal_long() {
            crosscheck(
                r#"(from-consensus-buff? principal 0x051a7321b74e2b6a7e949e6c4ad313035b1665095017ff)"#,
                Ok(Some(Value::none())),
            )
        }

        #[test]
        fn from_consensus_buff_contract_principal() {
            crosscheck(
                r#"(from-consensus-buff? principal 0x061a99e2ec69ac5b6e67b4e26edd0e2c1c1a6b9bbd230d66756e6374696f6e2d6e616d65)"#,
                Ok(Some(
                    Value::some(Value::Principal(
                        PrincipalData::parse_qualified_contract_principal(
                            "ST2CY5V39NHDPWSXMW9QDT3HC3GD6Q6XX4CFRK9AG.function-name",
                        )
                        .unwrap(),
                    ))
                    .unwrap(),
                )),
            )
        }

        #[test]
        fn from_consensus_buff_contract_principal_short() {
            crosscheck(
                r#"(from-consensus-buff? principal 0x061a99e2ec69ac5b6e67b4e26edd0e2c1c1a6b9bbd230d66756e6374696f6e2d6e616d)"#,
                Ok(Some(Value::none())),
            )
        }

        #[test]
        fn from_consensus_buff_contract_principal_long() {
            crosscheck(
                r#"(from-consensus-buff? principal 0x061a99e2ec69ac5b6e67b4e26edd0e2c1c1a6b9bbd230d66756e6374696f6e2d6e616d6565)"#,
                Ok(Some(Value::none())),
            )
        }

        #[test]
        fn from_consensus_buff_bool_true() {
            crosscheck(
                r#"(from-consensus-buff? bool 0x03)"#,
                Ok(Some(Value::some(Value::Bool(true)).unwrap())),
            )
        }

        #[test]
        fn from_consensus_buff_bool_false() {
            crosscheck(
                r#"(from-consensus-buff? bool 0x04)"#,
                Ok(Some(Value::some(Value::Bool(false)).unwrap())),
            )
        }

        #[test]
        fn from_consensus_buff_bool_bad_prefix() {
            crosscheck(
                r#"(from-consensus-buff? bool 0x02)"#,
                Ok(Some(Value::none())),
            )
        }

        #[test]
        fn from_consensus_buff_bool_short() {
            crosscheck(r#"(from-consensus-buff? bool 0x)"#, Ok(Some(Value::none())))
        }

        #[test]
        fn from_consensus_buff_bool_long() {
            crosscheck(
                r#"(from-consensus-buff? bool 0x0404)"#,
                Ok(Some(Value::none())),
            )
        }

        #[test]
        fn from_consensus_buff_optional_int_none() {
            crosscheck(
                r#"(from-consensus-buff? (optional int) 0x09)"#,
                Ok(Some(Value::some(Value::none()).unwrap())),
            )
        }

        #[test]
        fn from_consensus_buff_optional_bad_prefix() {
            crosscheck(
                r#"(from-consensus-buff? (optional int) 0x00ffffffffffffffffffffffffffffffd6)"#,
                Ok(Some(Value::none())),
            )
        }

        #[test]
        fn from_consensus_buff_optional_int_some() {
            crosscheck(
                r#"(from-consensus-buff? (optional int) 0x0a00ffffffffffffffffffffffffffffffd6)"#,
                Ok(Some(
                    Value::some(Value::some(Value::Int(-42)).unwrap()).unwrap(),
                )),
            )
        }

        #[test]
        fn from_consensus_buff_optional_bool_some() {
            crosscheck(
                r#"(from-consensus-buff? (optional bool) 0x0a03)"#,
                Ok(Some(
                    Value::some(Value::some(Value::Bool(true)).unwrap()).unwrap(),
                )),
            )
        }

        #[test]
        fn from_consensus_buff_optional_int_some_invalid() {
            crosscheck(
                r#"(from-consensus-buff? (optional int) 0x0a02ffffffffffffffffffffffffffffffd6)"#,
                Ok(Some(Value::none())),
            )
        }

        #[test]
        fn from_consensus_buff_optional_int_some_long() {
            crosscheck(
                r#"(from-consensus-buff? (optional int) 0x0a00ffffffffffffffffffffffffffffffd600)"#,
                Ok(Some(Value::none())),
            )
        }

        #[test]
        fn from_consensus_buff_optional_int_some_short() {
            crosscheck(
                r#"(from-consensus-buff? (optional int) 0x0a00ffffffffffffffffffffffffffffd6)"#,
                Ok(Some(Value::none())),
            )
        }

        #[test]
        fn from_consensus_buff_response_simple_ok() {
            crosscheck(
                r#"(from-consensus-buff? (response int int) 0x07000000000000000000000000000000007b)"#,
                Ok(Some(
                    Value::some(Value::okay(Value::Int(123)).unwrap()).unwrap(),
                )),
            )
        }

        #[test]
        fn from_consensus_buff_response_simple_err() {
            crosscheck(
                r#"(from-consensus-buff? (response int uint) 0x0801000000000000000000000000000001c8)"#,
                Ok(Some(Value::some(Value::err_uint(456)).unwrap())),
            )
        }

        #[test]
        fn from_consensus_buff_response_bad_prefix() {
            crosscheck(
                r#"(from-consensus-buff? (response int int) 0x000000000000000000000000000000007b)"#,
                Ok(Some(Value::none())),
            )
        }

        #[test]
        fn from_consensus_buff_response_short() {
            crosscheck(
                r#"(from-consensus-buff? (response int int) 0x070000000000000000000000000000007b)"#,
                Ok(Some(Value::none())),
            )
        }

        #[test]
        fn from_consensus_buff_response_long() {
            crosscheck(
                r#"(from-consensus-buff? (response int bool) 0x07000000000000000000000000000000007b03)"#,
                Ok(Some(Value::none())),
            )
        }

        #[test]
        fn from_consensus_buff_response_ok() {
            crosscheck(
            r#"(from-consensus-buff? (response (string-ascii 128) uint) 0x070d000000455468652054696d65732030332f4a616e2f32303039204368616e63656c6c6f72206f6e206272696e6b206f66207365636f6e64206261696c6f757420666f722062616e6b73)"#,
            Ok(Some(
                Value::some(
                    Value::okay(
                        Value::string_ascii_from_bytes(
                            "The Times 03/Jan/2009 Chancellor on brink of second bailout for banks"
                                .to_string()
                                .into_bytes(),
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                )
                .unwrap(),
            )),
        )
        }

        #[test]
        fn from_consensus_buff_buffer_exact_size() {
            crosscheck(
                r#"(from-consensus-buff? (buff 16) 0x0200000010000102030405060708090a0b0c0d0e0f)"#,
                Ok(Some(
                    Value::some(
                        Value::buff_from(vec![
                            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b,
                            0x0c, 0x0d, 0x0e, 0x0f,
                        ])
                        .unwrap(),
                    )
                    .unwrap(),
                )),
            )
        }

        #[test]
        fn from_consensus_buff_buffer_empty() {
            crosscheck(
                r#"(from-consensus-buff? (buff 16) 0x0200000000)"#,
                Ok(Some(
                    Value::some(Value::buff_from(vec![]).unwrap()).unwrap(),
                )),
            )
        }

        #[test]
        fn from_consensus_buff_buffer_smaller_than_type() {
            crosscheck(
                r#"(from-consensus-buff? (buff 16) 0x02000000080001020304050607)"#,
                Ok(Some(
                    Value::some(
                        Value::buff_from(vec![0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07])
                            .unwrap(),
                    )
                    .unwrap(),
                )),
            )
        }

        #[test]
        fn from_consensus_buff_buffer_smaller_than_size() {
            crosscheck(
                r#"(from-consensus-buff? (buff 16) 0x020000000800010203040506)"#,
                Ok(Some(Value::none())),
            )
        }

        #[test]
        fn from_consensus_buff_buffer_larger_than_size() {
            crosscheck(
                r#"(from-consensus-buff? (buff 16) 0x0200000008000102030405060708)"#,
                Ok(Some(Value::none())),
            )
        }

        #[test]
        fn from_consensus_buff_buffer_larger_than_type() {
            crosscheck(
                r#"(from-consensus-buff? (buff 8) 0x0200000009000102030405060708)"#,
                Ok(Some(Value::none())),
            )
        }

        #[test]
        fn from_consensus_buff_string_utf8_exact_size() {
            crosscheck(
                r#"(from-consensus-buff? (string-utf8 13) 0x0e0000000d48656c6c6f2c20776f726c6421)"#,
                Ok(Some(
                    Value::some(Value::string_utf8_from_bytes("Hello, world!".into()).unwrap())
                        .unwrap(),
                )),
            )
        }

        #[test]
        fn from_consensus_buff_string_utf8_b_exact_size() {
            crosscheck(
                r#"(from-consensus-buff? (string-utf8 20) 0x0e0000001468656cc5816f20776f726c6420e6849bf09fa68a)"#,
                Ok(Some(
                    Value::some(Value::string_utf8_from_bytes("helŁo world 愛🦊".into()).unwrap())
                        .unwrap(),
                )),
            )
        }

        #[test]
        fn from_consensus_buff_string_utf8_empty() {
            crosscheck(
                r#"(from-consensus-buff? (string-utf8 20) 0x0e00000000)"#,
                Ok(Some(
                    Value::some(Value::string_utf8_from_bytes("".into()).unwrap()).unwrap(),
                )),
            );
        }

        #[test]
        fn from_consensus_buff_string_utf8_invalid_initial_byte_pattern() {
            // Bytes in the range 0x80 to 0xBF are continuation bytes and should not appear as the initial byte in a UTF-8 sequence.
            // Bytes 0xF5 to 0xFF are not valid initial bytes in UTF-8.
            crosscheck(
                // invalid initial byte 0x80
                r#"(from-consensus-buff? (string-utf8 13) 0x0e0000000d8048656c6c6f2c20776f726c64)"#,
                Ok(Some(Value::none())),
            );

            crosscheck(
                // invalid initial byte 0xBF
                r#"(from-consensus-buff? (string-utf8 13) 0x0e0000000dbf48656c6c6f2c20776f726c64)"#,
                Ok(Some(Value::none())),
            );

            crosscheck(
                // invalid initial byte 0xF5
                r#"(from-consensus-buff? (string-utf8 13) 0x0e0000000d80f5656c6c6f2c20776f726c64)"#,
                Ok(Some(Value::none())),
            );

            crosscheck(
                // invalid initial byte 0xFF
                r#"(from-consensus-buff? (string-utf8 13) 0x0e0000000d80ff656c6c6f2c20776f726c64)"#,
                Ok(Some(Value::none())),
            );
        }

        #[test]
        fn from_consensus_buff_string_utf8_invalid_surrogate_code_point() {
            // Unicode surrogate halves (U+D800 to U+DFFF) are not valid code points themselves and should not appear in UTF-8 encoded data.
            crosscheck(
                // invalid surrogate code point U+D800 (EDA080)
                r#"(from-consensus-buff? (string-utf8 20) 0x0e0000000feda08048656c6c6f2c20776f726c64)"#,
                Ok(Some(Value::none())),
            )
        }

        #[test]
        fn from_consensus_buff_string_utf8_invalid_continuation_bytes() {
            // Test invalid utf-8 where continuation bytes do not conform to the 10xx xxxx pattern (i.e., they should not be in the range 0x80 to 0xBF)
            crosscheck(
                // 2-byte sequence `C2 7F` (second byte is not a continuation byte)
                r#"(from-consensus-buff? (string-utf8 20) 0x0e00000002c27f)"#,
                Ok(Some(Value::none())),
            );

            crosscheck(
                // 3-byte sequence `E0 A0 7F` (third byte is not a continuation byte)
                r#"(from-consensus-buff? (string-utf8 13) 0x0e00000003e0a07f)"#,
                Ok(Some(Value::none())),
            );

            crosscheck(
                // 3-byte sequence `E0 7F 80` (second byte is not a continuation byte)
                r#"(from-consensus-buff? (string-utf8 13) 0x0e00000003e07f80)"#,
                Ok(Some(Value::none())),
            );

            crosscheck(
                // 4-byte sequence `F0 90 7F 80` (third byte is not a continuation byte)
                r#"(from-consensus-buff? (string-utf8 13) 0x0e00000004f0907f80)"#,
                Ok(Some(Value::none())),
            );

            crosscheck(
                // 4-byte sequence `F0 90 80 7F` (fourth byte is not a continuation byte)
                r#"(from-consensus-buff? (string-utf8 13) 0x0e00000004f090807f)"#,
                Ok(Some(Value::none())),
            );
        }

        #[test]
        fn from_consensus_buff_string_utf8_overlong_encoding() {
            // Test invalid utf-8 where code points are encoded using more bytes than required
            crosscheck(
                // ASCII 'A' (U+0041) is normally `41` in hex, overlong 2-byte encoding could be `C1 81`
                r#"(from-consensus-buff? (string-utf8 20) 0x0e00000002c181)"#,
                Ok(Some(Value::none())),
            )
        }

        #[test]
        fn from_consensus_buff_string_utf8_unicode_range_check() {
            // Test invalid utf-8 where code points is above U+10FFFF (invalid in Unicode)
            crosscheck(
                // `F4908080`
                r#"(from-consensus-buff? (string-utf8 20) 0x0e00000004f4908080)"#,
                Ok(Some(Value::none())),
            )
        }

        #[test]
        fn from_consensus_buff_string_utf8_incomplete_sequence() {
            // Test buffer size validation where initial bytes indcate a longer sequence than is present in the buffer
            crosscheck(
                // Incomplete 2-byte sequence: string starts a 2-byte sequence but is only 1 byte long `C2`
                r#"(from-consensus-buff? (string-utf8 20) 0x0e00000001c2)"#,
                Ok(Some(Value::none())),
            )
        }

        #[test]
        fn from_consensus_buff_string_ascii_exact_size() {
            crosscheck(
                r#"(from-consensus-buff? (string-ascii 13) 0x0d0000000d48656c6c6f2c20776f726c6421)"#,
                Ok(Some(
                    Value::some(
                        Value::string_ascii_from_bytes("Hello, world!".to_string().into_bytes())
                            .unwrap(),
                    )
                    .unwrap(),
                )),
            )
        }

        #[test]
        fn from_consensus_buff_string_ascii_empty() {
            crosscheck(
                r#"(from-consensus-buff? (string-ascii 16) 0x0d00000000)"#,
                Ok(Some(
                    Value::some(Value::string_ascii_from_bytes(vec![]).unwrap()).unwrap(),
                )),
            )
        }

        #[test]
        fn from_consensus_buff_string_ascii_smaller_than_type() {
            crosscheck(
                r#"(from-consensus-buff? (string-ascii 13) 0x0d00000008686920776f726c64)"#,
                Ok(Some(
                    Value::some(
                        Value::string_ascii_from_bytes("hi world".to_string().into_bytes())
                            .unwrap(),
                    )
                    .unwrap(),
                )),
            )
        }

        #[test]
        fn from_consensus_buff_string_ascii_all_chars() {
            let all_chars = "\t\n\x0c\r !\"#$%&'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~";
            let snippet = "(from-consensus-buff? (string-ascii 256) 0x0d00000063090a0c0d202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f606162636465666768696a6b6c6d6e6f707172737475767778797a7b7c7d7e)";
            crosscheck(
                snippet,
                Ok(Some(
                    Value::some(
                        Value::string_ascii_from_bytes(all_chars.bytes().collect()).unwrap(),
                    )
                    .unwrap(),
                )),
            )
        }

        #[test]
        fn from_consensus_buff_string_ascii_all_invalid_chars() {
            let valid_chars: BTreeSet<u8> = b"\t\n\x0c\r !\"#$%&'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~".iter().copied().collect();
            let all_u8: BTreeSet<u8> = (u8::MIN..=u8::MAX).collect();
            let mut counter = 0;

            // Much faster to compute the result of one crosscheck on a list of x elements than the results of x crosschecks.
            let mut snippet = "(list".to_owned();
            for &c in all_u8.difference(&valid_chars) {
                write!(
                    &mut snippet,
                    " (from-consensus-buff? (string-ascii 1) 0x0d00000001{c:02x})"
                )
                .unwrap();
                counter += 1;
            }
            snippet += ")";

            crosscheck(
                &snippet,
                Ok(Some(
                    Value::cons_list_unsanitized(vec![Value::none(); counter]).unwrap(),
                )),
            );
        }

        #[test]
        fn from_consensus_buff_string_ascii_smaller_than_size() {
            crosscheck(
                r#"(from-consensus-buff? (string-ascii 13) 0x0d0000000d48656c6c6f2c20776f726c64)"#,
                Ok(Some(Value::none())),
            )
        }

        #[test]
        fn from_consensus_buff_string_ascii_larger_than_size() {
            crosscheck(
                r#"(from-consensus-buff? (string-ascii 13) 0x0d0000000d48656c6c6f2c20776f726c642121)"#,
                Ok(Some(Value::none())),
            )
        }

        #[test]
        fn from_consensus_buff_string_ascii_larger_than_type() {
            crosscheck(
                r#"(from-consensus-buff? (string-ascii 8) 0x0d0000000d48656c6c6f2c20776f726c6421)"#,
                Ok(Some(Value::none())),
            )
        }

        #[test]
        fn from_consensus_buff_string_ascii_invalid_char() {
            crosscheck(
                r#"(from-consensus-buff? (string-ascii 13) 0x0d0000000d48656c6c6f2c20776f726c6401)"#,
                Ok(Some(Value::none())),
            )
        }

        #[test]
        fn from_consensus_buff_list_int() {
            crosscheck(
                r#"(from-consensus-buff? (list 8 int) 0x0b00000003000000000000000000000000000000000100000000000000000000000000000000020000000000000000000000000000000003)"#,
                Ok(Some(
                    Value::some(
                        Value::cons_list_unsanitized(vec![
                            Value::Int(1),
                            Value::Int(2),
                            Value::Int(3),
                        ])
                        .unwrap(),
                    )
                    .unwrap(),
                )),
            )
        }

        #[test]
        fn from_consensus_buff_list_int_shorter_than_size() {
            crosscheck(
                r#"(from-consensus-buff? (list 8 int) 0x0b0000000300000000000000000000000000000000010000000000000000000000000000000002)"#,
                Ok(Some(Value::none())),
            )
        }

        #[test]
        fn from_consensus_buff_list_int_larger_than_size() {
            crosscheck(
                r#"(from-consensus-buff? (list 8 int) 0x0b000000030000000000000000000000000000000001000000000000000000000000000000000200000000000000000000000000000000030000000000000000000000000000000004)"#,
                Ok(Some(Value::none())),
            )
        }

        #[test]
        fn from_consensus_buff_list_int_larger_than_type() {
            crosscheck(
                r#"(from-consensus-buff? (list 2 int) 0x0b000000040000000000000000000000000000000001000000000000000000000000000000000200000000000000000000000000000000030000000000000000000000000000000004)"#,
                Ok(Some(Value::none())),
            );
        }

        #[test]
        fn from_consensus_buff_list_string() {
            crosscheck(
                r#"(from-consensus-buff? (list 8 (string-ascii 16)) 0x0b000000020d000000075361746f7368690d000000084e616b616d6f746f)"#,
                Ok(Some(
                    Value::some(
                        Value::cons_list_unsanitized(vec![
                            Value::string_ascii_from_bytes("Satoshi".to_string().into_bytes())
                                .unwrap(),
                            Value::string_ascii_from_bytes("Nakamoto".to_string().into_bytes())
                                .unwrap(),
                        ])
                        .unwrap(),
                    )
                    .unwrap(),
                )),
            )
        }

        #[test]
        fn from_consensus_buff_tuple_simple() {
            crosscheck(
                r#"(from-consensus-buff? {n: int} 0x0c00000001016e000000000000000000000000000000002a)"#,
                Ok(Some(
                    Value::some(Value::Tuple(
                        TupleData::from_data(vec![("n".into(), Value::Int(42))]).unwrap(),
                    ))
                    .unwrap(),
                )),
            )
        }

        #[test]
        fn from_consensus_buff_tuple_multiple() {
            crosscheck(
                r#"(from-consensus-buff? {my-number: int, a-string: (string-ascii 16), an-optional: (optional uint)} 0x0c0000000308612d737472696e670d0000000a7975702c2069742069730b616e2d6f7074696f6e616c09096d792d6e756d62657200ffffffffffffffffffffffffffffff85)"#,
                Ok(Some(
                    Value::some(Value::Tuple(
                        // {my-number: -123, a-string: "yup, it is", an-optional: none}
                        TupleData::from_data(vec![
                            ("my-number".into(), Value::Int(-123)),
                            (
                                "a-string".into(),
                                Value::string_ascii_from_bytes(
                                    "yup, it is".to_string().into_bytes(),
                                )
                                .unwrap(),
                            ),
                            ("an-optional".into(), Value::none()),
                        ])
                        .unwrap(),
                    ))
                    .unwrap(),
                )),
            )
        }

        #[test]
        fn from_consensus_buff_tuple_multiple_random_order() {
            // ENCODED: { a-string: "yup, it is", an-optional: none, my-number: -123 }
            crosscheck(
                r#"(from-consensus-buff? {my-number: int, a-string: (string-ascii 16), an-optional: (optional uint)} 0x0c000000030b616e2d6f7074696f6e616c0908612d737472696e670d0000000a7975702c206974206973096d792d6e756d62657200ffffffffffffffffffffffffffffff85)"#,
                Ok(Some(
                    Value::some(Value::Tuple(
                        // {my-number: -123, a-string: "yup, it is", an-optional: none}
                        TupleData::from_data(vec![
                            ("my-number".into(), Value::Int(-123)),
                            (
                                "a-string".into(),
                                Value::string_ascii_from_bytes(
                                    "yup, it is".to_string().into_bytes(),
                                )
                                .unwrap(),
                            ),
                            ("an-optional".into(), Value::none()),
                        ])
                        .unwrap(),
                    ))
                    .unwrap(),
                )),
            )
        }

        #[test]
        fn from_consensus_buff_unallowed_duplicate() {
            // ENCODED: { a:42, a: 1 }
            crosscheck(
                r#"(from-consensus-buff? {a: int} 0x0c000000020161000000000000000000000000000000002a01610000000000000000000000000000000001)"#,
                Ok(Some(Value::none())),
            )
        }

        #[test]
        fn from_consensus_buff_tuple_extra_pair() {
            // ENCODED: { extra: u32, a: 42 }
            crosscheck(
                r#"(from-consensus-buff? {n: int} 0x0c000000020565787472610100000000000000000000000000000020016e000000000000000000000000000000002a)"#,
                Ok(Some(
                    Value::some(Value::Tuple(
                        TupleData::from_data(vec![("n".into(), Value::Int(42))]).unwrap(),
                    ))
                    .unwrap(),
                )),
            )
        }

        #[test]
        fn from_consensus_buff_allow_duplicate_in_extra() {
            // ENCODED: { extra: u32, n: 42, extra: u33 }
            crosscheck(
                r#"(from-consensus-buff? {n: int} 0x0c000000030565787472610100000000000000000000000000000020016e000000000000000000000000000000002a0565787472610100000000000000000000000000000021)"#,
                Ok(Some(
                    Value::some(Value::Tuple(
                        TupleData::from_data(vec![("n".into(), Value::Int(42))]).unwrap(),
                    ))
                    .unwrap(),
                )),
            )
        }

        #[test]
        fn from_consensus_buff_tuple_missing_pair() {
            // ENCODED: { an-optional: none, my-number: -123 }
            crosscheck(
                r#"(from-consensus-buff? {my-number: int, a-string: (string-ascii 16), an-optional: (optional uint)} 0x0c000000020b616e2d6f7074696f6e616c09096d792d6e756d62657200ffffffffffffffffffffffffffffff85)"#,
                Ok(Some(Value::none())),
            )
        }

        #[test]
        fn from_consensus_buff_tuple_invalid_extra() {
            // ENCODED: { extra: *invalid value*, a: 42 }
            crosscheck(
                r#"(from-consensus-buff? {n: int} 0x0c000000020565787472611100000000000000000000000000000020016e000000000000000000000000000000002a)"#,
                Ok(Some(Value::none())),
            )
        }
    }
}
