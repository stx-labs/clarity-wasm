use clarity::vm::clarity_wasm::STANDARD_PRINCIPAL_BYTES;
use clarity::vm::types::TypeSignature;
use clarity::vm::{ClarityName, SymbolicExpression};
use clarity::{
    C32_ADDRESS_VERSION_MAINNET_MULTISIG, C32_ADDRESS_VERSION_MAINNET_SINGLESIG,
    C32_ADDRESS_VERSION_TESTNET_MULTISIG, C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
};
use walrus::ir::{BinaryOp, ExtendedLoad, InstrSeqType, LoadKind, MemArg};
use walrus::{LocalId, ValType};

use super::{ComplexWord, SimpleWord, Word};
use crate::check_args;
use crate::cost::WordCharge;
use crate::wasm_generator::{
    add_placeholder_for_clarity_type, clar2wasm_ty, ArgumentsExt, GeneratorError, WasmGenerator,
};
use crate::wasm_utils::{check_argument_count, ArgumentCountCheck};

#[derive(Debug)]
pub struct IsStandard;

impl Word for IsStandard {
    fn name(&self) -> ClarityName {
        "is-standard".into()
    }
}

impl SimpleWord for IsStandard {
    fn visit(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _arg_types: &[TypeSignature],
        _return_type: &TypeSignature,
    ) -> Result<(), GeneratorError> {
        self.charge(generator, builder, 0)?;

        // Drop the length
        builder.drop();

        // Read the version byte from the principal in memory
        builder.load(
            generator.get_memory()?,
            walrus::ir::LoadKind::I32_8 {
                kind: walrus::ir::ExtendedLoad::ZeroExtend,
            },
            MemArg {
                align: 1,
                offset: 0,
            },
        );

        // Save the version byte in a local
        let version_local = generator.module.locals.add(ValType::I32);
        builder.local_tee(version_local);

        // TODO: It would be nice if this was a global variable that gets set
        //       at compile time, instead of requiring a host-interface call.
        // Check if we are in mainnet (leaves a boolean on the stack)
        builder.call(generator.func_by_name("stdlib.is_in_mainnet"));

        builder.if_else(
            InstrSeqType::new(
                &mut generator.module.types,
                &[ValType::I32],
                &[ValType::I32],
            ),
            |then| {
                then.i32_const(C32_ADDRESS_VERSION_MAINNET_MULTISIG as i32)
                    .binop(BinaryOp::I32Eq);
                then.local_get(version_local)
                    .i32_const(C32_ADDRESS_VERSION_MAINNET_SINGLESIG as i32)
                    .binop(BinaryOp::I32Eq);
                then.binop(BinaryOp::I32Or);
            },
            |else_| {
                else_
                    .i32_const(C32_ADDRESS_VERSION_TESTNET_MULTISIG as i32)
                    .binop(BinaryOp::I32Eq);
                else_
                    .local_get(version_local)
                    .i32_const(C32_ADDRESS_VERSION_TESTNET_SINGLESIG as i32)
                    .binop(BinaryOp::I32Eq);
                else_.binop(BinaryOp::I32Or);
            },
        );

        Ok(())
    }
}

#[derive(Debug)]
pub struct Construct;

impl Word for Construct {
    fn name(&self) -> ClarityName {
        "principal-construct?".into()
    }
}

impl ComplexWord for Construct {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(
            generator,
            builder,
            2,
            args.len(),
            ArgumentCountCheck::AtLeast
        );
        check_args!(
            generator,
            builder,
            3,
            args.len(),
            ArgumentCountCheck::AtMost
        );

        self.charge(generator, builder, 0)?;

        let (result_offset, _) =
            generator.create_call_stack_local(builder, &TypeSignature::PrincipalType, false, true);

        // Traverse the version byte
        generator.traverse_expr(builder, args.get_expr(0)?)?;
        // [ version_offset, version_length ]

        // Traverse the public key hash
        generator.traverse_expr(builder, args.get_expr(1)?)?;
        // [ version_offset, version_length, pkhash_offset, pkhash_length ]

        if let Some(contract) = args.get(2) {
            // Push a 1 to indicate that a contract name was passed
            builder.i32_const(1);

            // Traverse the contract name (if it exists)
            generator.traverse_expr(builder, contract)?;
        } else {
            // Else push a 0 to indicate that no contract name was passed, and
            // two placeholder 0s.
            builder.i32_const(0).i32_const(0).i32_const(0);
        }
        // [ version_offset, version_length,
        //   pkhash_offset, pkhash_length,
        //   contract_present, contract_offset, contract_length ]

        // Call the principal-construct function in the stdlib
        builder
            .local_get(result_offset)
            .call(generator.func_by_name("stdlib.principal-construct"));

        Ok(())
    }
}

#[derive(Debug)]
pub struct Destruct;

/// Build the result tuple:
/// {
///   hash-bytes: (buff 20)
///   name: (optional (string-ascii 40))
///   version: (buff 1)
/// }
fn generate_tuple(
    builder: &mut walrus::InstrSeqBuilder,
    principal_offset: LocalId,
    length: LocalId,
) {
    // Push the hash-bytes offset
    builder
        .local_get(principal_offset)
        .i32_const(1)
        .binop(BinaryOp::I32Add);

    // Push the hash-bytes length
    builder.i32_const(20);

    // If `length` > 0, then there is a name. This result serves as the
    // optional name indicator.
    builder
        .local_get(length)
        .i32_const(0)
        .binop(BinaryOp::I32GtU);

    // If there isn't a name, then the offset and length will be ignored.
    // Push the name offset
    builder
        .local_get(principal_offset)
        .i32_const(STANDARD_PRINCIPAL_BYTES as i32)
        .binop(BinaryOp::I32Add);

    // Push the name length
    builder.local_get(length);

    // Push the version offset
    builder.local_get(principal_offset);

    // Push the version length
    builder.i32_const(1);
}

impl Word for Destruct {
    fn name(&self) -> ClarityName {
        "principal-destruct?".into()
    }
}

impl SimpleWord for Destruct {
    fn visit(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _arg_types: &[TypeSignature],
        return_type: &TypeSignature,
    ) -> Result<(), GeneratorError> {
        self.charge(generator, builder, 0)?;

        // Subtract STANDARD_PRINCIPAL_BYTES from the length to get the length
        // of the name.
        builder
            .i32_const(STANDARD_PRINCIPAL_BYTES as i32)
            .binop(BinaryOp::I32Sub);

        // Save the length and offset in locals
        let length = generator.module.locals.add(ValType::I32);
        builder.local_set(length);
        let principal_offset = generator.module.locals.add(ValType::I32);
        builder.local_tee(principal_offset);

        // Load the version byte
        builder.load(
            generator.get_memory()?,
            LoadKind::I32_8 {
                kind: ExtendedLoad::ZeroExtend,
            },
            MemArg {
                align: 1,
                offset: 0,
            },
        );

        // Check if the version matches the network.
        builder.call(generator.func_by_name("stdlib.is-version-valid"));

        #[allow(clippy::unwrap_used)]
        let tuple_ty = TypeSignature::TupleType(
            vec![
                ("hash-bytes".into(), TypeSignature::BUFFER_20.clone()),
                (
                    "name".into(),
                    TypeSignature::new_option(TypeSignature::STRING_ASCII_40.clone()).unwrap(),
                ),
                ("version".into(), TypeSignature::BUFFER_1.clone()),
            ]
            .try_into()
            .unwrap(),
        );

        let return_types = clar2wasm_ty(return_type);
        builder.if_else(
            InstrSeqType::new(&mut generator.module.types, &[], &return_types),
            |then| {
                // Push the indicator
                then.i32_const(1);

                // Push the tuple
                generate_tuple(then, principal_offset, length);

                // Push a placeholder for the error value
                add_placeholder_for_clarity_type(then, &tuple_ty);
            },
            |else_| {
                // Push the indicator
                else_.i32_const(0);

                // Push a placeholder for the ok tuple
                add_placeholder_for_clarity_type(else_, &tuple_ty);

                // Push the error tuple
                generate_tuple(else_, principal_offset, length);
            },
        );

        Ok(())
    }
}

#[derive(Debug)]
pub struct PrincipalOf;

impl Word for PrincipalOf {
    fn name(&self) -> ClarityName {
        "principal-of?".into()
    }
}

impl ComplexWord for PrincipalOf {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 1, args.len(), ArgumentCountCheck::Exact);

        self.charge(generator, builder, 0)?;

        // Traverse the public key
        generator.traverse_expr(builder, args.get_expr(0)?)?;

        // Create space for (optional (response principal error))
        let principal_type = TypeSignature::PrincipalType;
        let response_type =
            TypeSignature::ResponseType(Box::new((principal_type.clone(), TypeSignature::NoType)));
        let optional_type = TypeSignature::OptionalType(Box::new(response_type));

        let (result_offset, _) = generator.create_call_stack_local(
            builder,
            &optional_type,
            false, // include_repr
            true,  // include_value
        );

        builder.local_get(result_offset);
        // Call the host interface function, `principal-of?`
        builder.call(generator.func_by_name("stdlib.principal_of"));

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use clarity::vm::errors::Error;
    use clarity::vm::types::{
        BuffData, BufferLength, PrincipalData, SequenceData, SequenceSubtype, TypeSignature,
    };
    use clarity::vm::Value;

    use crate::tools::{crosscheck, evaluate};

    #[test]
    fn test_principal_of() {
        crosscheck(
            "(principal-of? 0x03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba7786110)",
            Ok(Some(
                Value::okay(
                    PrincipalData::parse("ST1AW6EKPGT61SQ9FNVDS17RKNWT8ZP582VF9HSCP")
                        .unwrap()
                        .into(),
                )
                .unwrap(),
            )),
        )
    }

    #[test]
    fn test_principal_of_runtime_err() {
        let pubkey_32_bytes = "03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba77861";

        crosscheck(
            &format!("(principal-of? 0x{pubkey_32_bytes})"),
            Err(Error::Unchecked(
                clarity::vm::errors::CheckErrors::TypeValueError(
                    Box::new(TypeSignature::SequenceType(SequenceSubtype::BufferType(
                        BufferLength::try_from(33_u32).unwrap(),
                    ))),
                    Box::new(Value::Sequence(SequenceData::Buffer(BuffData {
                        data: hex::decode(pubkey_32_bytes).unwrap(),
                    }))),
                ),
            )),
        );
    }

    #[test]
    fn test_principal_of_err() {
        crosscheck(
            "(principal-of? 0x03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba7780000)",
            Ok(Some(Value::err_uint(1))),
        );
    }
    #[test]
    fn principal_construct_less_than_two_args() {
        let result = evaluate("(principal-construct? 0x1a)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting >= 2 arguments, got 1"));
    }

    #[test]
    fn principal_construct_more_than_three_args() {
        let result = evaluate(
            r#"(principal-construct? 0x1a 0xfa6bf38ed557fe417333710d6033e9419391a320 "foo" "bar")"#,
        );
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting < 3 arguments, got 4"));
    }

    #[test]
    fn principal_of_no_args() {
        let result = evaluate("(principal-of?)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 1 arguments, got 0"));
    }

    #[test]
    fn principal_of_more_than_one_arg() {
        let result = evaluate("(principal-of? 0x03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba7786110 21)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 1 arguments, got 2"));
    }

    //
    // Module with tests that should only be executed
    // when running Clarity::V2 or Clarity::v3.
    //
    #[cfg(not(feature = "test-clarity-v1"))]
    #[cfg(test)]
    mod clarity_v2_v3 {
        use clarity::vm::types::{ResponseData, StandardPrincipalData, TupleData};

        use super::*;

        #[test]
        fn test_is_standard() {
            crosscheck(
                "(is-standard 'STB44HYPYAT2BB2QE513NSP81HTMYWBJP02HPGK6)",
                Ok(Some(Value::Bool(true))),
            );
        }

        #[test]
        fn test_is_standard_contract() {
            crosscheck(
                "(is-standard 'STB44HYPYAT2BB2QE513NSP81HTMYWBJP02HPGK6.foo)",
                Ok(Some(Value::Bool(true))),
            );
        }

        #[test]
        fn test_is_standard_multisig() {
            crosscheck(
                "(is-standard 'SN3X6QWWETNBZWGBK6DRGTR1KX50S74D340JWTSC7)",
                Ok(Some(Value::Bool(true))),
            )
        }

        #[test]
        fn test_is_standard_mainnet() {
            crosscheck(
                "(is-standard 'SP3X6QWWETNBZWGBK6DRGTR1KX50S74D3433WDGJY)",
                Ok(Some(Value::Bool(false))),
            );
        }

        #[test]
        fn test_is_standard_mainnet_contract() {
            crosscheck(
                "(is-standard 'SP3X6QWWETNBZWGBK6DRGTR1KX50S74D3433WDGJY.foo)",
                Ok(Some(Value::Bool(false))),
            );
        }

        #[test]
        fn test_is_standard_mainnet_multisig() {
            crosscheck(
                "(is-standard 'SM3X6QWWETNBZWGBK6DRGTR1KX50S74D341M9C5X7)",
                Ok(Some(Value::Bool(false))),
            );
        }

        #[test]
        fn test_is_standard_other() {
            crosscheck(
                "(is-standard 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)",
                Ok(Some(Value::Bool(false))),
            );
        }

        #[test]
        fn test_construct_standard() {
            crosscheck(
                "(principal-construct? 0x1a 0xfa6bf38ed557fe417333710d6033e9419391a320)",
                Ok(Some(
                    Value::okay(
                        PrincipalData::parse("ST3X6QWWETNBZWGBK6DRGTR1KX50S74D3425Q1TPK")
                            .unwrap()
                            .into(),
                    )
                    .unwrap(),
                )),
            );
        }

        #[test]
        fn test_construct_contract() {
            crosscheck(
                r#"(principal-construct? 0x1a 0xfa6bf38ed557fe417333710d6033e9419391a320 "foo")"#,
                Ok(Some(
                    Value::okay(
                        PrincipalData::parse("ST3X6QWWETNBZWGBK6DRGTR1KX50S74D3425Q1TPK.foo")
                            .unwrap()
                            .into(),
                    )
                    .unwrap(),
                )),
            );
        }

        #[test]
        fn test_construct_mainnet() {
            crosscheck(
                "(principal-construct? 0x16 0xfa6bf38ed557fe417333710d6033e9419391a320)",
                Ok(Some(
                    Value::error(
                        TupleData::from_data(vec![
                            ("error_code".into(), Value::UInt(0)),
                            (
                                "value".into(),
                                Value::some(
                                    PrincipalData::parse(
                                        "SP3X6QWWETNBZWGBK6DRGTR1KX50S74D3433WDGJY",
                                    )
                                    .unwrap()
                                    .into(),
                                )
                                .unwrap(),
                            ),
                        ])
                        .unwrap()
                        .into(),
                    )
                    .unwrap(),
                )),
            );
        }

        #[test]
        fn test_construct_mainnet_contract() {
            crosscheck(
                r#"(principal-construct? 0x16 0xfa6bf38ed557fe417333710d6033e9419391a320 "foo")"#,
                Ok(Some(
                    Value::error(
                        TupleData::from_data(vec![
                            ("error_code".into(), Value::UInt(0)),
                            (
                                "value".into(),
                                Value::some(
                                    PrincipalData::parse(
                                        "SP3X6QWWETNBZWGBK6DRGTR1KX50S74D3433WDGJY.foo",
                                    )
                                    .unwrap()
                                    .into(),
                                )
                                .unwrap(),
                            ),
                        ])
                        .unwrap()
                        .into(),
                    )
                    .unwrap(),
                )),
            );
        }

        #[test]
        fn test_construct_empty_version() {
            crosscheck(
                "(principal-construct? 0x 0xfa6bf38ed557fe417333710d6033e9419391a320)",
                Ok(Some(
                    Value::error(
                        TupleData::from_data(vec![
                            ("error_code".into(), Value::UInt(1)),
                            ("value".into(), Value::none()),
                        ])
                        .unwrap()
                        .into(),
                    )
                    .unwrap(),
                )),
            );
        }

        #[test]
        fn test_construct_short_hash() {
            crosscheck(
                "(principal-construct? 0x16 0xfa6bf38ed557fe417333710d6033e9419391a3)",
                Ok(Some(
                    Value::error(
                        TupleData::from_data(vec![
                            ("error_code".into(), Value::UInt(1)),
                            ("value".into(), Value::none()),
                        ])
                        .unwrap()
                        .into(),
                    )
                    .unwrap(),
                )),
            );
        }

        #[test]
        fn test_construct_high_version() {
            crosscheck(
                "(principal-construct? 0x20 0xfa6bf38ed557fe417333710d6033e9419391a320)",
                Ok(Some(
                    Value::error(
                        TupleData::from_data(vec![
                            ("error_code".into(), Value::UInt(1)),
                            ("value".into(), Value::none()),
                        ])
                        .unwrap()
                        .into(),
                    )
                    .unwrap(),
                )),
            );
        }

        #[test]
        fn test_construct_empty_contract() {
            crosscheck(
                r#"(principal-construct? 0x1a 0xfa6bf38ed557fe417333710d6033e9419391a320 "")"#,
                Ok(Some(
                    Value::error(
                        TupleData::from_data(vec![
                            ("error_code".into(), Value::UInt(2)),
                            ("value".into(), Value::none()),
                        ])
                        .unwrap()
                        .into(),
                    )
                    .unwrap(),
                )),
            )
        }

        #[test]
        fn test_construct_illegal_contract() {
            crosscheck(
                r#"(principal-construct? 0x1a 0xfa6bf38ed557fe417333710d6033e9419391a320 "foo[")"#,
                Ok(Some(
                    Value::error(
                        TupleData::from_data(vec![
                            ("error_code".into(), Value::UInt(2)),
                            ("value".into(), Value::none()),
                        ])
                        .unwrap()
                        .into(),
                    )
                    .unwrap(),
                )),
            )
        }

        #[test]
        fn test_destruct_standard() {
            crosscheck(
                "(principal-destruct? 'STB44HYPYAT2BB2QE513NSP81HTMYWBJP02HPGK6)",
                Ok(Some(
                    Value::okay(
                        TupleData::from_data(vec![
                            (
                                "hash-bytes".into(),
                                Value::buff_from(
                                    hex::decode("164247d6f2b425ac5771423ae6c80c754f7172b0")
                                        .unwrap(),
                                )
                                .unwrap(),
                            ),
                            ("name".into(), Value::none()),
                            ("version".into(), Value::buff_from_byte(0x1a)),
                        ])
                        .unwrap()
                        .into(),
                    )
                    .unwrap(),
                )),
            );
        }

        #[test]
        fn test_destruct_contract() {
            crosscheck(
                "(principal-destruct? 'STB44HYPYAT2BB2QE513NSP81HTMYWBJP02HPGK6.foo)",
                Ok(Some(
                    Value::okay(
                        TupleData::from_data(vec![
                            (
                                "hash-bytes".into(),
                                Value::buff_from(
                                    hex::decode("164247d6f2b425ac5771423ae6c80c754f7172b0")
                                        .unwrap(),
                                )
                                .unwrap(),
                            ),
                            (
                                "name".into(),
                                Value::some(
                                    Value::string_ascii_from_bytes("foo".as_bytes().to_vec())
                                        .unwrap(),
                                )
                                .unwrap(),
                            ),
                            ("version".into(), Value::buff_from_byte(0x1a)),
                        ])
                        .unwrap()
                        .into(),
                    )
                    .unwrap(),
                )),
            );
        }

        #[test]
        fn test_destruct_standard_err() {
            crosscheck(
                "(principal-destruct? 'SP3X6QWWETNBZWGBK6DRGTR1KX50S74D3433WDGJY)",
                Ok(Some(
                    Value::error(
                        TupleData::from_data(vec![
                            (
                                "hash-bytes".into(),
                                Value::buff_from(
                                    hex::decode("fa6bf38ed557fe417333710d6033e9419391a320")
                                        .unwrap(),
                                )
                                .unwrap(),
                            ),
                            ("name".into(), Value::none()),
                            ("version".into(), Value::buff_from_byte(0x16)),
                        ])
                        .unwrap()
                        .into(),
                    )
                    .unwrap(),
                )),
            );
        }

        #[test]
        fn test_destruct_contract_err() {
            crosscheck(
                "(principal-destruct? 'SP3X6QWWETNBZWGBK6DRGTR1KX50S74D3433WDGJY.foo)",
                Ok(Some(
                    Value::error(
                        TupleData::from_data(vec![
                            (
                                "hash-bytes".into(),
                                Value::buff_from(
                                    hex::decode("fa6bf38ed557fe417333710d6033e9419391a320")
                                        .unwrap(),
                                )
                                .unwrap(),
                            ),
                            (
                                "name".into(),
                                Value::some(
                                    Value::string_ascii_from_bytes("foo".as_bytes().to_vec())
                                        .unwrap(),
                                )
                                .unwrap(),
                            ),
                            ("version".into(), Value::buff_from_byte(0x16)),
                        ])
                        .unwrap()
                        .into(),
                    )
                    .unwrap(),
                )),
            );
        }

        #[test]
        fn builtins_principals() {
            let snpt = "
    (define-public (get-tx-sender)
      (ok tx-sender))

    (define-public (get-contract-caller)
      (ok contract-caller))

    (define-public (get-tx-sponsor)
      (ok tx-sponsor?))
            ";

            crosscheck(
                &format!("{snpt} (get-tx-sender)"),
                Ok(Some(Value::Response(ResponseData {
                    committed: true,
                    data: Box::new(Value::Principal(PrincipalData::Standard(
                        StandardPrincipalData::transient(),
                    ))),
                }))),
            );

            crosscheck(
                &format!("{snpt} (get-contract-caller)"),
                Ok(Some(Value::Response(ResponseData {
                    committed: true,
                    data: Box::new(Value::Principal(PrincipalData::Standard(
                        StandardPrincipalData::transient(),
                    ))),
                }))),
            );

            crosscheck(
                &format!("{snpt} (get-tx-sponsor)"),
                Ok(Some(Value::Response(ResponseData {
                    committed: true,
                    data: Box::new(Value::none()),
                }))),
            );
        }
    }
}
