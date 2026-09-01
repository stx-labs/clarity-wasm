use clarity::vm::{ClarityName, SymbolicExpression};

use super::{ComplexWord, Word};
use crate::check_args;
use crate::cost::WordCharge;
use crate::wasm_generator::{ArgumentsExt, GeneratorError, WasmGenerator};
use crate::wasm_utils::ArgumentCountCheck;

#[derive(Debug)]
pub struct Recover;

impl Word for Recover {
    fn name(&self) -> ClarityName {
        ClarityName::from_literal("secp256k1-recover?")
    }
}

impl ComplexWord for Recover {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 2, args.len(), ArgumentCountCheck::Exact);

        self.charge(generator, builder, 0)?;

        generator.traverse_expr(builder, args.get_expr(0)?)?;
        generator.traverse_expr(builder, args.get_expr(1)?)?;

        // Reserve stack space for the host-function to write the result
        let ret_ty = generator
            .get_expr_type(expr)
            .ok_or_else(|| {
                GeneratorError::TypeError("result of secp256k1-recover? should be typed".to_owned())
            })?
            .clone();

        let (result_local, result_size) =
            generator.create_call_stack_local(builder, &ret_ty, true, true);
        builder.local_get(result_local).i32_const(result_size);

        // Call the host interface function, `secp256k1_recover`
        builder.call(
            generator
                .module
                .funcs
                .by_name("stdlib.secp256k1_recover")
                .ok_or_else(|| {
                    GeneratorError::InternalError("stdlib.secp256k1_recover not found".to_owned())
                })?,
        );

        generator.read_from_memory(builder, result_local, 0, &ret_ty)?;

        Ok(())
    }
}

#[derive(Debug)]
pub struct Verify;

impl Word for Verify {
    fn name(&self) -> ClarityName {
        ClarityName::from_literal("secp256k1-verify")
    }
}

impl ComplexWord for Verify {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 3, args.len(), ArgumentCountCheck::Exact);

        self.charge(generator, builder, 0)?;

        generator.traverse_expr(builder, args.get_expr(0)?)?;
        generator.traverse_expr(builder, args.get_expr(1)?)?;
        generator.traverse_expr(builder, args.get_expr(2)?)?;

        // Call the host interface function, `secp256k1_verify`
        builder.call(
            generator
                .module
                .funcs
                .by_name("stdlib.secp256k1_verify")
                .ok_or_else(|| {
                    GeneratorError::InternalError("stdlib.secp256k1_verify not found".to_owned())
                })?,
        );

        Ok(())
    }
}

#[derive(Debug)]
pub struct Decompress;

impl Word for Decompress {
    fn name(&self) -> ClarityName {
        ClarityName::from_literal("secp256k1-decompress?")
    }
}

impl ComplexWord for Decompress {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 1, args.len(), ArgumentCountCheck::Exact);

        generator.traverse_expr(builder, args.get_expr(0)?)?;

        // Reserve stack space for the host-function to write the result
        let ret_ty = generator
            .get_expr_type(expr)
            .ok_or_else(|| {
                GeneratorError::TypeError(
                    "result of secp256k1-decompress? should be typed".to_owned(),
                )
            })?
            .clone();

        let (result_local, result_size) =
            generator.create_call_stack_local(builder, &ret_ty, true, true);
        builder.local_get(result_local).i32_const(result_size);

        // Call the host interface function, `secp256k1_decompress?`
        builder.call(
            generator
                .module
                .funcs
                .by_name("stdlib.secp256k1_decompress")
                .ok_or_else(|| {
                    GeneratorError::InternalError(
                        "stdlib.secp256k1_decompress not found".to_owned(),
                    )
                })?,
        );

        generator.read_from_memory(builder, result_local, 0, &ret_ty)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use clarity::vm::errors::VmExecutionError;
    use clarity::vm::types::{
        BuffData, BufferLength, SequenceData, SequenceSubtype, TypeSignature,
    };
    use clarity::vm::Value;

    use crate::tools::{crosscheck, evaluate};

    /// Uncompressed form of the compressed key
    /// 0x0250863ad64a87ae8a2fe83c1af1a8403cb53f53e486d8511dad8a04887e5b2352,
    /// reused across the `secp256k1-decompress?` tests.
    #[cfg(not(any(
        feature = "test-clarity-v1",
        feature = "test-clarity-v2",
        feature = "test-clarity-v3",
        feature = "test-clarity-v4",
        feature = "test-clarity-v5"
    )))]
    const UNCOMPRESSED: &str = "0450863ad64a87ae8a2fe83c1af1a8403cb53f53e486d8511dad8a04887e5b23522cd470243453a299fa9e77237716103abc11a1df38855ed6f2ee187e9c582ba6";

    /// Expected `(ok <65-byte buffer>)` for the given hex-encoded public key.
    #[cfg(not(any(
        feature = "test-clarity-v1",
        feature = "test-clarity-v2",
        feature = "test-clarity-v3",
        feature = "test-clarity-v4",
        feature = "test-clarity-v5"
    )))]
    fn ok_pubkey(hex_key: &str) -> Result<Option<Value>, VmExecutionError> {
        Ok(Some(
            Value::okay(Value::buff_from(hex::decode(hex_key).unwrap()).unwrap()).unwrap(),
        ))
    }

    #[test]
    fn secp256k1_recover_less_than_two_args() {
        let result = evaluate("(secp256k1-recover? 0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 1"));
    }

    #[test]
    fn secp256k1_recover_more_than_two_args() {
        let result = evaluate("(secp256k1-recover? 0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04 0x8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a1301 0x03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba7786110)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 3"));
    }

    #[test]
    fn test_secp256k1_recover() {
        let mut expected = [0u8; 33];
        hex::decode_to_slice(
            "03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba7786110",
            &mut expected,
        )
        .unwrap();

        crosscheck("(secp256k1-recover? 0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04
                0x8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a1301)",
        Ok(Some(Value::okay(Value::buff_from(expected.to_vec()).unwrap()).unwrap())))
    }

    #[test]
    fn test_secp256k1_recover_recid_3() {
        let mut expected = [0u8; 33];
        hex::decode_to_slice(
            "02db06e162a09f325a1150df9a2900431e89ea9cb92a9200d01bc6f6abc90e6dcb",
            &mut expected,
        )
        .unwrap();

        // Recovery id 3
        crosscheck("(secp256k1-recover? 0x19148567fff5a6177a7acae9ad60ceeff66f07ba00570b7abb64ff1f9d665dd4
                0x00000000000000000000000000000000604b173b69f8f48ee7a8780e6660b166fd76498d6e1552efce5bf370d0b17ebfd58df8a7fafa10ad9d32a7de305597e803)",
        Ok(Some(Value::okay(Value::buff_from(expected.to_vec()).unwrap()).unwrap())))
    }

    #[test]
    fn test_secp256k1_verify_less_than_three_args() {
        let result = evaluate("(secp256k1-verify 0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04
        0x8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a1301)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 3 arguments, got 2"));
    }

    #[test]
    fn secp256k1_verify_more_than_three_args() {
        let result = evaluate("(secp256k1-verify 0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04
        0x8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a1301
        0x03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba7786110
        0x03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba7786110)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 3 arguments, got 4"));
    }

    #[test]
    fn test_secp256k1_verify() {
        crosscheck("(secp256k1-verify 0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04
            0x8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a1301
            0x03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba7786110)", Ok(Some(Value::Bool(true))));
        crosscheck("(secp256k1-verify 0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04
            0x8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a13
            0x03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba7786110)", Ok(Some(Value::Bool(true))));
        crosscheck("(secp256k1-verify 0x0000000000000000000000000000000000000000000000000000000000000000
            0x0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
            0x03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba7786110)", Ok(Some(Value::Bool(false))));

        // Recovery id (b'\x03') <= b'\x03' (with correct signature[..64])
        crosscheck("(secp256k1-verify 0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04
            0x8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a1303
            0x03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba7786110)", Ok(Some(Value::Bool(true))));
    }

    #[test]
    fn test_secp256k1_recover_bad_values() {
        // For some reason, if the message-hash is the wrong size, it throws a
        // runtime type error, but if the signature is the wrong size, it's a
        // normal clarity error.

        // Message hash too short
        let short_hash = "de5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f";
        crosscheck(&format!("(secp256k1-recover? 0x{short_hash}
            0x8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a1301)"),
            Err(VmExecutionError::RuntimeCheck(
                clarity::vm::errors::RuntimeCheckErrorKind::TypeValueError(
                    Box::new(TypeSignature::SequenceType(SequenceSubtype::BufferType(
                        BufferLength::try_from(32_u32).unwrap(),
                    ))),
                    Value::Sequence(SequenceData::Buffer(BuffData {
                        data: hex::decode(short_hash).unwrap(),
                    })).to_error_string(),
                ),
            )));

        // Signature too short
        crosscheck("(secp256k1-recover? 0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04
            0x8738487ebe69b93d8e51583be8eee50bb4213fc49c767d1cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a13)",
            Ok(Some(Value::err_uint(2))));

        // Recovery id (b'\x17') > b'\x03'
        let snippet = "(secp256k1-recover?
        0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04
        0x8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a1317)";

        crosscheck(snippet, Ok(Some(Value::err_uint(2))));

        // Recovery id (b'\x04') > b'\x03'
        let snippet = "(secp256k1-recover?
            0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04
            0x8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a1304)";

        crosscheck(snippet, Ok(Some(Value::err_uint(2))));
    }

    #[test]
    fn test_secp256k1_recover_signature_not_matching() {
        // Recovery id (b'\x03') <= b'\x03'
        let snippet = "(secp256k1-recover?
            0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04
            0x8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a1303)";

        crosscheck(snippet, Ok(Some(Value::err_uint(1))));
    }

    #[test]
    fn test_secp256k1_verify_bad_values() {
        // For some reason, if the message hash or public key are the wrong
        // size, it throws a runtime type error, but if the signature is the
        // wrong size, it's a normal clarity error.

        // Message hash too short
        let short_hash = "de5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f";

        crosscheck(&format!("(secp256k1-verify 0x{short_hash}
            0x8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a1301
            0x03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba7786110)"),
            Err(VmExecutionError::RuntimeCheck(
                clarity::vm::errors::RuntimeCheckErrorKind::TypeValueError(
                    Box::new(TypeSignature::SequenceType(SequenceSubtype::BufferType(
                        BufferLength::try_from(32_u32).unwrap(),
                    ))),
                    Value::Sequence(SequenceData::Buffer(BuffData {
                        data: hex::decode(short_hash).unwrap(),
                    })).to_error_string()),
                ),
            ));

        // Signature too short
        let short_sig = "8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a";

        crosscheck(&format!("(secp256k1-verify 0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04
            0x{short_sig}
            0x03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba7786110)"),
            Ok(Some(Value::Bool(false))));

        // Recovery id (b'\x04') > b'\x03' (with correct signature[..64])
        crosscheck("(secp256k1-verify 0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04
            0x8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a1304
            0x03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba7786110)",
        Ok(Some(Value::Bool(false))));

        // Public key is too short
        let short_pubkey = "03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba77861";

        crosscheck(&format!("(secp256k1-verify 0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04
            0x8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a1301
            0x{short_pubkey})"),
            Err(VmExecutionError::RuntimeCheck(
                clarity::vm::errors::RuntimeCheckErrorKind::TypeValueError(
                    Box::new(TypeSignature::SequenceType(SequenceSubtype::BufferType(
                        BufferLength::try_from(33_u32).unwrap(),
                    ))),
                    Value::Sequence(SequenceData::Buffer(BuffData {
                        data: hex::decode(short_pubkey).unwrap(),
                    })).to_error_string(),
                ),
            )));
    }

    #[cfg(not(any(
        feature = "test-clarity-v1",
        feature = "test-clarity-v2",
        feature = "test-clarity-v3",
        feature = "test-clarity-v4",
        feature = "test-clarity-v5"
    )))]
    #[test]
    fn test_secp256k1_decompress_0_arguments() {
        let result = evaluate("(secp256k1-decompress? )");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 1 arguments, got 0"));
    }

    #[cfg(not(any(
        feature = "test-clarity-v1",
        feature = "test-clarity-v2",
        feature = "test-clarity-v3",
        feature = "test-clarity-v4",
        feature = "test-clarity-v5"
    )))]
    #[test]
    fn test_secp256k1_decompress_2_arguments() {
        let result = evaluate("(secp256k1-decompress? 1 2)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 1 arguments, got 2"));
    }

    #[cfg(not(any(
        feature = "test-clarity-v1",
        feature = "test-clarity-v2",
        feature = "test-clarity-v3",
        feature = "test-clarity-v4",
        feature = "test-clarity-v5"
    )))]
    #[test]
    fn test_secp256k1_decompress_bad_public_key_buffer_length() {
        let result = evaluate("(secp256k1-decompress? 0x1)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("invalid buffer length, 1"));
    }

    #[cfg(not(any(
        feature = "test-clarity-v1",
        feature = "test-clarity-v2",
        feature = "test-clarity-v3",
        feature = "test-clarity-v4",
        feature = "test-clarity-v5"
    )))]
    #[test]
    fn test_secp256k1_decompress_bad_public_key_size() {
        crosscheck(
            "(secp256k1-decompress? 0x11)",
            Err(clarity::vm::errors::RuntimeCheckErrorKind::TypeValueError(
                Box::new(TypeSignature::BUFFER_33),
                Value::Sequence(SequenceData::Buffer(BuffData {
                    data: hex::decode("11").unwrap(),
                }))
                .to_error_string(),
            )
            .into()),
        );
    }

    #[cfg(not(any(
        feature = "test-clarity-v1",
        feature = "test-clarity-v2",
        feature = "test-clarity-v3",
        feature = "test-clarity-v4",
        feature = "test-clarity-v5"
    )))]
    #[test]
    fn test_secp256k1_decompress_bad_public_key() {
        crosscheck(
            "(secp256k1-decompress? 0x111111111111111111111111111111111111111111111111111111111111111111)",
            Ok(Some(Value::err_uint(1)))
        );
    }

    #[cfg(not(any(
        feature = "test-clarity-v1",
        feature = "test-clarity-v2",
        feature = "test-clarity-v3",
        feature = "test-clarity-v4",
        feature = "test-clarity-v5"
    )))]
    #[test]
    fn test_secp256k1_decompress_0x02_prefix() {
        crosscheck(
            "(secp256k1-decompress? 0x0250863ad64a87ae8a2fe83c1af1a8403cb53f53e486d8511dad8a04887e5b2352)",
            ok_pubkey(UNCOMPRESSED),
        );
    }

    #[cfg(not(any(
        feature = "test-clarity-v1",
        feature = "test-clarity-v2",
        feature = "test-clarity-v3",
        feature = "test-clarity-v4",
        feature = "test-clarity-v5"
    )))]
    #[test]
    fn test_secp256k1_decompress_0x03_prefix() {
        // i.e. `p - y` of the 0x02 form.
        crosscheck(
            "(secp256k1-decompress? 0x0379be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798)",
            ok_pubkey("0479be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798b7c52588d95c3b9aa25b0403f1eef75702e84bb7597aabe663b82f6f04ef2777"),
        );
    }

    #[cfg(not(any(
        feature = "test-clarity-v1",
        feature = "test-clarity-v2",
        feature = "test-clarity-v3",
        feature = "test-clarity-v4",
        feature = "test-clarity-v5"
    )))]
    #[test]
    fn test_secp256k1_decompress_all_zero_key() {
        // x = 0 is a valid field element, but y^2 = 7 has no solution mod p.
        crosscheck(
            "(secp256k1-decompress? 0x000000000000000000000000000000000000000000000000000000000000000000)",
            Ok(Some(Value::err_uint(1))),
        );
    }

    #[cfg(not(any(
        feature = "test-clarity-v1",
        feature = "test-clarity-v2",
        feature = "test-clarity-v3",
        feature = "test-clarity-v4",
        feature = "test-clarity-v5"
    )))]
    #[test]
    fn test_secp256k1_decompress_public_key_too_long() {
        crate::tools::crosscheck_expect_failure(
            "(secp256k1-decompress? 0x02000000000000000000000000000000000000000000000000000000000000000000)",
        );
    }

    #[cfg(not(any(
        feature = "test-clarity-v1",
        feature = "test-clarity-v2",
        feature = "test-clarity-v3",
        feature = "test-clarity-v4",
        feature = "test-clarity-v5"
    )))]
    #[test]
    fn test_secp256k1_decompress_oom() {
        crate::tools::crosscheck_oom(
            "(secp256k1-decompress? 0x0250863ad64a87ae8a2fe83c1af1a8403cb53f53e486d8511dad8a04887e5b2352)",
            ok_pubkey(UNCOMPRESSED),
        );
    }

    #[cfg(not(any(
        feature = "test-clarity-v1",
        feature = "test-clarity-v2",
        feature = "test-clarity-v3",
        feature = "test-clarity-v4",
        feature = "test-clarity-v5"
    )))]
    #[test]
    fn test_secp256k1_decompress_x_out_of_range() {
        // x = 2^256 - 1 is not a field element (x >= p), so it is rejected
        // before the curve equation is evaluated.
        crosscheck(
            "(secp256k1-decompress? 0x02ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)",
            Ok(Some(Value::err_uint(1))),
        );
    }

    #[cfg(not(any(
        feature = "test-clarity-v1",
        feature = "test-clarity-v2",
        feature = "test-clarity-v3",
        feature = "test-clarity-v4",
        feature = "test-clarity-v5"
    )))]
    #[cfg(not(any(
        feature = "test-clarity-v1",
        feature = "test-clarity-v2",
        feature = "test-clarity-v3",
        feature = "test-clarity-v4",
        feature = "test-clarity-v5"
    )))]
    #[test]
    fn test_secp256k1_decompress_of_recover_result() {
        // `secp256k1-recover?` yields the compressed key
        // 0x03adb8de...786110, which decompresses to the value below.
        crosscheck(
            "(secp256k1-decompress? (unwrap-panic (secp256k1-recover? 0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04 0x8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a1301)))",
            ok_pubkey("04adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba7786110f600feb84ae5a7b551be5fd6a33e07a04ae1e20f8bac89e58e684625c1292af3"),
        );
    }
}
