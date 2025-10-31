use clarity::vm::{ClarityName, SymbolicExpression};

use super::{ComplexWord, Word};
use crate::check_args;
use crate::cost::WordCharge;
use crate::wasm_generator::{ArgumentsExt, GeneratorError, WasmGenerator};
use crate::wasm_utils::{check_argument_count, ArgumentCountCheck};

#[derive(Debug)]
pub struct Recover;

impl Word for Recover {
    fn name(&self) -> ClarityName {
        "secp256k1-recover?".into()
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
        "secp256k1-verify".into()
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

#[cfg(test)]
mod tests {
    use clarity::vm::errors::Error;
    use clarity::vm::types::{
        BuffData, BufferLength, SequenceData, SequenceSubtype, TypeSignature,
    };
    use clarity::vm::Value;

    use crate::tools::{crosscheck, evaluate};

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
            Err(Error::Unchecked(
                clarity::vm::errors::CheckErrors::TypeValueError(
                    Box::new(TypeSignature::SequenceType(SequenceSubtype::BufferType(
                        BufferLength::try_from(32_u32).unwrap(),
                    ))),
                    Box::new(Value::Sequence(SequenceData::Buffer(BuffData {
                        data: hex::decode(short_hash).unwrap(),
                    }))),
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
            Err(Error::Unchecked(
                clarity::vm::errors::CheckErrors::TypeValueError(
                    Box::new(TypeSignature::SequenceType(SequenceSubtype::BufferType(
                        BufferLength::try_from(32_u32).unwrap(),
                    ))),
                    Box::new(Value::Sequence(SequenceData::Buffer(BuffData {
                        data: hex::decode(short_hash).unwrap(),
                    }))),
                ),
            )));

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
            Err(Error::Unchecked(
                clarity::vm::errors::CheckErrors::TypeValueError(
                    Box::new(TypeSignature::SequenceType(SequenceSubtype::BufferType(
                        BufferLength::try_from(33_u32).unwrap(),
                    ))),
                    Box::new(Value::Sequence(SequenceData::Buffer(BuffData {
                        data: hex::decode(short_pubkey).unwrap(),
                    }))),
                ),
            )));
    }
}
