use clarity_types::ClarityName;
use walrus::ir::{BinaryOp, Block};
use walrus::ValType;

use crate::check_args;
use crate::cost::WordCharge;
use crate::error_mapping::ErrorMap;
use crate::wasm_generator::GeneratorError;
use crate::wasm_utils::get_global;
use crate::words::{ComplexWord, Word};

#[derive(Debug)]
pub struct Verify;

impl Word for Verify {
    fn name(&self) -> clarity_types::ClarityName {
        ClarityName::from_literal("secp256r1-verify")
    }
}

impl ComplexWord for Verify {
    fn traverse(
        &self,
        generator: &mut crate::wasm_generator::WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &clarity::vm::SymbolicExpression,
        args: &[clarity::vm::SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(
            generator,
            builder,
            3,
            args.len(),
            crate::wasm_utils::ArgumentCountCheck::Exact
        );

        self.charge(generator, builder, 0)?;

        let [message_hash, signature, public_key] = args else {
            unreachable!()
        };

        let verify_function = generator.func_by_name(
            if generator
                .contract_analysis
                .clarity_version
                .uses_secp256r1_double_hashing()
            {
                "stdlib.secp256r1_verify_double_hash"
            } else {
                "stdlib.secp256r1_verify_simple_hash"
            },
        );

        let outer_block_id = {
            let mut outer_block = builder.dangling_instr_seq(ValType::I32);
            let outer_block_id = outer_block.id();

            let expected_buffer_size = generator.borrow_local(ValType::I32);
            let actual_buffer_offset = generator.borrow_local(ValType::I32);
            let actual_buffer_size = generator.borrow_local(ValType::I32);

            let inner_block_id = {
                let mut inner_block = outer_block.dangling_instr_seq(None);
                let inner_block_id = inner_block.id();

                // handling message hash
                generator.traverse_expr(&mut inner_block, message_hash)?;
                inner_block
                    .local_set(*actual_buffer_size)
                    .local_set(*actual_buffer_offset);
                inner_block.i32_const(32).local_set(*expected_buffer_size);
                inner_block
                    .local_get(*expected_buffer_size)
                    .local_get(*actual_buffer_size)
                    .binop(BinaryOp::I32Ne)
                    .br_if(inner_block_id);
                inner_block
                    .local_get(*actual_buffer_offset)
                    .local_get(*actual_buffer_size);

                // handling signature
                generator.traverse_expr(&mut inner_block, signature)?;
                inner_block
                    .local_set(*actual_buffer_size)
                    .local_set(*actual_buffer_offset);
                inner_block.i32_const(64).local_set(*expected_buffer_size);
                inner_block
                    .local_get(*expected_buffer_size)
                    .local_get(*actual_buffer_size)
                    .binop(BinaryOp::I32LtU)
                    .br_if(inner_block_id);
                // if signature size is different from 64, it's an automatic false result
                inner_block
                    .local_get(*expected_buffer_size)
                    .local_get(*actual_buffer_size)
                    .binop(BinaryOp::I32Ne)
                    .if_else(
                        None,
                        |then| {
                            // we push a false
                            then.i32_const(0);
                            // we branch to the end of the computation: branching
                            // to the (i32-typed) outer block keeps the false we
                            // just pushed and unwinds the message hash offset and
                            // size still sitting on the stack.
                            then.br(outer_block_id);
                        },
                        |_else| {},
                    );
                inner_block
                    .local_get(*actual_buffer_offset)
                    .local_get(*actual_buffer_size);

                // handling public key
                generator.traverse_expr(&mut inner_block, public_key)?;
                inner_block
                    .local_set(*actual_buffer_size)
                    .local_set(*actual_buffer_offset);
                inner_block.i32_const(33).local_set(*expected_buffer_size);
                inner_block
                    .local_get(*expected_buffer_size)
                    .local_get(*actual_buffer_size)
                    .binop(BinaryOp::I32Ne)
                    .br_if(inner_block_id);
                inner_block
                    .local_get(*actual_buffer_offset)
                    .local_get(*actual_buffer_size);

                // calling the secp256r1 verify function
                inner_block.call(verify_function);

                // we can now go to the end of the computation
                inner_block.br(outer_block_id);

                inner_block_id
            };

            outer_block.instr(Block {
                seq: inner_block_id,
            });

            // if we arrive here, we have to throw a runtime error.
            outer_block
                .local_get(*expected_buffer_size)
                .global_set(get_global(&generator.module, "runtime-error-value-offset")?);
            outer_block
                .local_get(*actual_buffer_offset)
                .global_set(get_global(&generator.module, "runtime-error-arg-offset")?);
            outer_block
                .local_get(*actual_buffer_size)
                .global_set(get_global(&generator.module, "runtime-error-arg-len")?);
            outer_block
                .i32_const(ErrorMap::IncorrectBufferSize as i32)
                .call(generator.func_by_name("stdlib.runtime-error"));

            outer_block.unreachable();

            outer_block_id
        };

        builder.instr(Block {
            seq: outer_block_id,
        });

        Ok(())
    }
}

#[cfg(test)]
#[cfg(not(any(
    feature = "test-clarity-v1",
    feature = "test-clarity-v2",
    feature = "test-clarity-v3"
)))]
mod tests {

    use crate::tools::evaluate;

    #[test]
    fn less_than_three_args() {
        let result = evaluate(
                "(secp256r1-verify \
                 0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04 \
                 0x0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)",
            );
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 3 arguments, got 2"));
    }

    #[test]
    fn more_than_three_args() {
        let result = evaluate(
                "(secp256r1-verify \
                 0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04 \
                 0x0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 \
                 0x000000000000000000000000000000000000000000000000000000000000000000 \
                 0x000000000000000000000000000000000000000000000000000000000000000000)",
            );
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 3 arguments, got 4"));
    }

    /// Clarity 4: the message hash is SHA256-hashed again before verification
    /// (*double hashing*).
    #[cfg(feature = "test-clarity-v4")]
    mod clarity_v4 {
        use clarity::util::hash::to_hex;
        use clarity::util::secp256r1::{Secp256r1PrivateKey, Secp256r1PublicKey};
        use clarity::vm::errors::{RuntimeCheckErrorKind, VmExecutionError};
        use clarity::vm::types::{
            BuffData, BufferLength, SequenceData, SequenceSubtype, TypeSignature,
        };
        use clarity::vm::Value;

        use crate::tools::crosscheck;

        #[test]
        fn message_too_short() {
            let short_msg = vec![0xabu8; 31];
            let sig = vec![0u8; 64];
            let pubkey = vec![0u8; 33];
            crosscheck(
                &format!(
                    "(secp256r1-verify 0x{} 0x{} 0x{})",
                    to_hex(&short_msg),
                    to_hex(&sig),
                    to_hex(&pubkey)
                ),
                Err(VmExecutionError::RuntimeCheck(
                    RuntimeCheckErrorKind::TypeValueError(
                        Box::new(TypeSignature::SequenceType(SequenceSubtype::BufferType(
                            BufferLength::try_from(32_u32).unwrap(),
                        ))),
                        Value::Sequence(SequenceData::Buffer(BuffData { data: short_msg }))
                            .to_error_string(),
                    ),
                )),
            );
        }

        #[test]
        fn signature_too_short() {
            // A signature that is shorter than 64 bytes is not a runtime error:
            // the word returns `false`.
            let msg = vec![0u8; 32];
            let short_sig = vec![0u8; 63];
            let pubkey = vec![0u8; 33];
            crosscheck(
                &format!(
                    "(secp256r1-verify 0x{} 0x{} 0x{})",
                    to_hex(&msg),
                    to_hex(&short_sig),
                    to_hex(&pubkey)
                ),
                Ok(Some(Value::Bool(false))),
            );
        }

        #[test]
        fn public_key_too_short() {
            let msg = vec![0u8; 32];
            let sig = vec![0u8; 64];
            let short_pubkey = vec![0xcdu8; 32];
            crosscheck(
                &format!(
                    "(secp256r1-verify 0x{} 0x{} 0x{})",
                    to_hex(&msg),
                    to_hex(&sig),
                    to_hex(&short_pubkey)
                ),
                Err(VmExecutionError::RuntimeCheck(
                    RuntimeCheckErrorKind::TypeValueError(
                        Box::new(TypeSignature::SequenceType(SequenceSubtype::BufferType(
                            BufferLength::try_from(33_u32).unwrap(),
                        ))),
                        Value::Sequence(SequenceData::Buffer(BuffData { data: short_pubkey }))
                            .to_error_string(),
                    ),
                )),
            );
        }

        #[test]
        fn valid_signature() {
            let privk = Secp256r1PrivateKey::from_seed(&[1u8; 32]);
            let pubk = Secp256r1PublicKey::from_private(&privk);
            let msg = [0x11u8; 32];
            // `sign` double-hashes, matching the Clarity 4 verification.
            let sig = privk.sign(&msg).unwrap();
            crosscheck(
                &format!(
                    "(secp256r1-verify 0x{} 0x{} 0x{})",
                    to_hex(&msg),
                    to_hex(&sig.0),
                    to_hex(&pubk.to_bytes_compressed())
                ),
                Ok(Some(Value::Bool(true))),
            );
        }

        #[test]
        fn wrong_message() {
            let privk = Secp256r1PrivateKey::from_seed(&[1u8; 32]);
            let pubk = Secp256r1PublicKey::from_private(&privk);
            let msg = [0x11u8; 32];
            let sig = privk.sign(&msg).unwrap();
            let wrong_msg = [0x22u8; 32];
            crosscheck(
                &format!(
                    "(secp256r1-verify 0x{} 0x{} 0x{})",
                    to_hex(&wrong_msg),
                    to_hex(&sig.0),
                    to_hex(&pubk.to_bytes_compressed())
                ),
                Ok(Some(Value::Bool(false))),
            );
        }

        #[test]
        fn wrong_key() {
            let privk = Secp256r1PrivateKey::from_seed(&[1u8; 32]);
            let msg = [0x11u8; 32];
            let sig = privk.sign(&msg).unwrap();
            let other_pub =
                Secp256r1PublicKey::from_private(&Secp256r1PrivateKey::from_seed(&[2u8; 32]));
            crosscheck(
                &format!(
                    "(secp256r1-verify 0x{} 0x{} 0x{})",
                    to_hex(&msg),
                    to_hex(&sig.0),
                    to_hex(&other_pub.to_bytes_compressed())
                ),
                Ok(Some(Value::Bool(false))),
            );
        }

        #[test]
        fn simple_hash_signature_is_rejected() {
            // A signature produced for the simple-hashing scheme (`sign_digest`)
            // must not verify under the double-hashing scheme.
            let privk = Secp256r1PrivateKey::from_seed(&[1u8; 32]);
            let pubk = Secp256r1PublicKey::from_private(&privk);
            let msg = [0x11u8; 32];
            let sig = privk.sign_digest(&msg).unwrap();
            crosscheck(
                &format!(
                    "(secp256r1-verify 0x{} 0x{} 0x{})",
                    to_hex(&msg),
                    to_hex(&sig.0),
                    to_hex(&pubk.to_bytes_compressed())
                ),
                Ok(Some(Value::Bool(false))),
            );
        }
    }

    #[cfg(not(any(
        feature = "test-clarity-v1",
        feature = "test-clarity-v2",
        feature = "test-clarity-v3",
        feature = "test-clarity-v4"
    )))]
    mod clarity_ge_v5 {
        use clarity::util::hash::to_hex;
        use clarity::util::secp256r1::{Secp256r1PrivateKey, Secp256r1PublicKey};
        use clarity::vm::errors::{RuntimeCheckErrorKind, VmExecutionError};
        use clarity::vm::types::{
            BuffData, BufferLength, SequenceData, SequenceSubtype, TypeSignature,
        };
        use clarity::vm::Value;

        use crate::tools::crosscheck;

        #[test]
        fn message_too_short() {
            let short_msg = vec![0xabu8; 31];
            let sig = vec![0u8; 64];
            let pubkey = vec![0u8; 33];
            crosscheck(
                &format!(
                    "(secp256r1-verify 0x{} 0x{} 0x{})",
                    to_hex(&short_msg),
                    to_hex(&sig),
                    to_hex(&pubkey)
                ),
                Err(VmExecutionError::RuntimeCheck(
                    RuntimeCheckErrorKind::TypeValueError(
                        Box::new(TypeSignature::SequenceType(SequenceSubtype::BufferType(
                            BufferLength::try_from(32_u32).unwrap(),
                        ))),
                        Value::Sequence(SequenceData::Buffer(BuffData { data: short_msg }))
                            .to_error_string(),
                    ),
                )),
            );
        }

        #[test]
        fn signature_too_short() {
            // A signature that is shorter than 64 bytes is not a runtime error:
            // the word returns `false`.
            let msg = vec![0u8; 32];
            let short_sig = vec![0u8; 63];
            let pubkey = vec![0u8; 33];
            crosscheck(
                &format!(
                    "(secp256r1-verify 0x{} 0x{} 0x{})",
                    to_hex(&msg),
                    to_hex(&short_sig),
                    to_hex(&pubkey)
                ),
                Ok(Some(Value::Bool(false))),
            );
        }

        #[test]
        fn public_key_too_short() {
            let msg = vec![0u8; 32];
            let sig = vec![0u8; 64];
            let short_pubkey = vec![0xcdu8; 32];
            crosscheck(
                &format!(
                    "(secp256r1-verify 0x{} 0x{} 0x{})",
                    to_hex(&msg),
                    to_hex(&sig),
                    to_hex(&short_pubkey)
                ),
                Err(VmExecutionError::RuntimeCheck(
                    RuntimeCheckErrorKind::TypeValueError(
                        Box::new(TypeSignature::SequenceType(SequenceSubtype::BufferType(
                            BufferLength::try_from(33_u32).unwrap(),
                        ))),
                        Value::Sequence(SequenceData::Buffer(BuffData { data: short_pubkey }))
                            .to_error_string(),
                    ),
                )),
            );
        }

        #[test]
        fn valid_signature() {
            let privk = Secp256r1PrivateKey::from_seed(&[1u8; 32]);
            let pubk = Secp256r1PublicKey::from_private(&privk);
            let msg = [0x11u8; 32];
            let sig = privk.sign_digest(&msg).unwrap();
            crosscheck(
                &format!(
                    "(secp256r1-verify 0x{} 0x{} 0x{})",
                    to_hex(&msg),
                    to_hex(&sig.0),
                    to_hex(&pubk.to_bytes_compressed())
                ),
                Ok(Some(Value::Bool(true))),
            );
        }

        #[test]
        fn wrong_message() {
            let privk = Secp256r1PrivateKey::from_seed(&[1u8; 32]);
            let pubk = Secp256r1PublicKey::from_private(&privk);
            let msg = [0x11u8; 32];
            let sig = privk.sign_digest(&msg).unwrap();
            let wrong_msg = [0x22u8; 32];
            crosscheck(
                &format!(
                    "(secp256r1-verify 0x{} 0x{} 0x{})",
                    to_hex(&wrong_msg),
                    to_hex(&sig.0),
                    to_hex(&pubk.to_bytes_compressed())
                ),
                Ok(Some(Value::Bool(false))),
            );
        }

        #[test]
        fn wrong_key() {
            let privk = Secp256r1PrivateKey::from_seed(&[1u8; 32]);
            let msg = [0x11u8; 32];
            let sig = privk.sign_digest(&msg).unwrap();
            let other_pub =
                Secp256r1PublicKey::from_private(&Secp256r1PrivateKey::from_seed(&[2u8; 32]));
            crosscheck(
                &format!(
                    "(secp256r1-verify 0x{} 0x{} 0x{})",
                    to_hex(&msg),
                    to_hex(&sig.0),
                    to_hex(&other_pub.to_bytes_compressed())
                ),
                Ok(Some(Value::Bool(false))),
            );
        }

        #[test]
        fn double_hash_signature_is_rejected() {
            // A signature produced for the double-hashing scheme (`sign`) must
            // not verify under the simple-hashing scheme.
            let privk = Secp256r1PrivateKey::from_seed(&[1u8; 32]);
            let pubk = Secp256r1PublicKey::from_private(&privk);
            let msg = [0x11u8; 32];
            let sig = privk.sign(&msg).unwrap();
            crosscheck(
                &format!(
                    "(secp256r1-verify 0x{} 0x{} 0x{})",
                    to_hex(&msg),
                    to_hex(&sig.0),
                    to_hex(&pubk.to_bytes_compressed())
                ),
                Ok(Some(Value::Bool(false))),
            );
        }
    }
}
