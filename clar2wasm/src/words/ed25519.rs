use clarity::vm::{ClarityName, SymbolicExpression};

use super::{ComplexWord, Word};
use crate::check_args;
use crate::wasm_generator::{ArgumentsExt, GeneratorError, WasmGenerator};
use crate::wasm_utils::ArgumentCountCheck;

#[derive(Debug)]
pub struct Verify;

impl Word for Verify {
    fn name(&self) -> ClarityName {
        ClarityName::from_literal("ed25519-verify")
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

        generator.traverse_expr(builder, args.get_expr(0)?)?;

        // The signature and the public key are fixed-size buffers: the host
        // function checks their length and throws a runtime error if needed.
        generator.traverse_expr(builder, args.get_expr(1)?)?;
        generator.traverse_expr(builder, args.get_expr(2)?)?;

        // Call the host interface function, `ed25519_verify`
        builder.call(generator.func_by_name("stdlib.ed25519_verify"));

        Ok(())
    }
}

#[cfg(test)]
#[cfg(not(any(
    feature = "test-clarity-v1",
    feature = "test-clarity-v2",
    feature = "test-clarity-v3",
    feature = "test-clarity-v4",
    feature = "test-clarity-v5"
)))]
mod tests {
    use clarity::util::hash::to_hex;
    use clarity::vm::errors::{RuntimeCheckErrorKind, VmExecutionError};
    use clarity::vm::types::{
        BuffData, BufferLength, SequenceData, SequenceSubtype, TypeSignature,
    };
    use clarity::vm::Value;
    use stacks_common::util::ed25519::{Ed25519PrivateKey, Ed25519PublicKey};

    use crate::tools::{crosscheck, evaluate};

    /// [RFC 8032], section 7.1, TEST 2.
    ///
    /// [RFC 8032]: https://datatracker.ietf.org/doc/html/rfc8032#section-7.1
    const RFC8032_MESSAGE: &str = "0x72";
    const RFC8032_SIGNATURE: &str = "0x92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00";
    const RFC8032_PUBLIC_KEY: &str =
        "0x3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c";

    #[test]
    fn less_than_three_args() {
        let result = evaluate(&format!(
            "(ed25519-verify {RFC8032_MESSAGE} {RFC8032_SIGNATURE})"
        ));
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 3 arguments, got 2"));
    }

    #[test]
    fn more_than_three_args() {
        let result = evaluate(&format!(
            "(ed25519-verify {RFC8032_MESSAGE} {RFC8032_SIGNATURE} {RFC8032_PUBLIC_KEY} {RFC8032_PUBLIC_KEY})"
        ));
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 3 arguments, got 4"));
    }

    #[test]
    fn rfc8032_test_vector() {
        crosscheck(
            &format!("(ed25519-verify {RFC8032_MESSAGE} {RFC8032_SIGNATURE} {RFC8032_PUBLIC_KEY})"),
            Ok(Some(Value::Bool(true))),
        );
    }

    /// [RFC 8032], section 7.1, TEST 1: the message is empty.
    ///
    /// [RFC 8032]: https://datatracker.ietf.org/doc/html/rfc8032#section-7.1
    #[test]
    fn rfc8032_empty_message() {
        crosscheck(
            "(ed25519-verify 0x \
             0xe5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b \
             0xd75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a)",
            Ok(Some(Value::Bool(true))),
        );
    }

    #[test]
    fn wrong_message() {
        crosscheck(
            &format!("(ed25519-verify 0x73 {RFC8032_SIGNATURE} {RFC8032_PUBLIC_KEY})"),
            Ok(Some(Value::Bool(false))),
        );
    }

    #[test]
    fn wrong_public_key() {
        let other_pub =
            Ed25519PublicKey::from_private(&Ed25519PrivateKey::from_seed(&[0x42u8; 32]));
        crosscheck(
            &format!(
                "(ed25519-verify {RFC8032_MESSAGE} {RFC8032_SIGNATURE} 0x{})",
                to_hex(&other_pub.to_bytes())
            ),
            Ok(Some(Value::Bool(false))),
        );
    }

    #[test]
    fn round_trip_with_a_long_message() {
        let privk = Ed25519PrivateKey::from_seed(&[1u8; 32]);
        let pubk = Ed25519PublicKey::from_private(&privk);
        let msg = vec![0xabu8; 1000];
        let sig = privk.sign(&msg).unwrap();
        crosscheck(
            &format!(
                "(ed25519-verify 0x{} 0x{} 0x{})",
                to_hex(&msg),
                to_hex(&sig.0),
                to_hex(&pubk.to_bytes())
            ),
            Ok(Some(Value::Bool(true))),
        );
    }

    /// Verification runs in strict mode: a signature whose `s` component is not
    /// in canonical range is rejected instead of being accepted as a variant of
    /// a valid signature.
    #[test]
    fn non_canonical_signature_is_rejected() {
        let privk = Ed25519PrivateKey::from_seed(&[1u8; 32]);
        let pubk = Ed25519PublicKey::from_private(&privk);
        let msg = [0x11u8; 32];
        let mut sig = privk.sign(&msg).unwrap().0;
        // `s` is stored little-endian in the upper half of the signature, and
        // its top bits must be clear for the signature to be canonical.
        sig[63] |= 0b1110_0000;
        crosscheck(
            &format!(
                "(ed25519-verify 0x{} 0x{} 0x{})",
                to_hex(&msg),
                to_hex(&sig),
                to_hex(&pubk.to_bytes())
            ),
            Ok(Some(Value::Bool(false))),
        );
    }

    #[test]
    fn signature_too_short() {
        let short_sig = vec![0u8; 63];
        crosscheck(
            &format!(
                "(ed25519-verify {RFC8032_MESSAGE} 0x{} {RFC8032_PUBLIC_KEY})",
                to_hex(&short_sig)
            ),
            Err(VmExecutionError::RuntimeCheck(
                RuntimeCheckErrorKind::TypeValueError(
                    Box::new(TypeSignature::SequenceType(SequenceSubtype::BufferType(
                        BufferLength::try_from(64_u32).unwrap(),
                    ))),
                    Value::Sequence(SequenceData::Buffer(BuffData { data: short_sig }))
                        .to_error_string(),
                ),
            )),
        );
    }

    #[test]
    fn public_key_too_short() {
        let short_pubkey = vec![0xcdu8; 31];
        crosscheck(
            &format!(
                "(ed25519-verify {RFC8032_MESSAGE} {RFC8032_SIGNATURE} 0x{})",
                to_hex(&short_pubkey)
            ),
            Err(VmExecutionError::RuntimeCheck(
                RuntimeCheckErrorKind::TypeValueError(
                    Box::new(TypeSignature::SequenceType(SequenceSubtype::BufferType(
                        BufferLength::try_from(32_u32).unwrap(),
                    ))),
                    Value::Sequence(SequenceData::Buffer(BuffData { data: short_pubkey }))
                        .to_error_string(),
                ),
            )),
        );
    }
}
