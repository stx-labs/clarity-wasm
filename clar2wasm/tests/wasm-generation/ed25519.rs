#[cfg(not(any(
    feature = "test-clarity-v1",
    feature = "test-clarity-v2",
    feature = "test-clarity-v3",
    feature = "test-clarity-v4",
    feature = "test-clarity-v5"
)))]
mod clarity_v6 {
    use clar2wasm::tools::{crosscheck, crosscheck_validate};
    use clarity::util::hash::to_hex;
    use clarity::vm::Value;
    use proptest::prelude::*;
    use stacks_common::util::ed25519::{Ed25519PrivateKey, Ed25519PublicKey};

    use crate::buffer;

    proptest! {
        #![proptest_config(crate::runtime_config())]

        /// Random arguments of the right shape: whatever the outcome, the
        /// compiled version must agree with the interpreter.
        #[test]
        fn crossprop_ed25519_verify_generic(
            msg in buffer(32),
            sig in buffer(64),
            pkey in buffer(32))
        {
            crosscheck_validate(
                &format!("(ed25519-verify {msg} {sig} {pkey})"), |_|{}
            )
        }

        /// A signature produced by the reference implementation always verifies.
        #[test]
        fn crossprop_ed25519_verify_correct_sig(
            msg in prop::collection::vec(any::<u8>(), 0usize..=128usize),
            seed in prop::collection::vec(any::<u8>(), 32usize..=32usize))
        {
            let privk = Ed25519PrivateKey::from_seed(&seed);
            let pubk = Ed25519PublicKey::from_private(&privk);
            let sig = privk.sign(&msg).unwrap();

            crosscheck(
                &format!("(ed25519-verify 0x{} 0x{} 0x{})",
                    to_hex(&msg),
                    to_hex(&sig.0),
                    to_hex(&pubk.to_bytes())),
                Ok(Some(Value::Bool(true)))
            );
        }

        /// Altering a single byte of a valid signature must never verify.
        #[test]
        fn crossprop_ed25519_verify_altered_sig(
            msg in prop::collection::vec(any::<u8>(), 0usize..=128usize),
            seed in prop::collection::vec(any::<u8>(), 32usize..=32usize),
            index in 0usize..64usize,
            xor in 1u8..=255u8)
        {
            let privk = Ed25519PrivateKey::from_seed(&seed);
            let pubk = Ed25519PublicKey::from_private(&privk);
            let mut sig = privk.sign(&msg).unwrap().0;
            sig[index] ^= xor;

            crosscheck(
                &format!("(ed25519-verify 0x{} 0x{} 0x{})",
                    to_hex(&msg),
                    to_hex(&sig),
                    to_hex(&pubk.to_bytes())),
                Ok(Some(Value::Bool(false)))
            );
        }
    }
}
