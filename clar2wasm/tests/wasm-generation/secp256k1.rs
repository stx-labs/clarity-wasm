use std::ops::RangeInclusive;

use clar2wasm::tools::{crosscheck, crosscheck_validate};
use clarity::types::PrivateKey;
use clarity::util::hash::to_hex;
use clarity::util::secp256k1::{Secp256k1PrivateKey, Secp256k1PublicKey};
use clarity::vm::types::{SequenceSubtype, TypeSignature};
use clarity::vm::Value;
use proptest::prelude::*;
use proptest::proptest;
use proptest::strategy::Strategy;

use crate::{buffer, PropValue};

fn buffer_range(len_range: RangeInclusive<u32>) -> impl Strategy<Value = PropValue> {
    len_range
        .prop_map(|s| {
            TypeSignature::SequenceType(SequenceSubtype::BufferType(s.try_into().unwrap()))
        })
        .prop_flat_map(PropValue::from_type)
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn crossprop_secp256k1_recover_generic(msg in buffer(32), sig in buffer(65))
    {
        crosscheck_validate(
            &format!("(secp256k1-recover? {msg} {sig})"), |_|{}
        )
    }

    #[test]
    fn crossprop_secp256k1_recover_recid(msg in buffer(32), sig in buffer(64))
    {
        for recid in 0..4 {
            crosscheck_validate(
                &format!("(secp256k1-recover? {msg} {sig}{recid:02X})"), |_|{}
            )
        }
    }

    #[test]
    fn crossprop_secp256k1_recover_recid_23(msg in buffer(32), sig in buffer(48))
    {
        // Generate "low" R signatures to hope for valid recovery_id=(2|3) values
        for recid in 0..4 {
            crosscheck_validate(
                &format!("(secp256k1-recover? {msg} 0x00000000000000000000000000000000{}{recid:02X})", &sig.to_string()[2..]), |_|{}
            )
        }
    }

    #[test]
    fn crossprop_secp256k1_verify_generic(msg in buffer(32), sig in buffer_range(64..=65), pkey in buffer(33))
    {
        crosscheck_validate(
            &format!("(secp256k1-verify {msg} {sig} {pkey})"), |_|{}
        )
    }

    #[test]
    fn crossprop_secp256k1_verify_correct_sig(
        msg in prop::collection::vec(any::<u8>(), 32usize..=32usize),
        private_key in prop::collection::vec(any::<u8>(), 32usize..=32usize))
    {
        let mut key = Secp256k1PrivateKey::from_slice(&private_key).unwrap();
        key.set_compress_public(true);
        let sig = key.sign(&msg).unwrap().to_secp256k1_recoverable().unwrap();
        let (recid, sig) = sig.serialize_compact();

        // with recovery id
        crosscheck(
            &format!("(secp256k1-verify 0x{} 0x{}{:02X} 0x{})",
                to_hex(&msg),
                to_hex(&sig),
                recid.to_i32(),
                Secp256k1PublicKey::from_private(&key).to_hex()),
            Ok(Some(Value::Bool(true)))
        );

        // without recovery id
        crosscheck(
            &format!("(secp256k1-verify 0x{} 0x{} 0x{})",
                to_hex(&msg),
                to_hex(&sig),
                Secp256k1PublicKey::from_private(&key).to_hex()),
            Ok(Some(Value::Bool(true)))
        );

        // with some other recovery id
        crosscheck(
            &format!("(secp256k1-verify 0x{} 0x{}{:02X} 0x{})",
                to_hex(&msg),
                to_hex(&sig),
                (recid.to_i32() + 1) % 4,
                Secp256k1PublicKey::from_private(&key).to_hex()),
            Ok(Some(Value::Bool(true)))
        );
    }

    #[test]
    fn crossprop_secp256k1_verify_alter_recid(
        msg in prop::collection::vec(any::<u8>(), 32usize..=32usize),
        private_key in prop::collection::vec(any::<u8>(), 32usize..=32usize),
        recid in any::<u8>())
    {
        let mut key = Secp256k1PrivateKey::from_slice(&private_key).unwrap();
        key.set_compress_public(true);
        let sig = key.sign(&msg).unwrap().to_secp256k1_recoverable().unwrap();
        let (_, sig) = sig.serialize_compact();

        crosscheck_validate(
            &format!("(secp256k1-verify 0x{} 0x{}{:02X} 0x{})",
                to_hex(&msg),
                to_hex(&sig),
                recid,
                Secp256k1PublicKey::from_private(&key).to_hex()),
            |_|{}
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
    fn crossprop_secp256k1_decompress_generic(msg in buffer(33))
    {
        crosscheck_validate(
            &format!("(secp256k1-decompress? {msg})"), |_|{}
        )
    }

    #[cfg(not(any(
        feature = "test-clarity-v1",
        feature = "test-clarity-v2",
        feature = "test-clarity-v3",
        feature = "test-clarity-v4",
        feature = "test-clarity-v5"
    )))]
    #[test]
    fn crossprop_secp256k1_decompress_real_key(
        private_key in prop::collection::vec(any::<u8>(), 32usize..=32usize))
    {
        use clarity::types::PublicKey;
        let mut key = Secp256k1PrivateKey::from_slice(&private_key).unwrap();

        key.set_compress_public(true);
        let compressed = Secp256k1PublicKey::from_private(&key).to_bytes_compressed();
        key.set_compress_public(false);
        let uncompressed = Secp256k1PublicKey::from_private(&key).to_bytes();

        crosscheck(
            &format!("(secp256k1-decompress? 0x{})", to_hex(&compressed)),
            Ok(Some(Value::okay(Value::buff_from(uncompressed).unwrap()).unwrap()))
        );
    }

}
