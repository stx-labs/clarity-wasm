#[cfg(not(any(
    feature = "test-clarity-v1",
    feature = "test-clarity-v2",
    feature = "test-clarity-v3",
    feature = "test-clarity-v4",
    feature = "test-clarity-v5"
)))]
mod clarity_v6 {
    use clar2wasm::tools::{crosscheck, crosscheck_validate};
    use clarity::util::hash::{to_hex, Sha256Sum};
    use clarity::vm::types::TupleData;
    use clarity::vm::{ClarityName, Value};
    use proptest::prelude::*;

    /// Bitcoin's double-SHA-256.
    fn dsha256(bytes: &[u8]) -> [u8; 32] {
        Sha256Sum::from_data(Sha256Sum::from_data(bytes).as_bytes()).0
    }

    /// Build the canonical Bitcoin merkle tree over `leaves`, returning the
    /// root and the sibling path for `index`.
    fn merkle_path(leaves: &[[u8; 32]], index: usize) -> ([u8; 32], Vec<[u8; 32]>) {
        let mut row: Vec<[u8; 32]> = leaves.to_vec();
        let mut idx = index;
        let mut siblings = Vec::new();
        while row.len() > 1 {
            // Odd rows duplicate their last node.
            let sibling_idx = if idx ^ 1 < row.len() { idx ^ 1 } else { idx };
            siblings.push(row[sibling_idx]);
            let mut next = Vec::with_capacity(row.len().div_ceil(2));
            for pair in row.chunks(2) {
                let left = pair[0];
                let right = *pair.get(1).unwrap_or(&pair[0]);
                let mut buf = [0u8; 64];
                buf[..32].copy_from_slice(&left);
                buf[32..].copy_from_slice(&right);
                next.push(dsha256(&buf));
            }
            row = next;
            idx /= 2;
        }
        (row[0], siblings)
    }

    fn hash_list(hashes: &[[u8; 32]]) -> String {
        if hashes.is_empty() {
            "(list)".to_string()
        } else {
            let items: Vec<String> = hashes.iter().map(|h| format!("0x{}", to_hex(h))).collect();
            format!("(list {})", items.join(" "))
        }
    }

    /// Distinct leaves, so that no two subtrees can collide.
    fn leaves(count: usize) -> Vec<[u8; 32]> {
        (0..count)
            .map(|i| dsha256(&(i as u64).to_le_bytes()))
            .collect()
    }
    /// Serialize a single-output, single-input non-SegWit transaction.
    fn build_tx(amount: u64, script: &[u8]) -> Vec<u8> {
        let mut raw = Vec::new();
        raw.extend_from_slice(&1u32.to_le_bytes()); // version
        raw.push(0x01); // n_in
        raw.extend_from_slice(&[0u8; 32]); // prev txid
        raw.extend_from_slice(&[0u8; 4]); // prev vout
        raw.push(0x00); // scriptSig len
        raw.extend_from_slice(&[0xff; 4]); // sequence
        raw.push(0x01); // n_out
        raw.extend_from_slice(&amount.to_le_bytes());
        if script.len() < 0xfd {
            raw.push(script.len() as u8);
        } else {
            raw.push(0xfd);
            raw.extend_from_slice(&(script.len() as u16).to_le_bytes());
        }
        raw.extend_from_slice(script);
        raw.extend_from_slice(&[0u8; 4]); // locktime
        raw
    }

    /// Bitcoin's double-SHA-256, in internal byte order.
    fn txid_of(raw: &[u8]) -> Vec<u8> {
        Sha256Sum::from_data(Sha256Sum::from_data(raw).as_bytes())
            .0
            .to_vec()
    }

    proptest! {
        #![proptest_config(crate::runtime_config())]

        /// Every leaf of a canonical tree verifies against its own path.
        #[test]
        fn crossprop_verify_merkle_proof_valid(tx_count in 1usize..=40, seed in any::<u8>()) {
            let all = leaves(tx_count);
            let index = (seed as usize) % tx_count;
            let (root, siblings) = merkle_path(&all, index);
            crosscheck(
                &format!(
                    "(verify-merkle-proof 0x{} 0x{} u{index} u{tx_count} {})",
                    to_hex(&all[index]), to_hex(&root), hash_list(&siblings)
                ),
                Ok(Some(Value::Bool(true)))
            );
        }

        /// Pointing a valid path at the wrong leaf never verifies.
        #[test]
        fn crossprop_verify_merkle_proof_wrong_leaf(tx_count in 2usize..=40, seed in any::<u8>()) {
            let all = leaves(tx_count);
            let index = (seed as usize) % tx_count;
            let other = (index + 1) % tx_count;
            let (root, siblings) = merkle_path(&all, index);
            crosscheck(
                &format!(
                    "(verify-merkle-proof 0x{} 0x{} u{index} u{tx_count} {})",
                    to_hex(&all[other]), to_hex(&root), hash_list(&siblings)
                ),
                Ok(Some(Value::Bool(false)))
            );
        }

        /// A path whose length does not match `ceil(log2(tx-count))` is
        /// rejected outright.
        #[test]
        fn crossprop_verify_merkle_proof_truncated_path(tx_count in 3usize..=40, seed in any::<u8>()) {
            let all = leaves(tx_count);
            let index = (seed as usize) % tx_count;
            let (root, mut siblings) = merkle_path(&all, index);
            siblings.pop();
            crosscheck(
                &format!(
                    "(verify-merkle-proof 0x{} 0x{} u{index} u{tx_count} {})",
                    to_hex(&all[index]), to_hex(&root), hash_list(&siblings)
                ),
                Ok(Some(Value::Bool(false)))
            );
        }

        /// Arbitrary hashes and counts: whatever the outcome, the compiled
        /// version must agree with the interpreter.
        #[test]
        fn crossprop_verify_merkle_proof_arbitrary(
            leaf in any::<[u8; 32]>(),
            root in any::<[u8; 32]>(),
            tx_index in any::<u128>(),
            tx_count in any::<u128>(),
            siblings in prop::collection::vec(any::<[u8; 32]>(), 0..=24))
        {
            crosscheck_validate(
                &format!(
                    "(verify-merkle-proof 0x{} 0x{} u{tx_index} u{tx_count} {})",
                    to_hex(&leaf), to_hex(&root), hash_list(&siblings)
                ),
                |_|{}
            )
        }
        /// Arbitrary bytes are almost never a valid transaction, but whatever
        /// the outcome, the compiled version must agree with the interpreter.
        #[test]
        fn crossprop_get_bitcoin_tx_output_arbitrary_bytes(
            raw in prop::collection::vec(any::<u8>(), 0usize..=128usize),
            vout in 0u32..4)
        {
            crosscheck_validate(
                &format!("(get-bitcoin-tx-output? 0x{} u{vout})", to_hex(&raw)), |_|{}
            )
        }

        /// A well-formed transaction round-trips to its own output.
        #[test]
        fn crossprop_get_bitcoin_tx_output_valid_tx(
            amount in any::<u64>(),
            script in prop::collection::vec(any::<u8>(), 0usize..=1024usize))
        {
            let raw = build_tx(amount, &script);
            let tuple = TupleData::from_data(vec![
                (ClarityName::from_literal("script"), Value::buff_from(script).unwrap()),
                (ClarityName::from_literal("amount"), Value::UInt(u128::from(amount))),
                (ClarityName::from_literal("txid"), Value::buff_from(txid_of(&raw)).unwrap()),
            ]).unwrap();

            crosscheck(
                &format!("(get-bitcoin-tx-output? 0x{} u0)", to_hex(&raw)),
                Ok(Some(Value::okay(Value::Tuple(tuple)).unwrap()))
            );
        }

        /// The transaction has exactly one output, so every other index is
        /// out of range.
        #[test]
        fn crossprop_get_bitcoin_tx_output_out_of_range(
            amount in any::<u64>(),
            script in prop::collection::vec(any::<u8>(), 0usize..=64usize),
            vout in 1u128..=u128::MAX)
        {
            let raw = build_tx(amount, &script);
            crosscheck(
                &format!("(get-bitcoin-tx-output? 0x{} u{vout})", to_hex(&raw)),
                Ok(Some(Value::err_uint(2)))
            );
        }

        /// Anything over the 1024-byte `scriptPubKey` cap is `(err u3)`.
        #[test]
        fn crossprop_get_bitcoin_tx_output_oversized_script(
            amount in any::<u64>(),
            extra in 1usize..=512usize)
        {
            let raw = build_tx(amount, &vec![0x51u8; 1024 + extra]);
            crosscheck(
                &format!("(get-bitcoin-tx-output? 0x{} u0)", to_hex(&raw)),
                Ok(Some(Value::err_uint(3)))
            );
        }
    }
}
