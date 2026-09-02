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
    use clarity::vm::Value;
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
    }
}
