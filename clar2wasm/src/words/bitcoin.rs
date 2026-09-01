use clarity::vm::{ClarityName, SymbolicExpression};

use super::{ComplexWord, Word};
use crate::check_args;
use crate::wasm_generator::{ArgumentsExt, GeneratorError, WasmGenerator};
use crate::wasm_utils::ArgumentCountCheck;

#[derive(Debug)]
pub struct VerifyMerkleProof;

impl Word for VerifyMerkleProof {
    fn name(&self) -> ClarityName {
        ClarityName::from_literal("verify-merkle-proof")
    }
}

impl ComplexWord for VerifyMerkleProof {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 5, args.len(), ArgumentCountCheck::Exact);

        generator.traverse_expr(builder, args.get_expr(0)?)?;
        generator.traverse_expr(builder, args.get_expr(1)?)?;
        generator.traverse_expr(builder, args.get_expr(2)?)?;
        generator.traverse_expr(builder, args.get_expr(3)?)?;
        generator.traverse_expr(builder, args.get_expr(4)?)?;

        // Call the host interface function, `verify_merkle_proof`
        builder.call(generator.func_by_name("stdlib.verify_merkle_proof"));

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
    use clarity::vm::errors::{RuntimeCheckErrorKind, VmExecutionError};
    use clarity::vm::types::{
        BuffData, BufferLength, SequenceData, SequenceSubtype, TypeSignature,
    };
    use clarity::vm::Value;

    use crate::tools::{crosscheck, evaluate};

    /// The Bitcoin genesis block holds a single transaction, so its coinbase
    /// txid (internal byte order) is also the block's merkle root.
    const GENESIS_TXID: &str = "3ba3edfd7a7b12b27ac72c3e67768f617fc81bc3888a51323a9fb8aa4b1e5e4a";

    // Leaves of the hand-built trees below.
    const A: &str = "1111111111111111111111111111111111111111111111111111111111111111";
    const B: &str = "2222222222222222222222222222222222222222222222222222222222222222";
    const C: &str = "3333333333333333333333333333333333333333333333333333333333333333";

    /// Root of the two-leaf tree `[A, B]`, i.e. `dSHA256(A || B)`.
    const ROOT_AB: &str = "1140b574afee3cb89a4db3dc8037acfa856f5112e68a954e3ca0a908082c98ba";
    /// `dSHA256(C || C)`: the odd row `[H(A||B), H(C||C)]` duplicates the last
    /// node, per Bitcoin's merkle rule.
    const HCC: &str = "ee99b53b490294fac3f1f92699211740853452f355b51a82240c75688ce6204d";
    /// Root of the three-leaf tree `[A, B, C]`.
    const ROOT_ABC: &str = "cacd895c5e82f37a37b6f4923c214ca6089e5f7b075b9fca7e11e782a0f3f5e6";

    #[test]
    fn less_than_five_args() {
        let result = evaluate(&format!(
            "(verify-merkle-proof 0x{GENESIS_TXID} 0x{GENESIS_TXID} u0 u1)"
        ));
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 5 arguments, got 4"));
    }

    #[test]
    fn more_than_five_args() {
        let result = evaluate(&format!(
            "(verify-merkle-proof 0x{GENESIS_TXID} 0x{GENESIS_TXID} u0 u1 (list) u0)"
        ));
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 5 arguments, got 6"));
    }

    /// The example from SIP-044: a single-transaction block verifies with an
    /// empty sibling list.
    #[test]
    fn single_tx_block() {
        crosscheck(
            &format!("(verify-merkle-proof 0x{GENESIS_TXID} 0x{GENESIS_TXID} u0 u1 (list))"),
            Ok(Some(Value::Bool(true))),
        );
    }

    #[test]
    fn two_leaf_tree_left() {
        crosscheck(
            &format!("(verify-merkle-proof 0x{A} 0x{ROOT_AB} u0 u2 (list 0x{B}))"),
            Ok(Some(Value::Bool(true))),
        );
    }

    #[test]
    fn two_leaf_tree_right() {
        crosscheck(
            &format!("(verify-merkle-proof 0x{B} 0x{ROOT_AB} u1 u2 (list 0x{A}))"),
            Ok(Some(Value::Bool(true))),
        );
    }

    /// The sibling is correct but the index says the leaf is on the other
    /// side, so the pair hashes in the wrong order.
    #[test]
    fn wrong_index_is_false() {
        crosscheck(
            &format!("(verify-merkle-proof 0x{A} 0x{ROOT_AB} u1 u2 (list 0x{B}))"),
            Ok(Some(Value::Bool(false))),
        );
    }

    /// An odd row duplicates its last node: `C` pairs with itself.
    #[test]
    fn three_leaf_tree_padded_leaf() {
        crosscheck(
            &format!("(verify-merkle-proof 0x{C} 0x{ROOT_ABC} u2 u3 (list 0x{C} 0x{ROOT_AB}))"),
            Ok(Some(Value::Bool(true))),
        );
    }

    #[test]
    fn three_leaf_tree_first_leaf() {
        crosscheck(
            &format!("(verify-merkle-proof 0x{A} 0x{ROOT_ABC} u0 u3 (list 0x{B} 0x{HCC}))"),
            Ok(Some(Value::Bool(true))),
        );
    }

    /// `tx-index` must be less than `tx-count`.
    #[test]
    fn index_beyond_tx_count_is_false() {
        crosscheck(
            &format!("(verify-merkle-proof 0x{A} 0x{ROOT_AB} u2 u2 (list 0x{B}))"),
            Ok(Some(Value::Bool(false))),
        );
    }

    #[test]
    fn zero_tx_count_is_false() {
        crosscheck(
            &format!("(verify-merkle-proof 0x{A} 0x{A} u0 u0 (list))"),
            Ok(Some(Value::Bool(false))),
        );
    }

    /// The path length has to match `ceil(log2(tx-count))`.
    #[test]
    fn wrong_path_length_is_false() {
        crosscheck(
            &format!("(verify-merkle-proof 0x{A} 0x{ROOT_AB} u0 u2 (list 0x{B} 0x{C}))"),
            Ok(Some(Value::Bool(false))),
        );
    }

    /// CVE-2012-2459: outside the duplicated-padding slot a sibling equal to
    /// the running hash would require duplicate leaves, so it is rejected.
    #[test]
    fn self_paired_sibling_is_false() {
        crosscheck(
            &format!("(verify-merkle-proof 0x{A} 0x{ROOT_AB} u0 u2 (list 0x{A}))"),
            Ok(Some(Value::Bool(false))),
        );
    }

    /// A sibling that is not a 32-byte buffer makes the proof structurally
    /// invalid, which is `false` rather than a runtime error.
    #[test]
    fn short_sibling_is_false() {
        let short = &B[..62];
        crosscheck(
            &format!("(verify-merkle-proof 0x{A} 0x{ROOT_AB} u0 u2 (list 0x{short}))"),
            Ok(Some(Value::Bool(false))),
        );
    }

    /// A leaf that is not 32 bytes is an argument-shape error, not a failed
    /// proof.
    #[test]
    fn short_leaf_is_a_runtime_error() {
        let short = &A[..62];
        crosscheck(
            &format!("(verify-merkle-proof 0x{short} 0x{ROOT_AB} u0 u2 (list 0x{B}))"),
            Err(VmExecutionError::RuntimeCheck(
                RuntimeCheckErrorKind::TypeValueError(
                    Box::new(TypeSignature::SequenceType(SequenceSubtype::BufferType(
                        BufferLength::try_from(32_u32).unwrap(),
                    ))),
                    Value::Sequence(SequenceData::Buffer(BuffData {
                        data: hex::decode(short).unwrap(),
                    }))
                    .to_error_string(),
                ),
            )),
        );
    }

    #[test]
    fn short_root_is_a_runtime_error() {
        let short = &ROOT_AB[..62];
        crosscheck(
            &format!("(verify-merkle-proof 0x{A} 0x{short} u0 u2 (list 0x{B}))"),
            Err(VmExecutionError::RuntimeCheck(
                RuntimeCheckErrorKind::TypeValueError(
                    Box::new(TypeSignature::SequenceType(SequenceSubtype::BufferType(
                        BufferLength::try_from(32_u32).unwrap(),
                    ))),
                    Value::Sequence(SequenceData::Buffer(BuffData {
                        data: hex::decode(short).unwrap(),
                    }))
                    .to_error_string(),
                ),
            )),
        );
    }
}
