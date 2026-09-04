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

#[derive(Debug)]
pub struct GetTxOutput;

impl Word for GetTxOutput {
    fn name(&self) -> ClarityName {
        ClarityName::from_literal("get-bitcoin-tx-output?")
    }
}

impl ComplexWord for GetTxOutput {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 2, args.len(), ArgumentCountCheck::Exact);

        generator.traverse_expr(builder, args.get_expr(0)?)?;

        // `vout`, pushed as the low/high `i64` pair of a Clarity `uint`
        generator.traverse_expr(builder, args.get_expr(1)?)?;

        // Reserve stack space for the host-function to write the result
        let ret_ty = generator
            .get_expr_type(expr)
            .ok_or_else(|| {
                GeneratorError::TypeError(
                    "result of get-bitcoin-tx-output? should be typed".to_owned(),
                )
            })?
            .clone();

        let (result_local, result_size) =
            generator.create_call_stack_local(builder, &ret_ty, true, true);
        builder.local_get(result_local).i32_const(result_size);

        // Call the host interface function, `get_bitcoin_tx_output`
        builder.call(generator.func_by_name("stdlib.get_bitcoin_tx_output"));

        generator.read_from_memory(builder, result_local, 0, &ret_ty)?;

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
    use clarity::util::hash::{to_hex, Sha256Sum};
    use clarity::vm::errors::{RuntimeCheckErrorKind, VmExecutionError};
    use clarity::vm::types::{
        BuffData, BufferLength, SequenceData, SequenceSubtype, TupleData, TypeSignature,
    };
    use clarity::vm::{ClarityName, Value};

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

    /// A minimal non-SegWit tx: version 1, one input, one P2WPKH output of
    /// 1000 sats, locktime 0.
    const SAMPLE_TX: &str = concat!(
        "01000000",                                                         // version
        "01",                                                               // n_in
        "0000000000000000000000000000000000000000000000000000000000000000", // prev txid
        "00000000",                                                         // prev vout
        "00",                                                               // scriptSig len
        "ffffffff",                                                         // sequence
        "01",                                                               // n_out
        "e803000000000000",                                                 // amount = 1000
        "16",                                                               // script len = 22
        "0014aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",                     // P2WPKH
        "00000000",                                                         // locktime
    );
    const SAMPLE_SCRIPT: &str = "0014aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    /// Internal byte order, i.e. the raw double-SHA-256 of `SAMPLE_TX`.
    const SAMPLE_TXID: &str = "026ac2ecda2e5b8be7e9ba0658e9bebe75671fe06335116a4c6712bc822438e4";

    /// The same transaction serialized with a SegWit marker, flag and witness
    /// stack. The witness is excluded from the txid preimage, so this yields
    /// the same txid as `SAMPLE_TX`.
    const SAMPLE_TX_SEGWIT: &str = concat!(
        "01000000",                                                         // version
        "0001",                                                             // marker + flag
        "01",                                                               // n_in
        "0000000000000000000000000000000000000000000000000000000000000000", // prev txid
        "00000000",                                                         // prev vout
        "00",                                                               // scriptSig len
        "ffffffff",                                                         // sequence
        "01",                                                               // n_out
        "e803000000000000",                                                 // amount = 1000
        "16",                                                               // script len = 22
        "0014aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",                     // P2WPKH
        "01",                                                               // 1 witness item
        "02",                                                               // item length
        "5151",                                                             // OP_1 OP_1
        "00000000",                                                         // locktime
    );

    /// The Bitcoin genesis block coinbase transaction. Its txid is
    /// [`GENESIS_TXID`].
    const GENESIS_COINBASE: &str = concat!(
        "01000000010000000000000000000000000000000000000000000000000000000000000000ffffffff4d",
        "04ffff001d0104455468652054696d65732030332f4a616e2f32303039204368616e63656c6c6f72206f",
        "6e206272696e6b206f66207365636f6e64206261696c6f757420666f722062616e6b73ffffffff0100f2",
        "052a01000000434104678afdb0fe5548271967f1a67130b7105cd6a828e03909a67962e0ea1f61deb649",
        "f6bc3f4cef38c4f35504e51ec112de5c384df7ba0b8d578a4c702b6bf11d5fac00000000",
    );
    const GENESIS_SCRIPT: &str = concat!(
        "4104678afdb0fe5548271967f1a67130b7105cd6a828e03909a67962e0ea1f61deb649f6bc3f4cef38c4",
        "f35504e51ec112de5c384df7ba0b8d578a4c702b6bf11d5fac",
    );

    /// The expected `(ok { script, amount, txid })` value.
    fn expect_output(
        script: &str,
        amount: u128,
        txid: &str,
    ) -> Result<Option<Value>, VmExecutionError> {
        let tuple = TupleData::from_data(vec![
            (
                ClarityName::from_literal("script"),
                Value::buff_from(hex::decode(script).unwrap()).unwrap(),
            ),
            (ClarityName::from_literal("amount"), Value::UInt(amount)),
            (
                ClarityName::from_literal("txid"),
                Value::buff_from(hex::decode(txid).unwrap()).unwrap(),
            ),
        ])
        .unwrap();
        Ok(Some(Value::okay(Value::Tuple(tuple)).unwrap()))
    }

    /// Bitcoin's double-SHA-256, in internal byte order. For a non-SegWit
    /// transaction the txid preimage is the raw serialization.
    fn txid_of(raw: &[u8]) -> String {
        to_hex(&Sha256Sum::from_data(Sha256Sum::from_data(raw).as_bytes()).0)
    }

    /// A single-output tx whose `scriptPubKey` is `script_len` bytes of OP_1.
    fn tx_with_script_of_len(script_len: usize) -> Vec<u8> {
        let mut raw = hex::decode(concat!(
            "01000000",                                                         // version
            "01",                                                               // n_in
            "0000000000000000000000000000000000000000000000000000000000000000", // prev txid
            "00000000",                                                         // prev vout
            "00",                                                               // scriptSig len
            "ffffffff",                                                         // sequence
            "01",                                                               // n_out
            "e803000000000000",                                                 // amount = 1000
        ))
        .unwrap();
        // CompactSize length prefix, always in the 0xfd + u16 range here
        raw.push(0xfd);
        raw.extend_from_slice(&(script_len as u16).to_le_bytes());
        raw.extend(std::iter::repeat_n(0x51u8, script_len));
        raw.extend_from_slice(&[0, 0, 0, 0]); // locktime
        raw
    }

    #[test]
    fn less_than_two_args() {
        let result = evaluate(&format!("(get-bitcoin-tx-output? 0x{SAMPLE_TX})"));
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 1"));
    }

    #[test]
    fn more_than_two_args() {
        let result = evaluate(&format!("(get-bitcoin-tx-output? 0x{SAMPLE_TX} u0 u0)"));
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 3"));
    }

    #[test]
    fn non_segwit_output() {
        crosscheck(
            &format!("(get-bitcoin-tx-output? 0x{SAMPLE_TX} u0)"),
            expect_output(SAMPLE_SCRIPT, 1000, SAMPLE_TXID),
        );
    }

    #[test]
    fn segwit_output_has_the_same_txid() {
        crosscheck(
            &format!("(get-bitcoin-tx-output? 0x{SAMPLE_TX_SEGWIT} u0)"),
            expect_output(SAMPLE_SCRIPT, 1000, SAMPLE_TXID),
        );
    }

    #[test]
    fn genesis_coinbase() {
        crosscheck(
            &format!("(get-bitcoin-tx-output? 0x{GENESIS_COINBASE} u0)"),
            expect_output(GENESIS_SCRIPT, 5_000_000_000, GENESIS_TXID),
        );
    }

    /// `(err u1)`: the bytes do not deserialize as a Bitcoin transaction.
    #[test]
    fn truncated_tx_is_err_u1() {
        let truncated = &SAMPLE_TX[..SAMPLE_TX.len() - 2];
        crosscheck(
            &format!("(get-bitcoin-tx-output? 0x{truncated} u0)"),
            Ok(Some(Value::err_uint(1))),
        );
    }

    #[test]
    fn empty_tx_is_err_u1() {
        crosscheck(
            "(get-bitcoin-tx-output? 0x u0)",
            Ok(Some(Value::err_uint(1))),
        );
    }

    /// `(err u2)`: the transaction parses, but has no such output.
    #[test]
    fn vout_out_of_range_is_err_u2() {
        crosscheck(
            &format!("(get-bitcoin-tx-output? 0x{SAMPLE_TX} u1)"),
            Ok(Some(Value::err_uint(2))),
        );
    }

    /// A `vout` past `u64::MAX` is out of range rather than a truncation.
    #[test]
    fn huge_vout_is_err_u2() {
        crosscheck(
            &format!(
                "(get-bitcoin-tx-output? 0x{SAMPLE_TX} u340282366920938463463374607431768211455)"
            ),
            Ok(Some(Value::err_uint(2))),
        );
    }

    /// `(err u3)`: the output's `scriptPubKey` is over the 1024-byte cap.
    #[test]
    fn oversized_script_is_err_u3() {
        let raw = tx_with_script_of_len(1025);
        crosscheck(
            &format!("(get-bitcoin-tx-output? 0x{} u0)", to_hex(&raw)),
            Ok(Some(Value::err_uint(3))),
        );
    }

    /// A `scriptPubKey` of exactly 1024 bytes is still accepted.
    #[test]
    fn script_at_the_size_limit_is_accepted() {
        let raw = tx_with_script_of_len(1024);
        crosscheck(
            &format!("(get-bitcoin-tx-output? 0x{} u0)", to_hex(&raw)),
            expect_output(&"51".repeat(1024), 1000, &txid_of(&raw)),
        );
    }
}
