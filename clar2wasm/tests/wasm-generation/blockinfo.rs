use clar2wasm::tools::crosscheck_compare_only_advancing_tip;
use proptest::proptest;

use crate::{buffer, runtime_config, PropValue};

#[allow(dead_code)]
const BLOCK_INFO_V1: [&str; 5] = [
    "burnchain-header-hash",
    "id-header-hash",
    "header-hash",
    "miner-address",
    "time",
];

const STACKS_BLOCK_HEIGHT_LIMIT: u32 = 100;

//
// Module with tests that should only be executed
// when running Clarity::V1.
//
#[cfg(feature = "test-clarity-v1")]
mod clarity_v1 {
    use super::*;

    proptest! {
        #![proptest_config(runtime_config())]

        #[test]
        fn crossprop_blockinfo_within_controlled_range(block_height in 1..=STACKS_BLOCK_HEIGHT_LIMIT, tip in 1..=80u32) {
            for info in &BLOCK_INFO_V1 {
                crosscheck_compare_only_advancing_tip(&format!("(get-block-info? {info} u{block_height})"), tip)
            }
        }
    }
}

//
// Module with tests that should only be executed
// when running Clarity::V2.
//
#[cfg(feature = "test-clarity-v2")]
mod clarity_v2 {
    use super::*;

    const BLOCK_INFO_V2: [&str; 3] = ["block-reward", "miner-spend-total", "miner-spend-winner"];

    proptest! {
        #![proptest_config(runtime_config())]

        #[test]
        fn crossprop_blockinfo_within_controlled_range(block_height in 1..=STACKS_BLOCK_HEIGHT_LIMIT, tip in 1..=80u32) {
            for info in BLOCK_INFO_V1.iter().chain(BLOCK_INFO_V2.iter()) {
                crosscheck_compare_only_advancing_tip(&format!("(get-block-info? {info} u{block_height})"), tip)
            }
        }
    }
}

//
// Module with tests that should only be executed
// when running Clarity::V3.
//
#[cfg(feature = "test-clarity-v3")]
mod clarity_v3 {
    use clar2wasm::tools::crosscheck_with_epoch;
    use clarity::types::StacksEpochId;
    use clarity::vm::Value;

    use super::*;

    const STACKS_BLOCK_INFO: [&str; 3] = ["id-header-hash", "header-hash", "time"];
    const TENURE_INFO: [&str; 7] = [
        "burnchain-header-hash",
        "miner-address",
        "time",
        "vrf-seed",
        "block-reward",
        "miner-spend-total",
        "miner-spend-winner",
    ];

    proptest! {
        #![proptest_config(runtime_config())]

        #[test]
        fn crossprop_stacksblockinfo_within_controlled_range(block_height in 1..=STACKS_BLOCK_HEIGHT_LIMIT, tip in 1..=80u32) {
            for info in STACKS_BLOCK_INFO.iter() {
                crosscheck_compare_only_advancing_tip(&format!("(get-stacks-block-info? {info} u{block_height})"), tip)
            }
        }

        #[test]
        fn crossprop_tenureinfo_within_controlled_range(block_height in 1..=STACKS_BLOCK_HEIGHT_LIMIT, tip in 1..=80u32) {
            for info in TENURE_INFO.iter() {
                crosscheck_compare_only_advancing_tip(&format!("(get-tenure-info? {info} u{block_height})"), tip)
            }
        }

        #[test]
        fn crosscheck_at_block_no_leak(
            value in PropValue::any(),
            buf in buffer(32)
        ) {
            let expected = Value::UInt(0);

            crosscheck_with_epoch(
                &format!("(at-block {buf} {value}) (ok stacks-block-height)"),
                Ok(Some(Value::okay(expected).unwrap())),
                StacksEpochId::Epoch30,
            );
        }
    }

    proptest! {
        #![proptest_config(runtime_config())]

        #[cfg(feature = "test-clarity-v3")]
        #[test]
        fn crosscheck_at_block(
            value in PropValue::any(),
            buf in buffer(32)
        ) {
            crosscheck_with_epoch(
                &format!("(at-block {buf} {value})"),
                Ok(Some(value.into())),
               clarity::types::StacksEpochId::Epoch33
            )
        }
    }
}

//
// Module with tests that should only be executed
// when running Clarity::V2 or Clarity::V3.
//
#[cfg(not(feature = "test-clarity-v1"))]
mod clarity_v2_v3 {
    use super::*;

    const BURN_BLOCK_INFO: [&str; 2] = ["header-hash", "pox-addrs"];
    const BURN_BLOCK_HEIGHT_LIMIT: u32 = 100;

    proptest! {
        #![proptest_config(runtime_config())]

        # [test]
        fn crossprop_blockinfo_burnchain_within_controlled_range(block_height in 1..=BURN_BLOCK_HEIGHT_LIMIT, tip in 1..=80u32) {
            for info in &BURN_BLOCK_INFO {
                crosscheck_compare_only_advancing_tip(
                    &format!("(get-burn-block-info? {info} u{block_height})"), tip
                )
            }
        }
    }
}

//
// Module with tests that should only be executed
// when running Clarity::V1 or Clarity::V2.
//
#[cfg(any(feature = "test-clarity-v1", feature = "test-clarity-v2"))]
mod clarity_v1_v2 {
    use clar2wasm::tools::crosscheck_with_epoch;
    use clarity::types::StacksEpochId;
    use clarity::vm::Value;

    use super::*;

    proptest! {
        #![proptest_config(runtime_config())]

        #[test]
        fn crosscheck_at_block_no_leak(
            value in PropValue::any(),
            buf in buffer(32)
        ) {
            let expected = Value::UInt(0);

            crosscheck_with_epoch(
                &format!("(at-block {buf} {value}) (ok block-height)"),
                Ok(Some(Value::okay(expected).unwrap())),
                StacksEpochId::Epoch24,
            );
        }
    }
}
