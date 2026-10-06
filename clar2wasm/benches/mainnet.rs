#![allow(clippy::expect_used, clippy::unwrap_used)]

//! Benchmarks comparing the Clarity interpreter with the WebAssembly runtime on mainnet contracts.
//!
//! The contracts in `contracts/mainnet` are copies of mainnet contracts, see the README there. Each
//! benchmark calls one of their most used functions, as whole transactions as executed by a node,
//! and, when the call can be repeated on the state it leaves behind, as calls within a single
//! transaction. See [`common`] for how benchmarks are run.

mod common;

use clarity::util::hash::Hash160;
use clarity::vm::contexts::{ExecutionState, InvocationContext};
use clarity::vm::types::PrincipalData;
use clarity::vm::{ClarityVersion, Value};
use common::{bench_calls, bench_transactions, criterion_config, sender, Contract, Scenario, Step};
use criterion::{criterion_group, criterion_main, Criterion};

const SBTC_TOKEN: &str = include_str!("contracts/mainnet/sbtc-token.clar");
const SBTC_REGISTRY: &str = include_str!("contracts/mainnet/sbtc-registry.clar");
const BNS_V2: &str = include_str!("contracts/mainnet/BNS-V2.clar");
const BNS_COMMISSION_TRAIT: &str = include_str!("contracts/mainnet/commission-trait.clar");
const NFT_TRAIT: &str = include_str!("contracts/mainnet/nft-trait.clar");

/// Stands in for `sbtc-deposit`, which the registry authorizes to mint, to fund accounts.
const SBTC_DEPOSIT_STUB: &str = r#"
(define-public (mint (amount uint) (recipient principal))
    (contract-call? .sbtc-token protocol-mint amount recipient 0x01))
"#;

/// The recipient of transfers.
const RECIPIENT: &str = "ST1PQHQKV0RJXZFY1DGX8MNSNYVE3VGZJSRTPGZGM";

/// Sets up the state of a benchmark and returns the arguments of the benchmarked call.
type Init = Box<dyn Fn(&mut ExecutionState, &mut InvocationContext) -> Vec<Value>>;

fn args(args: Vec<Value>) -> Init {
    Box::new(move |_, _| args.clone())
}

fn principal(address: &str) -> Value {
    Value::Principal(PrincipalData::parse(address).unwrap())
}

fn buff(bytes: &[u8]) -> Value {
    Value::buff_from(bytes.to_vec()).unwrap()
}

fn sbtc_scenario() -> Scenario {
    let v3 = ClarityVersion::Clarity3;
    Scenario::new(
        vec![
            Contract::with_version("sbtc-registry", SBTC_REGISTRY, v3),
            Contract::with_version("sbtc-token", SBTC_TOKEN, v3),
            Contract::with_version("sbtc-deposit", SBTC_DEPOSIT_STUB, v3),
        ],
        "sbtc-token",
        "transfer",
    )
    .with_setup(vec![Step::call(
        "sbtc-deposit",
        "mint",
        vec![
            Value::UInt(1_000_000_000_000_000),
            Value::Principal(sender()),
        ],
    )])
}

/// A transfer of 100 sats from the sender, with `memo`.
fn sbtc_transfer(memo: Option<&[u8]>) -> Init {
    let memo = match memo {
        Some(memo) => Value::some(buff(memo)).unwrap(),
        None => Value::none(),
    };
    args(vec![
        Value::UInt(100),
        Value::Principal(sender()),
        principal(RECIPIENT),
        memo,
    ])
}

const BNS_NAMESPACE: &[u8] = b"benchmark";
const BNS_NAMESPACE_SALT: &[u8] = b"salt";
/// The name claimed during the setup, with the id 1.
const BNS_NAME: &[u8] = b"satoshi";

/// Deploys BNS-V2 and launches a namespace, owned by the sender, in which names cost 10 µSTX and
/// last 5000 blocks, then claims a name for the sender.
fn bns_scenario(function: &str) -> Scenario {
    let hashed_salted_namespace =
        Hash160::from_data(&[BNS_NAMESPACE, b".", BNS_NAMESPACE_SALT].concat());

    let mut reveal_args = vec![buff(BNS_NAMESPACE), buff(BNS_NAMESPACE_SALT)];
    // Price function: base, coefficient, 16 buckets, non-alpha and no-vowel discounts.
    reveal_args.extend(std::iter::repeat_n(Value::UInt(1), 20));
    reveal_args.extend([
        Value::UInt(5000),          // lifetime
        Value::Principal(sender()), // namespace-import
        Value::none(),              // namespace-manager
        Value::Bool(false),         // can-update-price
        Value::Bool(false),         // manager-transfers
        Value::Bool(true),          // manager-frozen
    ]);

    Scenario::new(
        vec![
            Contract::with_version("nft-trait", NFT_TRAIT, ClarityVersion::Clarity1)
                .at("SP2PABAF9FTAJYNFZH93XENAJ8FVY99RRM50D2JG9"),
            Contract::with_version(
                "commission-trait",
                BNS_COMMISSION_TRAIT,
                ClarityVersion::Clarity2,
            ),
            Contract::with_version("BNS-V2", BNS_V2, ClarityVersion::Clarity2),
        ],
        "BNS-V2",
        function,
    )
    .with_setup(vec![
        Step::call("BNS-V2", "flip-migration-complete", vec![]),
        Step::call(
            "BNS-V2",
            "namespace-preorder",
            vec![
                buff(hashed_salted_namespace.as_bytes()),
                Value::UInt(640_000_000_000),
            ],
        ),
        Step::AdvanceBlocks(1),
        Step::call("BNS-V2", "namespace-reveal", reveal_args),
        Step::call("BNS-V2", "namespace-launch", vec![buff(BNS_NAMESPACE)]),
        Step::call(
            "BNS-V2",
            "name-claim-fast",
            vec![
                buff(BNS_NAME),
                buff(BNS_NAMESPACE),
                Value::Principal(sender()),
            ],
        ),
        // A claimed name can only be transferred once its registration block has passed.
        Step::AdvanceBlocks(2),
    ])
    .with_fresh_state()
}

fn mainnet(c: &mut Criterion) {
    let sbtc = sbtc_scenario();
    let bns_transfer = bns_scenario("transfer");
    let bns_claim = bns_scenario("name-claim-fast");

    let benchmarks: [(&str, &Scenario, Init); 4] = [
        ("sbtc-transfer", &sbtc, sbtc_transfer(None)),
        (
            "sbtc-transfer-memo",
            &sbtc,
            sbtc_transfer(Some(&[0x42; 34])),
        ),
        (
            "bns-transfer",
            &bns_transfer,
            args(vec![
                Value::UInt(1),
                Value::Principal(sender()),
                principal(RECIPIENT),
            ]),
        ),
        (
            "bns-name-claim-fast",
            &bns_claim,
            args(vec![
                buff(b"nakamoto"),
                buff(BNS_NAMESPACE),
                Value::Principal(sender()),
            ]),
        ),
    ];

    for (name, scenario, init) in &benchmarks {
        if !scenario.fresh_state {
            let mut group = c.benchmark_group(*name);
            bench_calls(&mut group, None, scenario, init);
            group.finish();
        }

        let group_name = format!("{name}-tx");
        let mut group = c.benchmark_group(&group_name);
        bench_transactions(&mut group, &group_name, None, scenario, init);
        group.finish();
    }
}

criterion_group! {
    name = benches;
    config = criterion_config();
    targets = mainnet
}
criterion_main!(benches);
