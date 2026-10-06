#![allow(clippy::expect_used, clippy::unwrap_used)]

//! Benchmarks comparing the Clarity interpreter with the WebAssembly runtime.
//!
//! Contracts are deployed, and compiled to Wasm, before anything is measured: only execution is
//! benchmarked. Every benchmark first checks that both engines agree on the result and the events
//! of the benchmarked transaction, so that a speedup can never come from an engine computing
//! something else. Each benchmark is then measured twice on both engines: as calls to the function
//! within a single transaction, and as whole transactions, as executed by a node. Costs are tracked
//! with the real cost functions, as a node would, and the cost of the transaction is written next
//! to the criterion results in `costs.json`.

use std::hint::black_box;
use std::path::PathBuf;

use clar2wasm::compile;
use clar2wasm::datastore::{BurnDatastore, Datastore, StacksConstants};
use clar2wasm::initialize::initialize_contract;
use clarity::consts::CHAIN_ID_TESTNET;
use clarity::types::{PrivateKey, StacksEpochId};
use clarity::util::hash::Keccak256Hash;
use clarity::util::secp256k1::{Secp256k1PrivateKey, Secp256k1PublicKey};
use clarity::vm::analysis::{run_analysis, ContractAnalysis};
use clarity::vm::ast::build_ast;
use clarity::vm::contexts::{
    ExecutionState, FunctionExecutionOptions, GlobalContext, InvocationContext,
};
use clarity::vm::costs::{ExecutionCost, LimitedCostTracker};
use clarity::vm::database::ClarityDatabase;
use clarity::vm::errors::StaticCheckErrorKind;
use clarity::vm::events::StacksTransactionEvent;
use clarity::vm::resource_limiter::ResourceLimiter;
use clarity::vm::types::{
    PrincipalData, QualifiedContractIdentifier, StandardPrincipalData, TupleData,
};
use clarity::vm::{
    eval_all, CallStack, ClarityName, ClarityVersion, ContractContext, ContractName,
    SymbolicExpression, Value,
};
use criterion::measurement::WallTime;
use criterion::{criterion_group, criterion_main, BenchmarkGroup, BenchmarkId, Criterion};
use paste::paste;
use pprof::criterion::{Output, PProfProfiler};

const EPOCH: StacksEpochId = StacksEpochId::latest();
const VERSION: ClarityVersion = ClarityVersion::latest();

#[derive(Clone, Copy, Debug)]
enum Engine {
    Interpreter,
    Webassembly,
}

impl Engine {
    const ALL: [Engine; 2] = [Engine::Interpreter, Engine::Webassembly];

    fn name(self) -> &'static str {
        match self {
            Engine::Interpreter => "interpreter",
            Engine::Webassembly => "webassembly",
        }
    }
}

/// A contract to deploy, as `(name, source)`.
type Contract = (String, String);

fn contract_id(name: &str) -> QualifiedContractIdentifier {
    QualifiedContractIdentifier::new(
        StandardPrincipalData::transient(),
        ContractName::try_from(name)
            .unwrap_or_else(|_| panic!("Failed to create contract name from {name}")),
    )
}

/// The chain state contracts are deployed to and called on.
struct Chain {
    datastore: Datastore,
    burn_datastore: BurnDatastore,
}

impl Chain {
    fn new() -> Self {
        let mut datastore = Datastore::new();
        let burn_datastore = BurnDatastore::new(StacksConstants::default());

        let mut conn = ClarityDatabase::new(&mut datastore, &burn_datastore, &burn_datastore);
        conn.begin();
        conn.set_clarity_epoch_version(EPOCH).unwrap();
        conn.commit().unwrap();
        if EPOCH.uses_marfed_block_time() {
            conn.begin();
            conn.setup_block_metadata(Some(1)).unwrap();
            conn.commit().unwrap();
        }

        Self {
            datastore,
            burn_datastore,
        }
    }

    /// A cost tracker using the real cost functions, but without a limit, so that it can be kept
    /// for all the iterations of a benchmark.
    fn cost_tracker(&mut self) -> LimitedCostTracker {
        let mut conn = ClarityDatabase::new(
            &mut self.datastore,
            &self.burn_datastore,
            &self.burn_datastore,
        );
        LimitedCostTracker::new(
            false,
            CHAIN_ID_TESTNET,
            ExecutionCost::max_value(),
            &mut conn,
            EPOCH,
        )
        .expect("Failed to create cost tracker")
    }

    fn global_context(&mut self, cost_tracker: LimitedCostTracker) -> GlobalContext<'_> {
        let conn = ClarityDatabase::new(
            &mut self.datastore,
            &self.burn_datastore,
            &self.burn_datastore,
        );
        GlobalContext::new(false, CHAIN_ID_TESTNET, conn, cost_tracker, EPOCH)
    }

    fn deploy(&mut self, engine: Engine, (name, source): &Contract) -> ContractContext {
        let contract_id = contract_id(name);
        let cost_tracker = self.cost_tracker();

        let (mut analysis, wasm_module): (ContractAnalysis, Option<Vec<u8>>) = self
            .datastore
            .as_analysis_db()
            .execute(|analysis_db| {
                let deployed = match engine {
                    Engine::Interpreter => {
                        let mut cost_tracker = cost_tracker;
                        let ast =
                            build_ast(&contract_id, source, &mut cost_tracker, VERSION, EPOCH)
                                .unwrap_or_else(|e| panic!("Failed to parse {name}: {e:?}"));
                        let analysis = run_analysis(
                            &contract_id,
                            &ast.expressions,
                            analysis_db,
                            false,
                            cost_tracker,
                            EPOCH,
                            VERSION,
                            true,
                            ResourceLimiter::unlimited(),
                        )
                        .unwrap_or_else(|e| panic!("Failed to analyze {name}: {e:?}"));
                        (analysis, None)
                    }
                    Engine::Webassembly => {
                        let mut compilation = compile(
                            source,
                            &contract_id,
                            cost_tracker,
                            VERSION,
                            EPOCH,
                            analysis_db,
                            false,
                        )
                        .unwrap_or_else(|e| panic!("Failed to compile {name}: {e:?}"));
                        let wasm_module = compilation.module.emit_wasm();
                        (compilation.contract_analysis, Some(wasm_module))
                    }
                };
                analysis_db
                    .insert_contract(&contract_id, &deployed.0)
                    .expect("Failed to store contract analysis");
                Ok::<_, StaticCheckErrorKind>(deployed)
            })
            .expect("Failed to deploy contract");

        let cost_tracker = analysis
            .cost_track
            .take()
            .expect("Analysis should return its cost tracker");
        let mut contract_context = ContractContext::new(contract_id.clone(), VERSION);
        if let Some(wasm_module) = wasm_module {
            contract_context.set_wasm_module(wasm_module);
        }

        let mut global_context = self.global_context(cost_tracker);
        global_context.begin();
        global_context
            .database
            .insert_contract_hash(&contract_id, source)
            .unwrap();
        match engine {
            Engine::Interpreter => {
                eval_all(
                    &analysis.expressions,
                    &mut contract_context,
                    &mut global_context,
                    None,
                )
                .unwrap_or_else(|e| panic!("Failed to initialize {name}: {e:?}"));
            }
            Engine::Webassembly => {
                initialize_contract(&mut global_context, &mut contract_context, None, &analysis)
                    .unwrap_or_else(|e| panic!("Failed to initialize {name}: {e:?}"));
            }
        }
        global_context
            .database
            .insert_contract(&contract_id, contract_context.clone().into())
            .unwrap();
        global_context
            .database
            .set_contract_data_size(&contract_id, contract_context.data_size)
            .unwrap();
        global_context.commit().unwrap();

        contract_context
    }

    /// Runs `f` inside a transaction calling into `contract`, and commits it.
    fn session<R>(
        &mut self,
        contract: &ContractContext,
        f: impl FnOnce(&mut ExecutionState, &mut InvocationContext) -> R,
    ) -> R {
        let cost_tracker = self.cost_tracker();
        let mut global_context = self.global_context(cost_tracker);
        global_context.begin();

        let mut call_stack = CallStack::new();
        let mut exec_state = ExecutionState {
            global_context: &mut global_context,
            call_stack: &mut call_stack,
        };
        let mut invoke_ctx = InvocationContext {
            contract_context: contract,
            sender: Some(sender()),
            caller: Some(sender()),
            sponsor: None,
        };

        let result = f(&mut exec_state, &mut invoke_ctx);

        global_context.commit().unwrap();
        result
    }

    /// Executes a contract-call transaction the way a node does (see
    /// `OwnedEnvironment::execute_transaction`): the contract is loaded from the chain state, the
    /// arguments are sanitized, the function is called, and the transaction is committed.
    ///
    /// The cost tracker lives for a whole block on a node, so it is moved in and out of the
    /// transaction instead of being created for it.
    fn transaction(
        &mut self,
        cost_tracker: &mut LimitedCostTracker,
        contract_id: &QualifiedContractIdentifier,
        fn_name: &str,
        args: &[SymbolicExpression],
    ) -> (Value, Vec<StacksTransactionEvent>) {
        let mut global_context = self.global_context(std::mem::replace(
            cost_tracker,
            LimitedCostTracker::new_free(),
        ));
        global_context.begin();

        let initial_context = ContractContext::new(
            QualifiedContractIdentifier::transient(),
            ClarityVersion::Clarity1,
        );
        let mut call_stack = CallStack::new();
        let mut exec_state = ExecutionState {
            global_context: &mut global_context,
            call_stack: &mut call_stack,
        };
        let invoke_ctx = InvocationContext {
            contract_context: &initial_context,
            sender: Some(sender()),
            caller: Some(sender()),
            sponsor: None,
        };
        let result = exec_state
            .execute_contract(&invoke_ctx, contract_id, fn_name, args, false)
            .unwrap_or_else(|e| panic!("Transaction calling {fn_name} failed: {e:?}"));

        let (_, events) = global_context.commit().unwrap();
        *cost_tracker = std::mem::replace(
            &mut global_context.cost_track,
            LimitedCostTracker::new_free(),
        );
        (result, events.map(|batch| batch.events).unwrap_or_default())
    }
}

fn sender() -> PrincipalData {
    StandardPrincipalData::transient().into()
}

/// A chain on which the contracts of a benchmark are deployed, ready for the benchmarked call.
struct Prepared {
    chain: Chain,
    contract: ContractContext,
    args: Vec<Value>,
}

/// Deploys `contracts` in order on a new chain, then runs `init` in its own transaction to set up
/// the state and produce the arguments of the call to the last contract, which holds the
/// benchmarked function. Contracts are compiled to Wasm here, so compilation is never measured.
fn prepare<F>(engine: Engine, contracts: &[Contract], init: &F) -> Prepared
where
    F: Fn(&mut ExecutionState, &mut InvocationContext) -> Vec<Value>,
{
    let mut chain = Chain::new();
    let mut deployed: Vec<_> = contracts
        .iter()
        .map(|contract| chain.deploy(engine, contract))
        .collect();
    let contract = deployed
        .pop()
        .expect("A benchmark needs at least one contract");

    // A contract stored without a Wasm module is silently interpreted, which the crosscheck cannot
    // detect since both engines would then be the interpreter.
    let mut conn = ClarityDatabase::new(
        &mut chain.datastore,
        &chain.burn_datastore,
        &chain.burn_datastore,
    );
    conn.begin();
    for (name, _) in contracts {
        let stored = conn
            .get_contract(&contract_id(name))
            .expect("Failed to load deployed contract");
        assert_eq!(
            stored.wasm_module.is_some(),
            matches!(engine, Engine::Webassembly),
            "{name} is not stored as expected for the {}",
            engine.name()
        );
    }
    conn.roll_back().unwrap();

    let args = chain.session(&contract, |exec_state, invoke_ctx| {
        init(exec_state, invoke_ctx)
    });
    Prepared {
        chain,
        contract,
        args,
    }
}

fn as_transaction_args(args: &[Value]) -> Vec<SymbolicExpression> {
    args.iter()
        .cloned()
        .map(SymbolicExpression::atom_value)
        .collect()
}

/// Executes the benchmarked transaction once on each engine, starting from the same state, and
/// panics if the engines disagree on the result or the emitted events. Returns the cost of the
/// transaction on each engine.
fn crosscheck<F>(contracts: &[Contract], fn_name: &str, init: &F) -> [ExecutionCost; 2]
where
    F: Fn(&mut ExecutionState, &mut InvocationContext) -> Vec<Value>,
{
    let [(interpreted, interpreter_events, interpreter_cost), (wasm, wasm_events, wasm_cost)] =
        Engine::ALL.map(|engine| {
            let Prepared {
                mut chain,
                contract,
                args,
            } = prepare(engine, contracts, init);
            let mut cost_tracker = chain.cost_tracker();
            let (result, events) = chain.transaction(
                &mut cost_tracker,
                &contract.contract_identifier,
                fn_name,
                &as_transaction_args(&args),
            );
            (result, events, cost_tracker.get_total())
        });

    assert_eq!(
        interpreted, wasm,
        "{fn_name}: the engines returned different values"
    );
    assert_eq!(
        interpreter_events, wasm_events,
        "{fn_name}: the engines emitted different events"
    );

    [interpreter_cost, wasm_cost]
}

/// Writes the costs of a benchmarked transaction next to its criterion results.
fn record_costs(group: &str, param: Option<&str>, costs: &[ExecutionCost; 2]) {
    let mut dir = std::env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../target"))
        .join("criterion")
        .join(group);
    if let Some(param) = param {
        dir.push(param);
    }

    let json = Engine::ALL
        .iter()
        .zip(costs)
        .map(|(engine, cost)| {
            format!(
                r#""{}":{{"runtime":{},"read_count":{},"read_length":{},"write_count":{},"write_length":{}}}"#,
                engine.name(),
                cost.runtime,
                cost.read_count,
                cost.read_length,
                cost.write_count,
                cost.write_length
            )
        })
        .collect::<Vec<_>>()
        .join(",");

    std::fs::create_dir_all(&dir).expect("Failed to create the costs directory");
    std::fs::write(dir.join("costs.json"), format!("{{{json}}}\n"))
        .expect("Failed to write the costs");
}

fn benchmark_id(engine: Engine, param: Option<&str>) -> BenchmarkId {
    match param {
        Some(param) => BenchmarkId::new(engine.name(), param),
        None => BenchmarkId::from_parameter(engine.name()),
    }
}

/// Benchmarks calling `fn_name` of the last of `contracts` on both engines. All calls happen in a
/// single transaction, so this measures the function call alone.
fn bench_calls<F>(
    group: &mut BenchmarkGroup<WallTime>,
    param: Option<&str>,
    contracts: &[Contract],
    fn_name: &str,
    init: F,
) where
    F: Fn(&mut ExecutionState, &mut InvocationContext) -> Vec<Value>,
{
    for engine in Engine::ALL {
        group.bench_function(benchmark_id(engine, param), |b| {
            let Prepared {
                mut chain,
                contract,
                args,
            } = prepare(engine, contracts, &init);
            let func = contract
                .lookup_function(fn_name)
                .expect("failed to lookup function");
            chain.session(&contract, |exec_state, invoke_ctx| {
                b.iter(|| {
                    exec_state
                        .execute_function_as_transaction(
                            invoke_ctx,
                            &func,
                            &args,
                            FunctionExecutionOptions::default(),
                        )
                        .expect("Function call failed")
                });
            });
        });
    }
}

/// Benchmarks a transaction calling `fn_name` of the last of `contracts` on both engines, after
/// checking that they agree on the outcome. Each iteration is a whole transaction, as executed by
/// a node: setting up the execution context, loading the contract, calling it and committing.
fn bench_transactions<F>(
    group: &mut BenchmarkGroup<WallTime>,
    group_name: &str,
    param: Option<&str>,
    contracts: &[Contract],
    fn_name: &str,
    init: F,
) where
    F: Fn(&mut ExecutionState, &mut InvocationContext) -> Vec<Value>,
{
    record_costs(group_name, param, &crosscheck(contracts, fn_name, &init));

    for engine in Engine::ALL {
        group.bench_function(benchmark_id(engine, param), |b| {
            let Prepared {
                mut chain,
                contract,
                args,
            } = prepare(engine, contracts, &init);
            let args = as_transaction_args(&args);
            let mut cost_tracker = chain.cost_tracker();
            b.iter(|| {
                chain.transaction(
                    &mut cost_tracker,
                    &contract.contract_identifier,
                    fn_name,
                    &args,
                )
            });
        });
    }
}

fn criterion_config() -> Criterion {
    if cfg!(feature = "flamegraph") {
        Criterion::default().with_profiler(PProfProfiler::new(100, Output::Flamegraph(None)))
    } else if cfg!(feature = "pb") {
        Criterion::default().with_profiler(PProfProfiler::new(100, Output::Protobuf))
    } else {
        Criterion::default()
    }
}

/// Used to declare benchmarks of clarity contracts to be run on both the interpreter and the
/// WebAssembly runtime.
/// Each arm should only be matched once and declares a criterion group that can then be picked up
/// by [`criterion_main!`].
/// Every benchmark `name` declares two groups: `name`, measuring calls to the function `name`, and
/// `name-tx`, measuring whole transactions calling it.
macro_rules! decl_benches {
    // single
    ($(($fn_name:literal, $clarity:literal, [$($arg:expr),*])),* $(,)?) => {
        paste! {
            $(
                #[allow(non_snake_case)]
                fn [<single _ $fn_name>](c: &mut Criterion) {
                    let contracts = [(format!("clarity-{}", $fn_name), $clarity.to_string())];

                    let mut group = c.benchmark_group($fn_name);
                    bench_calls(&mut group, None, &contracts, $fn_name, |_, _| {
                        vec![$(black_box($arg)),*]
                    });
                    group.finish();

                    let group_name = concat!($fn_name, "-tx");
                    let mut group = c.benchmark_group(group_name);
                    bench_transactions(&mut group, group_name, None, &contracts, $fn_name, |_, _| {
                        vec![$(black_box($arg)),*]
                    });
                    group.finish();
                }
            )*

            criterion_group! {
                name = single;
                config = criterion_config();
                targets = $([<single _ $fn_name>]),*
            }
        }
    };
    // range
    ($(($fn_name:literal, $range:expr, $produce_clarity:expr, $init:expr)),* $(,)?) => {
        paste! {
            $(
                #[allow(non_snake_case)]
                fn [<range _ $fn_name>](c: &mut Criterion) {
                    let produce_clarity = $produce_clarity;
                    let all_contracts: Vec<_> = ($range)
                        .map(|i| (i, [(format!("clarity-{}", $fn_name), produce_clarity(i))]))
                        .collect();

                    let mut group = c.benchmark_group($fn_name);
                    for (i, contracts) in &all_contracts {
                        let i = *i;
                        bench_calls(&mut group, Some(&i.to_string()), contracts, $fn_name, |exec_state, invoke_ctx| {
                            $init(i, exec_state, invoke_ctx)
                        });
                    }
                    group.finish();

                    let group_name = concat!($fn_name, "-tx");
                    let mut group = c.benchmark_group(group_name);
                    for (i, contracts) in &all_contracts {
                        let i = *i;
                        bench_transactions(&mut group, group_name, Some(&i.to_string()), contracts, $fn_name, |exec_state, invoke_ctx| {
                            $init(i, exec_state, invoke_ctx)
                        });
                    }
                    group.finish();
                }
            )*

            criterion_group! {
                name = range;
                config = criterion_config();
                targets = $([<range _ $fn_name>]),*
            }
        }
    }
}

decl_benches! {
    (
        "add",
        r#"
         (define-read-only (add (x int) (y int))
             (+ x y)
         )
        "#,
        [Value::Int(42), Value::Int(12345)]
    ),
}

decl_benches! {
    (
        "fold_add_square",
        (1..=1001).step_by(50),
        |i| format!(r#"
        (define-private (add_square (x int) (y int))
            (+ (* x x) y)
        )

        (define-public (fold_add_square (l (list {i} int)) (init int))
            (ok (fold add_square l init))
        )
        "#),
        |i, _, _| vec![Value::cons_list_unsanitized((1..=i).map(Value::Int).collect()).unwrap(), Value::Int(0)]
    ),
    (
        "map_set_entries",
        (1..=1001).step_by(50),
        |i| format!(r#"
        (define-map mymap int int)

        (define-public (map_set_entries (l (list {i} int)))
            (begin
                (map set_entry l)
                (ok true)
            )
        )

        (define-private (set_entry (entry int))
            (map-set mymap entry entry)
        )
        "#),
        |i, _: &mut ExecutionState, _: &mut InvocationContext| vec![Value::cons_list_unsanitized((1..=i).map(Value::Int).collect()).unwrap()]
    ),
    (
        "add_prices",
        (1..51).step_by(2),
        |_i| r"
        (define-map oracle_data
            { source: uint, symbol: uint }
            { amount: uint }
        )

        (define-map oracle_sources
            { source: uint }
            { key: (buff 33) }
        )

        (define-read-only (slice-16 (b (buff 48)) (start uint))
            (unwrap-panic (as-max-len? (unwrap-panic (slice? b start (+ start u16))) u16))
        )

        (define-read-only (extract-source (msg (buff 48)))
            (buff-to-uint-le (slice-16 msg u0))
        )

        (define-read-only (extract-symbol (msg (buff 48)))
            (buff-to-uint-le (slice-16 msg u16))
        )

        (define-read-only (extract-amount (msg (buff 48)))
            (buff-to-uint-le (slice-16 msg u32))
        )

        (define-read-only (verify-signature (msg (buff 48)) (sig (buff 65)) (key (buff 33)))
            (is-eq (unwrap-panic (secp256k1-recover? (keccak256 msg) sig)) key)
        )

        (define-private (add-price (msg (buff 48)) (sig (buff 65)))
            (let ((source (extract-source msg)))
                (if (verify-signature msg sig (get key (unwrap-panic (map-get? oracle_sources {source: source}))))
                    (let ((symbol (extract-symbol msg)) (amount (extract-amount msg)) (data-opt (map-get? oracle_data {source: source, symbol: symbol})))
                        (if (is-some data-opt)
                            (let ((data (unwrap-panic data-opt)))
                                (begin
                                    (map-set oracle_data {source: source, symbol: symbol} {amount: amount})
                                    (ok true)
                                )
                            )
                            (begin
                                (map-set oracle_data {source: source, symbol: symbol} {amount: amount})
                                (ok true)
                            )
                        )
                    )
                    (err u62)
                )
            )
        )

        (define-private (call-add-price (price {msg: (buff 48), sig: (buff 65)}))
            (unwrap-panic (add-price (get msg price) (get sig price)))
        )

        (define-public (add_source (source uint) (key (buff 33)))
            (begin
                (map-set oracle_sources { source: source } { key: key })
                (ok true)
            )
        )

        (define-public (add_prices (prices (list 1001 {msg: (buff 48), sig: (buff 65)})))
            (begin
                (map call-add-price prices)
                (ok true)
            )
        )
        ".to_string(),
        |i, execution_state: &mut ExecutionState, invoke_ctx: &mut InvocationContext| vec![add_prices_init(i, execution_state, invoke_ctx)]
    ),
    (
        "poc2",
        (1..123).step_by(3),
        |i| format!(r#"
            (define-public (poc2 (v int))
                (begin
                    (let ((a {{a: {{a: {{b: 1,c: 1,d: 1,e: 1,f: 1,g: 1,h: 1,i: 1,j: 1,k: 1,l: 1,m: 1,n: 1,o: 1,p: 1,q: 1,r: 1,s: 1,t: 1,u-: 1,v: 1,w: 1,x: 1,y: 1,z: 1,A: 1,B: 1,C: 1,D: 1,E: 1,F: 1,G: 1,H: 1,I: 1,J: 1,K: 1,L: 1,M: 1,N: 1,O: 1,P: 1,Q: 1,R: 1,S: 1,T: 1,U: 1,V: 1,W: 1,X: 1,Y: 1,Z: 1,ba: 1,bb: 1,bc: 1,bd: 1,be: 1,bf: 1,bg: 1,bh: 1,bi: 1,bj: 1,bk: 1,bl: 1,bm: 1,bn: 1,bo: 1,bp: 1,bq: 1,br: 1,bs: 1,bt: 1,bu: 1,bv: 1,bw: 1,bx: 1,by: 1,bz: 1,bA: 1,bB: 1,bC: 1,bD: 1,bE: 1,bF: 1,bG: 1,bH: 1,bI: 1,bJ: 1,bK: 1,bL: 1,bM: 1,bN: 1,bO: 1,bP: 1,bQ: 1,bR: 1,bS: 1,bT: 1,bU: 1,bV: 1,bW: 1,bX: 1,bY: 1,bZ: 1,ca: 1,cb: 1,cc: 1,cd: 1,ce: 1,cf: 1,cg: 1,ch: 1,ci: 1,cj: 1,ck: 1,cl: 1,cm: 1,cn: 1,co: 1,cp: 1,cq: 1,cr: 1,cs: 1,ct: 1,cu: 1,cv: 1,cw: 1,cx: 1,cy: 1,cz: 1,cA: 1,cB: 1,cC: 1,cD: 1,cE: 1,cF: 1,cG: 1,cH: 1,cI: 1,cJ: 1,cK: 1,cL: 1,cM: 1,cN: 1,cO: 1,cP: 1,cQ: 1,cR: 1,cS: 1,cT: 1,cU: 1,cV: 1,cW: 1,cX: 1,cY: 1,cZ: 1,da: 1,db: 1,dc: 1,dd: 1,de: 1,df: 1,dg: 1,dh: 1,di: 1,dj: 1,dk: 1,dl: 1,dm: 1,dn: 1,do: 1,dp: 1,dq: 1,dr: 1,ds: 1,dt: 1,du: 1,dv: 1,dw: 1,dx: 1,dy: 1,dz: 1,dA: 1,dB: 1,dC: 1,dD: 1,dE: 1,dF: 1,dG: 1,dH: 1,dI: 1,dJ: 1,dK: 1,dL: 1,dM: 1,dN: 1,dO: 1,dP: 1,dQ: 1,dR: 1,dS: 1,dT: 1,dU: 1,dV: 1,dW: 1,dX: 1,dY: 1,dZ: 1,ea: 1,eb: 1,ec: 1,ed: 1,ee: 1,ef: 1,eg: 1,eh: 1,ei: 1,ej: 1,ek: 1,el: 1,em: 1,en: 1,eo: 1,ep: 1,eq: 1,er: 1,es: 1,et: 1,eu: 1,ev: 1,ew: 1,ex: 1,ey: 1,ez: 1,eA: 1,eB: 1,eC: 1,eD: 1,eE: 1,eF: 1,eG: 1,eH: 1,eI: 1,eJ: 1,eK: 1,eL: 1,eM: 1,eN: 1,eO: 1}}}}}}) (b (list{} ))) b)
                    (ok (+ 1 1))
                )
            )"#,
            " a".repeat(i)
        ),
        |_, _, _| vec![Value::Int(42)]
    ),
}

fn add_prices_init(
    n: usize,
    execution_state: &mut ExecutionState,
    invocation_context: &mut InvocationContext,
) -> Value {
    let mut prices = Vec::with_capacity(n);

    let sk = Secp256k1PrivateKey::from_hex(
        "9bf49a6a0755f953811fce125f2683d50429c3bb49e074147e0089a52eae155f01",
    )
    .unwrap();
    let pk = Secp256k1PublicKey::from_private(&sk);

    let source = 1u128;
    let symbol = 2u128;
    let amount = 3u128;

    let mut msg = [0; 48];
    msg[0..16].copy_from_slice(&source.to_le_bytes());
    msg[16..32].copy_from_slice(&symbol.to_le_bytes());
    msg[32..48].copy_from_slice(&amount.to_le_bytes());
    let msg_hash = Keccak256Hash::from_data(&msg);

    // NOTE: the way we have to construct the signature here would be better handled closer to
    //       the upstream types themselves.
    let sig = sk.sign(msg_hash.as_bytes()).unwrap();
    let sig = sig.to_secp256k1_recoverable().unwrap();
    let (recovery_id, compact) = sig.serialize_compact();

    let mut sig_bytes = [0u8; 65];
    sig_bytes[..64].copy_from_slice(&compact);
    sig_bytes[64] = recovery_id.to_i32() as u8;

    for _ in 0..n {
        prices.push(Value::Tuple(
            TupleData::from_data(vec![
                (
                    ClarityName::from_literal("msg"),
                    Value::buff_from(msg.to_vec()).unwrap(),
                ),
                (
                    ClarityName::from_literal("sig"),
                    Value::buff_from(sig_bytes.to_vec()).unwrap(),
                ),
            ])
            .unwrap(),
        ));
    }

    let func = invocation_context
        .contract_context
        .lookup_function("add_source")
        .expect("failed to lookup function");

    execution_state
        .execute_function_as_transaction(
            invocation_context,
            &func,
            &[
                Value::UInt(source),
                Value::buff_from(pk.to_bytes_compressed()).unwrap(),
            ],
            FunctionExecutionOptions::default(),
        )
        .expect("Adding source should succeed");

    Value::cons_list_unsanitized(prices).unwrap()
}

criterion_main!(single, range);
