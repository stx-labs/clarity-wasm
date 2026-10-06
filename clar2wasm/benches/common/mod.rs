//! The harness shared by the benchmarks comparing the Clarity interpreter with the WebAssembly
//! runtime.
//!
//! Contracts are deployed, and compiled to Wasm, before anything is measured: only execution is
//! benchmarked. Before measuring, a benchmark checks that both engines agree on the result and the
//! events of the benchmarked transaction, so that a speedup can never come from an engine computing
//! something else. Calls can be measured on their own, within a single transaction, or as whole
//! transactions, as executed by a node. Costs are tracked with the real cost functions, as a node
//! would, and the cost of the transaction is written next to the criterion results in
//! `costs.json`.

// Each benchmark only uses part of the harness.
#![allow(dead_code)]

use std::path::PathBuf;

use clar2wasm::compile;
use clar2wasm::datastore::{BurnDatastore, Datastore, StacksConstants};
use clar2wasm::initialize::initialize_contract;
use clarity::consts::CHAIN_ID_TESTNET;
use clarity::types::StacksEpochId;
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
use clarity::vm::types::{PrincipalData, QualifiedContractIdentifier, StandardPrincipalData};
use clarity::vm::{
    eval_all, CallStack, ClarityVersion, ContractContext, ContractName, SymbolicExpression, Value,
};
use criterion::measurement::WallTime;
use criterion::{BenchmarkGroup, BenchmarkId, Criterion};
use pprof::criterion::{Output, PProfProfiler};

pub const EPOCH: StacksEpochId = StacksEpochId::latest();
pub const VERSION: ClarityVersion = ClarityVersion::latest();

#[derive(Clone, Copy, Debug)]
pub enum Engine {
    Interpreter,
    Webassembly,
}

impl Engine {
    pub const ALL: [Engine; 2] = [Engine::Interpreter, Engine::Webassembly];

    pub fn name(self) -> &'static str {
        match self {
            Engine::Interpreter => "interpreter",
            Engine::Webassembly => "webassembly",
        }
    }
}

/// A contract to deploy, as `(name, source)`.
pub type Contract = (String, String);

pub fn contract_id(name: &str) -> QualifiedContractIdentifier {
    QualifiedContractIdentifier::new(
        StandardPrincipalData::transient(),
        ContractName::try_from(name)
            .unwrap_or_else(|_| panic!("Failed to create contract name from {name}")),
    )
}

/// The chain state contracts are deployed to and called on.
pub struct Chain {
    datastore: Datastore,
    burn_datastore: BurnDatastore,
}

impl Chain {
    pub fn new() -> Self {
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
    pub fn cost_tracker(&mut self) -> LimitedCostTracker {
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

    pub fn global_context(&mut self, cost_tracker: LimitedCostTracker) -> GlobalContext<'_> {
        let conn = ClarityDatabase::new(
            &mut self.datastore,
            &self.burn_datastore,
            &self.burn_datastore,
        );
        GlobalContext::new(false, CHAIN_ID_TESTNET, conn, cost_tracker, EPOCH)
    }

    pub fn deploy(&mut self, engine: Engine, (name, source): &Contract) -> ContractContext {
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
    pub fn session<R>(
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
    pub fn transaction(
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

pub fn sender() -> PrincipalData {
    StandardPrincipalData::transient().into()
}

/// A chain on which the contracts of a benchmark are deployed, ready for the benchmarked call.
pub struct Prepared {
    pub chain: Chain,
    pub contract: ContractContext,
    pub args: Vec<Value>,
}

/// Deploys `contracts` in order on a new chain, then runs `init` in its own transaction to set up
/// the state and produce the arguments of the call to the last contract, which holds the
/// benchmarked function. Contracts are compiled to Wasm here, so compilation is never measured.
pub fn prepare<F>(engine: Engine, contracts: &[Contract], init: &F) -> Prepared
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

pub fn as_transaction_args(args: &[Value]) -> Vec<SymbolicExpression> {
    args.iter()
        .cloned()
        .map(SymbolicExpression::atom_value)
        .collect()
}

/// Executes the benchmarked transaction once on each engine, starting from the same state, and
/// panics if the engines disagree on the result or the emitted events. Returns the cost of the
/// transaction on each engine.
pub fn crosscheck<F>(contracts: &[Contract], fn_name: &str, init: &F) -> [ExecutionCost; 2]
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
pub fn record_costs(group: &str, param: Option<&str>, costs: &[ExecutionCost; 2]) {
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

/// Checks that both engines agree on the benchmarked transaction (see [`crosscheck`]), and records
/// its costs next to the criterion results of `group_name`.
pub fn check<F>(
    group_name: &str,
    param: Option<&str>,
    contracts: &[Contract],
    fn_name: &str,
    init: &F,
) where
    F: Fn(&mut ExecutionState, &mut InvocationContext) -> Vec<Value>,
{
    record_costs(group_name, param, &crosscheck(contracts, fn_name, init));
}

pub fn benchmark_id(engine: Engine, param: Option<&str>) -> BenchmarkId {
    match param {
        Some(param) => BenchmarkId::new(engine.name(), param),
        None => BenchmarkId::from_parameter(engine.name()),
    }
}

/// Benchmarks calling `fn_name` of the last of `contracts` on both engines. All calls happen in a
/// single transaction, so this measures the function call alone.
pub fn bench_calls<F>(
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
pub fn bench_transactions<F>(
    group: &mut BenchmarkGroup<WallTime>,
    group_name: &str,
    param: Option<&str>,
    contracts: &[Contract],
    fn_name: &str,
    init: F,
) where
    F: Fn(&mut ExecutionState, &mut InvocationContext) -> Vec<Value>,
{
    check(group_name, param, contracts, fn_name, &init);

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

pub fn criterion_config() -> Criterion {
    if cfg!(feature = "flamegraph") {
        Criterion::default().with_profiler(PProfProfiler::new(100, Output::Flamegraph(None)))
    } else if cfg!(feature = "pb") {
        Criterion::default().with_profiler(PProfProfiler::new(100, Output::Protobuf))
    } else {
        Criterion::default()
    }
}
