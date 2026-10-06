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
use clar2wasm::tools::execute;
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
use criterion::{BatchSize, BenchmarkGroup, BenchmarkId, Criterion};
use pprof::criterion::{Output, PProfProfiler};

pub const EPOCH: StacksEpochId = StacksEpochId::latest();

/// The STX balance of the sender of the benchmarked transactions.
pub const SENDER_BALANCE: u128 = 100_000_000_000_000;

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

/// A contract to deploy.
pub struct Contract {
    pub name: String,
    pub source: String,
    pub version: ClarityVersion,
    /// The address deploying the contract, the transient test address by default.
    pub issuer: StandardPrincipalData,
}

impl Contract {
    /// A contract using the latest Clarity version.
    pub fn new(name: impl Into<String>, source: impl Into<String>) -> Self {
        Self::with_version(name, source, ClarityVersion::latest())
    }

    pub fn with_version(
        name: impl Into<String>,
        source: impl Into<String>,
        version: ClarityVersion,
    ) -> Self {
        Self {
            name: name.into(),
            source: source.into(),
            version,
            issuer: StandardPrincipalData::transient(),
        }
    }

    /// Deploys the contract from `address` instead of the transient test address, for contracts
    /// referred to by their fully qualified name.
    pub fn at(mut self, address: &str) -> Self {
        self.issuer = match PrincipalData::parse_standard_principal(address) {
            Ok(issuer) => issuer,
            Err(e) => panic!("Invalid address {address}: {e:?}"),
        };
        self
    }

    pub fn id(&self) -> QualifiedContractIdentifier {
        QualifiedContractIdentifier::new(
            self.issuer.clone(),
            ContractName::try_from(self.name.as_str())
                .unwrap_or_else(|_| panic!("Failed to create contract name from {}", self.name)),
        )
    }
}

/// A step setting up the chain state of a benchmark.
pub enum Step {
    /// A transaction from the sender, which must return `(ok ...)`.
    Call {
        contract: String,
        function: String,
        args: Vec<Value>,
    },
    /// Mines empty blocks.
    AdvanceBlocks(u32),
}

impl Step {
    pub fn call(contract: &str, function: &str, args: Vec<Value>) -> Self {
        Step::Call {
            contract: contract.to_string(),
            function: function.to_string(),
            args,
        }
    }
}

/// What a benchmark deploys and calls.
pub struct Scenario {
    /// The contracts to deploy, in order.
    pub contracts: Vec<Contract>,
    /// The name of the contract holding the benchmarked function.
    pub target: String,
    /// The benchmarked function.
    pub function: String,
    /// Steps run after deploying the contracts, before `init`.
    pub setup: Vec<Step>,
    /// Whether every benchmarked transaction must start from the prepared state, for transactions
    /// which cannot be repeated on the state they leave behind (transferring an NFT, registering a
    /// name). The prepared state is then copied before each transaction, outside of the
    /// measurement. Such scenarios can only be benchmarked as whole transactions.
    pub fresh_state: bool,
}

impl Scenario {
    pub fn new(
        contracts: Vec<Contract>,
        target: impl Into<String>,
        function: impl Into<String>,
    ) -> Self {
        let target = target.into();
        assert!(
            contracts.iter().any(|contract| contract.name == target),
            "{target} is not deployed by the scenario"
        );
        Self {
            contracts,
            target,
            function: function.into(),
            setup: vec![],
            fresh_state: false,
        }
    }

    pub fn with_setup(mut self, setup: Vec<Step>) -> Self {
        self.setup = setup;
        self
    }

    pub fn with_fresh_state(mut self) -> Self {
        self.fresh_state = true;
        self
    }

    /// The identifier of the deployed contract `name`.
    pub fn contract_id(&self, name: &str) -> QualifiedContractIdentifier {
        self.contracts
            .iter()
            .find(|contract| contract.name == name)
            .unwrap_or_else(|| panic!("{name} is not deployed by the scenario"))
            .id()
    }

    /// A scenario calling `function` of a single contract.
    pub fn single(contract: Contract, function: impl Into<String>) -> Self {
        let target = contract.name.clone();
        Self::new(vec![contract], target, function)
    }
}

pub fn contract_id(name: &str) -> QualifiedContractIdentifier {
    QualifiedContractIdentifier::new(
        StandardPrincipalData::transient(),
        ContractName::try_from(name)
            .unwrap_or_else(|_| panic!("Failed to create contract name from {name}")),
    )
}

/// The chain state contracts are deployed to and called on.
#[derive(Clone)]
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

        execute(&mut conn, |db| {
            let mut snapshot = db.get_stx_balance_snapshot(&sender())?;
            snapshot.credit(SENDER_BALANCE)?;
            snapshot.save()?;
            db.increment_ustx_liquid_supply(SENDER_BALANCE)
        })
        .expect("Failed to fund the sender");

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

    pub fn deploy(&mut self, engine: Engine, contract: &Contract) -> ContractContext {
        let Contract {
            name,
            source,
            version,
            ..
        } = contract;
        let version = *version;
        let contract_id = contract.id();
        let cost_tracker = self.cost_tracker();

        let (mut analysis, wasm_module): (ContractAnalysis, Option<Vec<u8>>) = self
            .datastore
            .as_analysis_db()
            .execute(|analysis_db| {
                let deployed = match engine {
                    Engine::Interpreter => {
                        let mut cost_tracker = cost_tracker;
                        let ast =
                            build_ast(&contract_id, source, &mut cost_tracker, version, EPOCH)
                                .unwrap_or_else(|e| panic!("Failed to parse {name}: {e:?}"));
                        let analysis = run_analysis(
                            &contract_id,
                            &ast.expressions,
                            analysis_db,
                            false,
                            cost_tracker,
                            EPOCH,
                            version,
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
                            version,
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
        let mut contract_context = ContractContext::new(contract_id.clone(), version);
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

impl Chain {
    pub fn advance_blocks(&mut self, count: u32) {
        self.burn_datastore.advance_chain_tip(count);
        self.datastore.advance_chain_tip(count);
    }
}

pub fn sender() -> PrincipalData {
    StandardPrincipalData::transient().into()
}

/// Panics if `value` is an `(err ...)` response, so that a benchmark can never measure a failing
/// call by mistake.
pub fn expect_success(value: &Value, what: &str) {
    if let Value::Response(response) = value {
        assert!(response.committed, "{what} returned {value}");
    }
}

/// A chain on which the contracts of a benchmark are deployed, ready for the benchmarked call.
pub struct Prepared {
    pub chain: Chain,
    pub contract: ContractContext,
    pub args: Vec<Value>,
}

/// Deploys the contracts of `scenario` in order on a new chain, then runs `init` in its own
/// transaction calling into the target contract, to set up the state and produce the arguments of
/// the benchmarked call. Contracts are compiled to Wasm here, so compilation is never measured.
pub fn prepare<F>(engine: Engine, scenario: &Scenario, init: &F) -> Prepared
where
    F: Fn(&mut ExecutionState, &mut InvocationContext) -> Vec<Value>,
{
    let mut chain = Chain::new();
    let mut target = None;
    for contract in &scenario.contracts {
        let context = chain.deploy(engine, contract);
        if contract.name == scenario.target && target.is_none() {
            target = Some(context);
        }
    }
    let contract = target.expect("The target contract should be deployed");

    // A contract stored without a Wasm module is silently interpreted, which the crosscheck cannot
    // detect since both engines would then be the interpreter.
    let mut conn = ClarityDatabase::new(
        &mut chain.datastore,
        &chain.burn_datastore,
        &chain.burn_datastore,
    );
    conn.begin();
    for contract @ Contract { name, .. } in &scenario.contracts {
        let stored = conn
            .get_contract(&contract.id())
            .expect("Failed to load deployed contract");
        assert_eq!(
            stored.wasm_module.is_some(),
            matches!(engine, Engine::Webassembly),
            "{name} is not stored as expected for the {}",
            engine.name()
        );
    }
    conn.roll_back().unwrap();

    let mut cost_tracker = chain.cost_tracker();
    for step in &scenario.setup {
        match step {
            Step::Call {
                contract,
                function,
                args,
            } => {
                let (result, _) = chain.transaction(
                    &mut cost_tracker,
                    &scenario.contract_id(contract),
                    function,
                    &as_transaction_args(args),
                );
                expect_success(&result, &format!("Setup call to {contract}.{function}"));
            }
            Step::AdvanceBlocks(count) => chain.advance_blocks(*count),
        }
    }

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
pub fn crosscheck<F>(scenario: &Scenario, init: &F) -> [ExecutionCost; 2]
where
    F: Fn(&mut ExecutionState, &mut InvocationContext) -> Vec<Value>,
{
    let fn_name = scenario.function.as_str();
    let [(interpreted, interpreter_events, interpreter_cost), (wasm, wasm_events, wasm_cost)] =
        Engine::ALL.map(|engine| {
            let Prepared {
                mut chain,
                contract,
                args,
            } = prepare(engine, scenario, init);
            let mut cost_tracker = chain.cost_tracker();
            let (result, events) = chain.transaction(
                &mut cost_tracker,
                &contract.contract_identifier,
                fn_name,
                &as_transaction_args(&args),
            );
            expect_success(&result, &format!("{fn_name} on the {}", engine.name()));
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
pub fn check<F>(group_name: &str, param: Option<&str>, scenario: &Scenario, init: &F)
where
    F: Fn(&mut ExecutionState, &mut InvocationContext) -> Vec<Value>,
{
    record_costs(group_name, param, &crosscheck(scenario, init));
}

pub fn benchmark_id(engine: Engine, param: Option<&str>) -> BenchmarkId {
    match param {
        Some(param) => BenchmarkId::new(engine.name(), param),
        None => BenchmarkId::from_parameter(engine.name()),
    }
}

/// Benchmarks calling the function of `scenario` on both engines. All calls happen in a single
/// transaction, so this measures the function call alone.
pub fn bench_calls<F>(
    group: &mut BenchmarkGroup<WallTime>,
    param: Option<&str>,
    scenario: &Scenario,
    init: F,
) where
    F: Fn(&mut ExecutionState, &mut InvocationContext) -> Vec<Value>,
{
    assert!(
        !scenario.fresh_state,
        "Scenarios needing a fresh state can only be benchmarked as transactions"
    );
    for engine in Engine::ALL {
        group.bench_function(benchmark_id(engine, param), |b| {
            let Prepared {
                mut chain,
                contract,
                args,
            } = prepare(engine, scenario, &init);
            let func = contract
                .lookup_function(&scenario.function)
                .expect("failed to lookup function");
            chain.session(&contract, |exec_state, invoke_ctx| {
                b.iter(|| {
                    let result = exec_state
                        .execute_function_as_transaction(
                            invoke_ctx,
                            &func,
                            &args,
                            FunctionExecutionOptions::default(),
                        )
                        .expect("Function call failed");
                    expect_success(&result, &scenario.function);
                    result
                });
            });
        });
    }
}

/// Benchmarks a transaction calling the function of `scenario` on both engines, after checking
/// that they agree on the outcome. Each iteration is a whole transaction, as executed by a node:
/// setting up the execution context, loading the contract, calling it and committing. With a
/// [`Scenario::fresh_state`], each transaction runs on a copy of the prepared state, made outside of
/// the measurement.
pub fn bench_transactions<F>(
    group: &mut BenchmarkGroup<WallTime>,
    group_name: &str,
    param: Option<&str>,
    scenario: &Scenario,
    init: F,
) where
    F: Fn(&mut ExecutionState, &mut InvocationContext) -> Vec<Value>,
{
    check(group_name, param, scenario, &init);

    for engine in Engine::ALL {
        group.bench_function(benchmark_id(engine, param), |b| {
            let Prepared {
                mut chain,
                contract,
                args,
            } = prepare(engine, scenario, &init);
            let args = as_transaction_args(&args);
            let mut cost_tracker = chain.cost_tracker();
            let mut transaction = |chain: &mut Chain| {
                let (result, events) = chain.transaction(
                    &mut cost_tracker,
                    &contract.contract_identifier,
                    &scenario.function,
                    &args,
                );
                expect_success(&result, &scenario.function);
                (result, events)
            };
            if scenario.fresh_state {
                b.iter_batched_ref(
                    || chain.clone(),
                    |chain| transaction(chain),
                    BatchSize::SmallInput,
                );
            } else {
                b.iter(|| transaction(&mut chain));
            }
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
