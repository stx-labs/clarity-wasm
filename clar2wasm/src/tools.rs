//! The `tools` module contains tools for evaluating Clarity snippets.
//! It is intended for use in tooling and tests, but not intended to be used
//! in production.
#![allow(clippy::expect_used, clippy::unwrap_used)]

use std::collections::HashMap;
use std::sync::LazyLock;

use clarity::boot_util::boot_code_id;
use clarity::consts::{CHAIN_ID_MAINNET, CHAIN_ID_TESTNET};
use clarity::types::StacksEpochId;
use clarity::vm::analysis::run_analysis;
use clarity::vm::ast::build_ast;
use clarity::vm::clarity_wasm::CostMeter;
use clarity::vm::contexts::{EventBatch, GlobalContext};
use clarity::vm::costs::{CostTracker, ExecutionCost, LimitedCostTracker};
use clarity::vm::database::ClarityDatabase;
use clarity::vm::errors::{StaticCheckErrorKind, VmExecutionError, WasmError};
use clarity::vm::events::{SmartContractEventData, StacksTransactionEvent};
use clarity::vm::resource_limiter::ResourceLimiter;
use clarity::vm::types::{PrincipalData, QualifiedContractIdentifier, StandardPrincipalData};
use clarity::vm::{eval_all, ClarityVersion, ContractContext, ContractName, Value};
use clarity_types::types::TypeSignature;
use regex::Regex;

use crate::compile;
use crate::datastore::{BurnDatastore, Datastore, StacksConstants};
use crate::initialize::initialize_contract;
use crate::wasm_utils::get_type_in_memory_size;

const DEFAULT_ENV_AMOUNT: u128 = 1_000_000_000;

#[derive(Clone)]
pub struct TestEnvironment {
    contract_contexts: HashMap<String, ContractContext>,
    pub epoch: StacksEpochId,
    pub version: ClarityVersion,
    datastore: Datastore,
    burn_datastore: BurnDatastore,
    events: Vec<EventBatch>,
    is_mainnet: bool,
    chain_id: u32,
    emit_cost_code: bool,
    pub cost_tracker: LimitedCostTracker,
}

impl TestEnvironment {
    fn new_full(
        amount: u128,
        epoch: StacksEpochId,
        version: ClarityVersion,
        network: Network,
        emit_cost_code: bool,
    ) -> Self {
        assert!(
            Self::epoch_and_clarity_match(epoch, version),
            "[ERR] Provided epoch ({epoch}) and Clarity version ({version}) do not match."
        );

        let constants = StacksConstants::default();
        let burn_datastore = BurnDatastore::new(constants.clone());
        let mut datastore = Datastore::new();

        let (is_mainnet, chain_id) = match network {
            Network::Mainnet => (true, CHAIN_ID_MAINNET),
            Network::Testnet => (false, CHAIN_ID_TESTNET),
        };

        let mut conn = ClarityDatabase::new(&mut datastore, &burn_datastore, &burn_datastore);

        conn.begin();
        conn.set_clarity_epoch_version(epoch)
            .expect("Failed to set epoch version.");
        conn.commit().expect("Failed to commit.");

        // Setup block metadata for epochs that use marfed block time
        if epoch.uses_marfed_block_time() {
            conn.begin();
            conn.setup_block_metadata(Some(1))
                .expect("Failed to setup block metadata.");
            conn.commit().expect("Failed to commit block metadata.");
        }

        // Give one account a starting balance, to be used for testing.
        let recipient = PrincipalData::Standard(StandardPrincipalData::transient());
        let mut conn = ClarityDatabase::new(&mut datastore, &burn_datastore, &burn_datastore);
        execute(&mut conn, |database| {
            let mut snapshot = database.get_stx_balance_snapshot(&recipient)?;
            snapshot.credit(amount)?;
            snapshot.save()?;
            database.increment_ustx_liquid_supply(amount)
        })
        .expect("Failed to increment liquid supply.");

        let mut env = Self {
            contract_contexts: HashMap::new(),
            epoch,
            version,
            datastore,
            burn_datastore,
            events: vec![],
            is_mainnet,
            chain_id,
            emit_cost_code,
            cost_tracker: LimitedCostTracker::new_free(),
        };

        if env.emit_cost_code {
            // we only load boot contracts if we need to track cost
            for contract in BOOT_CONTRACTS {
                let _ = env
                    .inner_init_contract_with_snippet(
                        contract.name,
                        true,
                        contract.code,
                        contract.version,
                        contract.epoch,
                    )
                    .unwrap_or_else(|err| {
                        panic!(
                            "could not interpret boot contract: {}\nreason: {err}",
                            contract.name
                        )
                    });
            }

            let limit = ExecutionCost::from(CostMeter::INIT);

            let mut conn =
                ClarityDatabase::new(&mut env.datastore, &env.burn_datastore, &env.burn_datastore);

            env.cost_tracker =
                LimitedCostTracker::new(env.is_mainnet, env.chain_id, limit, &mut conn, env.epoch)
                    .expect("Creating cost tracker should succeed")
        }

        env
    }

    /// Creates a new environment instance with the specified epoch and Clarity version.
    ///
    /// # Parameters
    ///
    /// - `epoch`: The desired `StacksEpochId` for the environment.
    /// - `version`: The desired `ClarityVersion` for the environment.
    ///
    /// # Behavior
    ///
    /// This function first checks whether the provided `epoch` and `version` are compatible using
    /// `epoch_and_clarity_match`. If they do not match, it uses a default Clarity version that is
    /// appropriate for the given `epoch` (as determined by `ClarityVersion::default_for_epoch`), and
    /// prints a warning message indicating the mismatch and the defaulted values.
    ///
    /// Then, the function creates a new environment instance by calling `new_with_amount` with a
    /// default amount of `1_000_000_000` along with the validated `epoch` and `version`.
    ///
    /// # Returns
    ///
    /// An instance of the environment configured with the validated epoch and Clarity version.
    pub fn new(epoch: StacksEpochId, version: ClarityVersion) -> Self {
        Self::new_full(DEFAULT_ENV_AMOUNT, epoch, version, Network::Testnet, false)
    }

    pub fn new_with_amount(amount: u128, epoch: StacksEpochId, version: ClarityVersion) -> Self {
        Self::new_full(amount, epoch, version, Network::Testnet, false)
    }

    pub fn new_with_network(
        epoch: StacksEpochId,
        version: ClarityVersion,
        network: Network,
    ) -> Self {
        Self::new_full(DEFAULT_ENV_AMOUNT, epoch, version, network, false)
    }

    pub fn new_with_cost(epoch: StacksEpochId, version: ClarityVersion) -> Self {
        Self::new_full(DEFAULT_ENV_AMOUNT, epoch, version, Network::Testnet, true)
    }

    /// Checks whether the given epoch and Clarity version are compatible.
    ///
    /// # Parameters
    ///
    /// - `epoch`: The `StacksEpochId` representing the current epoch.
    /// - `version`: The `ClarityVersion` representing the Clarity version to check.
    ///
    /// # Returns
    ///
    /// Returns `true` if the specified `epoch` supports the given `ClarityVersion`,
    /// and `false` otherwise.
    ///
    pub fn epoch_and_clarity_match(epoch: StacksEpochId, version: ClarityVersion) -> bool {
        match (epoch, version) {
            // For Epoch10, no clarity version is supported.
            (StacksEpochId::Epoch10, _) => false,
            (epoch, version) => version <= ClarityVersion::default_for_epoch(epoch),
        }
    }

    pub fn init_contract_with_snippet(
        &mut self,
        contract_name: &str,
        snippet: &str,
    ) -> Result<Option<Value>, VmExecutionError> {
        self.inner_init_contract_with_snippet(
            contract_name,
            false,
            snippet,
            self.version,
            self.epoch,
        )
    }

    fn inner_init_contract_with_snippet(
        &mut self,
        contract_name: &str,
        is_boot_contract: bool,
        snippet: &str,
        version: ClarityVersion,
        epoch: StacksEpochId,
    ) -> Result<Option<Value>, VmExecutionError> {
        let contract_id = match is_boot_contract {
            false => QualifiedContractIdentifier::new(
                StandardPrincipalData::transient(),
                ContractName::try_from(contract_name)?,
            ),
            true => boot_code_id(contract_name, self.is_mainnet),
        };

        let mut compile_result = self
            .datastore
            .as_analysis_db()
            .execute(|analysis_db| {
                compile(
                    snippet,
                    &contract_id,
                    LimitedCostTracker::new_free(),
                    version,
                    epoch,
                    analysis_db,
                    !is_boot_contract && self.emit_cost_code,
                )
                .map_err(|e| {
                    StaticCheckErrorKind::Unreachable(format!("Compilation failure {e:?}"))
                })
            })
            .map_err(|e| VmExecutionError::Wasm(WasmError::WasmGeneratorError(format!("{e:?}"))))?;

        self.datastore
            .as_analysis_db()
            .execute(|analysis_db| {
                analysis_db.insert_contract(&contract_id, &compile_result.contract_analysis)
            })
            .expect("Failed to insert contract analysis.");

        let mut contract_context = ContractContext::new(contract_id.clone(), self.version);
        // compile_result.module.emit_wasm_file("test.wasm").unwrap();
        contract_context.set_wasm_module(compile_result.module.emit_wasm());

        let mut cost_tracker = LimitedCostTracker::new_free();
        std::mem::swap(&mut self.cost_tracker, &mut cost_tracker);

        let conn = ClarityDatabase::new(
            &mut self.datastore,
            &self.burn_datastore,
            &self.burn_datastore,
        );

        let mut global_context =
            GlobalContext::new(self.is_mainnet, self.chain_id, conn, cost_tracker, epoch);
        global_context.begin();
        global_context
            .execute(|g| g.database.insert_contract_hash(&contract_id, snippet))
            .expect("Failed to insert contract hash.");

        let return_val = initialize_contract(
            &mut global_context,
            &mut contract_context,
            None,
            &compile_result.contract_analysis,
        )?;

        let data_size = contract_context.data_size;
        global_context
            .database
            .insert_contract(&contract_id, contract_context.clone().into())?;
        global_context
            .database
            .set_contract_data_size(&contract_id, data_size)
            .expect("Failed to set contract data size.");

        let (_, events) = global_context.commit().unwrap();
        if let Some(events) = events {
            self.events.push(events);
        }

        self.contract_contexts
            .insert(contract_id.name.to_string(), contract_context);

        self.cost_tracker = global_context.cost_track;
        self.cost_tracker
            .add_cost(ExecutionCost::from(return_val.cost))
            .expect("Adding cost should succeed");

        Ok(return_val.ret)
    }

    pub fn evaluate(&mut self, snippet: &str) -> Result<Option<Value>, VmExecutionError> {
        self.init_contract_with_snippet("snippet", snippet)
    }

    pub fn get_contract_context(&self, contract_name: &str) -> Option<&ContractContext> {
        self.contract_contexts.get(contract_name)
    }

    pub fn get_events(&self) -> &Vec<EventBatch> {
        &self.events
    }

    pub fn advance_chain_tip(&mut self, count: u32) -> u32 {
        self.burn_datastore.advance_chain_tip(count);
        self.datastore.advance_chain_tip(count)
    }

    pub fn interpret_contract_with_snippet(
        &mut self,
        contract_name: &str,
        snippet: &str,
    ) -> Result<Option<Value>, VmExecutionError> {
        let contract_id = QualifiedContractIdentifier::new(
            StandardPrincipalData::transient(),
            ContractName::try_from(contract_name)?,
        );

        let contract_analysis = self
            .datastore
            .as_analysis_db()
            .execute(|analysis_db| {
                let mut cost_tracker = LimitedCostTracker::new_free();

                // Parse the contract
                let ast = build_ast(
                    &contract_id,
                    snippet,
                    &mut cost_tracker,
                    self.version,
                    self.epoch,
                )
                .map_err(|e| StaticCheckErrorKind::Unreachable(format!("{e:?}")))?;

                // Run the analysis passes
                run_analysis(
                    &contract_id,
                    &ast.expressions,
                    analysis_db,
                    false,
                    cost_tracker,
                    self.epoch,
                    self.version,
                    true,
                    ResourceLimiter::unlimited(),
                )
                .map_err(|boxed| StaticCheckErrorKind::Unreachable(format!("{:?}", boxed.0)))
            })
            .map_err(|e| VmExecutionError::Wasm(WasmError::WasmGeneratorError(format!("{e:?}"))))?;

        self.datastore
            .as_analysis_db()
            .execute(|analysis_db| analysis_db.insert_contract(&contract_id, &contract_analysis))
            .expect("Failed to insert contract analysis");

        let mut contract_context = ContractContext::new(contract_id.clone(), self.version);

        let conn = ClarityDatabase::new(
            &mut self.datastore,
            &self.burn_datastore,
            &self.burn_datastore,
        );

        let mut cost_tracker = LimitedCostTracker::new_free();
        std::mem::swap(&mut self.cost_tracker, &mut cost_tracker);

        let mut global_context = GlobalContext::new(
            self.is_mainnet,
            self.chain_id,
            conn,
            cost_tracker,
            self.epoch,
        );
        global_context.begin();

        global_context
            .database
            .insert_contract_hash(&contract_id, snippet)
            .expect("Failed to insert contract hash.");

        let result = eval_all(
            &contract_analysis.expressions,
            &mut contract_context,
            &mut global_context,
            None,
        )?;

        global_context
            .database
            .insert_contract(&contract_id, contract_context.clone().into())?;
        global_context
            .database
            .set_contract_data_size(&contract_id, contract_context.data_size)
            .expect("Failed to set contract data size.");

        let (_, events) = global_context.commit().unwrap();
        if let Some(events) = events {
            self.events.push(events);
        }

        self.contract_contexts
            .insert(contract_name.to_owned(), contract_context);

        self.cost_tracker = global_context.cost_track;
        Ok(result)
    }

    pub fn interpret(&mut self, snippet: &str) -> Result<Option<Value>, VmExecutionError> {
        self.interpret_contract_with_snippet("snippet", snippet)
    }
}

impl Default for TestEnvironment {
    fn default() -> Self {
        let version = TestConfig::clarity_version();
        Self::new(TestConfig::epoch_for_version(version), version)
    }
}

pub fn execute<F, T, E>(conn: &mut ClarityDatabase, f: F) -> std::result::Result<T, E>
where
    F: FnOnce(&mut ClarityDatabase) -> std::result::Result<T, E>,
{
    conn.begin();
    let result = f(conn).inspect_err(|_| conn.roll_back().expect("Failed to roll back"))?;
    conn.commit().expect("Failed to commit");
    Ok(result)
}

/// Evaluate a Clarity snippet at a specific epoch and version.
/// Returns an optional value -- the result of the evaluation.
pub fn evaluate_at(
    snippet: &str,
    epoch: StacksEpochId,
    version: ClarityVersion,
) -> Result<Option<Value>, VmExecutionError> {
    let mut env = TestEnvironment::new(epoch, version);
    env.evaluate(snippet)
}

/// Evaluate a Clarity snippet at a specific epoch and version, with a default
/// amount of money for the transient principal account.
/// Returns an optional value -- the result of the evaluation.
pub fn evaluate_at_with_amount(
    snippet: &str,
    amount: u128,
    epoch: StacksEpochId,
    version: ClarityVersion,
) -> Result<Option<Value>, VmExecutionError> {
    let mut env = TestEnvironment::new_with_amount(amount, epoch, version);
    env.evaluate(snippet)
}

/// Evaluate a Clarity snippet at the clarity version selected by the
/// `test-clarity-vN` features (latest if none is set) and its matching epoch.
/// Returns an optional value -- the result of the evaluation.
pub fn evaluate(snippet: &str) -> Result<Option<Value>, VmExecutionError> {
    let version = TestConfig::clarity_version();
    evaluate_at(snippet, TestConfig::epoch_for_version(version), version)
}

/// Interpret a Clarity snippet at a specific epoch and version.
/// Returns an optional value -- the result of the evaluation.
pub fn interpret_at(
    snippet: &str,
    epoch: StacksEpochId,
    version: ClarityVersion,
) -> Result<Option<Value>, VmExecutionError> {
    let mut env = TestEnvironment::new(epoch, version);
    env.interpret(snippet)
}

/// Interpret a Clarity snippet at a specific epoch and version, with a default
/// amount of money for the transient principal account.
/// Returns an optional value -- the result of the evaluation.
pub fn interpret_at_with_amount(
    snippet: &str,
    amount: u128,
    epoch: StacksEpochId,
    version: ClarityVersion,
) -> Result<Option<Value>, VmExecutionError> {
    let mut env = TestEnvironment::new_with_amount(amount, epoch, version);
    env.interpret(snippet)
}

/// Interprets a Clarity snippet at the clarity version selected by the
/// `test-clarity-vN` features (latest if none is set) and its matching epoch.
///
/// Must stay in sync with [`evaluate`]: `crosscheck_expect_failure` compares
/// the two, so they have to run at the same version and epoch.
/// Returns an optional value -- the result of the evaluation.
pub fn interpret(snippet: &str) -> Result<Option<Value>, VmExecutionError> {
    let version = TestConfig::clarity_version();
    interpret_at(snippet, TestConfig::epoch_for_version(version), version)
}

pub struct TestConfig;

impl TestConfig {
    /// Select a Clarity version based on enabled features.
    pub fn clarity_version() -> ClarityVersion {
        match () {
            _ if cfg!(feature = "test-clarity-v1") => ClarityVersion::Clarity1,
            _ if cfg!(feature = "test-clarity-v2") => ClarityVersion::Clarity2,
            _ if cfg!(feature = "test-clarity-v3") => ClarityVersion::Clarity3,
            _ if cfg!(feature = "test-clarity-v4") => ClarityVersion::Clarity4,
            _ if cfg!(feature = "test-clarity-v5") => ClarityVersion::Clarity5,
            _ => ClarityVersion::latest(),
        }
    }

    /// Latest Stacks epoch.
    pub fn latest_epoch() -> StacksEpochId {
        StacksEpochId::latest()
    }

    pub fn epoch_for_version(version: ClarityVersion) -> StacksEpochId {
        match version {
            ClarityVersion::Clarity1 => StacksEpochId::Epoch2_05,
            _ => StacksEpochId::latest(),
        }
    }
}

struct CrossEvalResult {
    env_interpreted: TestEnvironment,
    interpreted: Result<Option<Value>, VmExecutionError>,

    env_compiled: TestEnvironment,
    compiled: Result<Option<Value>, VmExecutionError>,
}

#[derive(Debug, Clone, Copy)]
enum KnownBug {
    /// [https://github.com/stacks-network/stacks-core/issues/4622]
    ListOfQualifiedPrincipal,
    /// A string literal ending with a backslash cannot be lexed by the parser v1.
    StringEndingWithBackslash,
}

impl KnownBug {
    fn check_for_known_bugs(
        compiled: &Result<Option<Value>, VmExecutionError>,
        interpreted: &Result<Option<Value>, VmExecutionError>,
        snippet: &str,
        version: ClarityVersion,
        epoch: StacksEpochId,
    ) -> Option<Self> {
        let check_predicate = |pred: &dyn Fn(&VmExecutionError) -> bool| {
            interpreted.as_ref().is_err_and(pred) && compiled.as_ref().is_err_and(pred)
        };

        // The parser v1 is used below epoch 2.1, and Clarity 1 is the only
        // version available on those epochs.
        let uses_parser_v1 = epoch < StacksEpochId::Epoch21 && version == ClarityVersion::Clarity1;

        if check_predicate(&Self::has_list_of_qualified_principal_issue) {
            Some(KnownBug::ListOfQualifiedPrincipal)
        } else if uses_parser_v1 && Self::has_string_ending_with_backslash(snippet) {
            Some(KnownBug::StringEndingWithBackslash)
        } else {
            None
        }
    }

    /// Allows to detect if a snippet contains a string literal ending with a
    /// backslash, which the parser v1 cannot lex.
    ///
    /// The parser v1 matches string literals with the regex
    /// `"(?P<value>((\\")|([[ -~]&&[^"]]))*)"`, which prefers the escaped quote
    /// alternative over a single character. When the last character of a string
    /// is a backslash, the closing quote is consumed as part of a `\"` escape and
    /// the literal keeps running until the next quote of the source.
    fn has_string_ending_with_backslash(snippet: &str) -> bool {
        let mut chars = snippet.chars();

        while let Some(c) = chars.next() {
            if c != '"' {
                continue;
            }

            // inside a string literal, until its closing quote
            let mut ends_with_backslash = false;
            while let Some(c) = chars.next() {
                match c {
                    '\\' => ends_with_backslash = chars.next() == Some('\\'),
                    '"' => break,
                    _ => ends_with_backslash = false,
                }
            }

            if ends_with_backslash {
                return true;
            }
        }

        false
    }

    /// Allows to detect if an error suffers from this issue:
    /// [https://github.com/stacks-network/stacks-core/issues/4622].
    fn has_list_of_qualified_principal_issue(err: &VmExecutionError) -> bool {
        static RGX: LazyLock<Regex> = LazyLock::new(|| {
            let regex = r#"expecting expression of type '.*(?:\(principal ([A-Z0-9]{41}\.[^\)]+)\)|principal).*', found '\(.*principal ([^\)]+).*\)'"#;
            Regex::new(regex).unwrap()
        });

        if let VmExecutionError::Wasm(WasmError::WasmGeneratorError(message)) = err {
            RGX.captures(message).is_some_and(|caps| {
                caps.get(1)
                    .is_none_or(|cap1| cap1.as_str() == caps.get(2).unwrap().as_str())
            })
        } else {
            false
        }
    }
}

impl CrossEvalResult {
    fn compare(&self, snippet: &str) {
        assert_eq!(
            self.compiled, self.interpreted,
            "Compiled and interpreted results diverge! {snippet}\ncompiled: {:?}\ninterpreted: {:?}",
            self.compiled, self.interpreted
        );

        compare_events(
            self.env_interpreted.get_events(),
            self.env_compiled.get_events(),
        );
    }
}

fn crosseval(snippet: &str, env: TestEnvironment) -> Result<CrossEvalResult, KnownBug> {
    let (version, epoch) = (env.version, env.epoch);

    let mut env_interpreted = env.clone();
    let interpreted = env_interpreted.interpret(snippet);

    let mut env_compiled = env;
    let compiled = env_compiled.evaluate(snippet);

    match KnownBug::check_for_known_bugs(&compiled, &interpreted, snippet, version, epoch) {
        Some(bug) => {
            println!("KNOW BUG TRIGGERED <{bug:?}>:\n\t{snippet}");
            Err(bug)
        }
        None => Ok(CrossEvalResult {
            env_interpreted,
            env_compiled,
            interpreted,
            compiled,
        }),
    }
}

fn execute_crosscheck(
    env: TestEnvironment,
    snippet: &str,
    pre_compare: impl FnOnce(&CrossEvalResult),
) -> Option<CrossEvalResult> {
    let result = match crosseval(snippet, env) {
        Ok(result) => result,
        Err(_bug) => {
            return None;
        }
    };

    pre_compare(&result);
    result.compare(snippet);

    Some(result)
}

pub fn crosscheck(snippet: &str, expected: Result<Option<Value>, VmExecutionError>) {
    crosscheck_with_epoch_and_version(
        snippet,
        expected,
        TestConfig::latest_epoch(),
        TestConfig::clarity_version(),
    );
}

pub fn crosscheck_with_amount(
    snippet: &str,
    amount: u128,
    expected: Result<Option<Value>, VmExecutionError>,
) {
    if let Some(eval) = execute_crosscheck(
        TestEnvironment::new_with_amount(
            amount,
            TestConfig::latest_epoch(),
            TestConfig::clarity_version(),
        ),
        snippet,
        |_| {},
    ) {
        assert_eq!(
            eval.compiled, expected,
            "value is not the expected {:?}",
            eval.compiled
        );
    }
}

pub fn crosscheck_with_env(
    snippet: &str,
    expected: Result<Option<Value>, VmExecutionError>,
    env: TestEnvironment,
) {
    if let Some(eval) = execute_crosscheck(env, snippet, |_| {}) {
        assert_eq!(
            eval.compiled, expected,
            "value is not the expected {:?}",
            eval.compiled
        );
    }
}

fn crosscheck_compare_only_with_env(snippet: &str, env: TestEnvironment) {
    // to avoid false positives when both the compiled and interpreted fail,
    // we don't allow failures in these tests
    execute_crosscheck(env, snippet, |result| {
        // If both interpreted and compiled results have errors, panic and
        // show both errors.
        // If only one fails, panic with the error from the failing one.
        match (result.interpreted.as_ref(), result.compiled.as_ref()) {
            (Err(interpreted_err), Err(compiled_err)) => {
                panic!(
                    "Interpreted and compiled snippets failed: {interpreted_err:?}, {compiled_err:?}"
                );
            }
            (Err(interpreted_err), Ok(_)) => {
                panic!("Interpreted snippet failed: {interpreted_err:?}");
            }
            (Ok(_), Err(compiled_err)) => {
                panic!("Compiled snippet failed: {compiled_err:?}");
            }
            _ => {
                // Both succeeded; no action needed.
            }
        }
    });
}

pub fn crosscheck_compare_only(snippet: &str) {
    crosscheck_compare_only_with_env(
        snippet,
        TestEnvironment::new(TestConfig::latest_epoch(), TestConfig::clarity_version()),
    );
}

pub fn crosscheck_compare_only_with_epoch_and_version(
    snippet: &str,
    epoch: StacksEpochId,
    version: ClarityVersion,
) {
    crosscheck_compare_only_with_env(snippet, TestEnvironment::new(epoch, version));
}

pub fn crosscheck_compare_only_with_expected_error<E: Fn(&VmExecutionError) -> bool>(
    snippet: &str,
    expected: E,
) {
    execute_crosscheck(
        TestEnvironment::new(TestConfig::latest_epoch(), TestConfig::clarity_version()),
        snippet,
        |result| {
            if let Err(e) = &result.compiled {
                if !expected(e) {
                    panic!("Compiled snippet failed with unexpected error: {e:?}");
                }
            }
        },
    );
}

/// Advance the block height to `count`, and uses identical TestEnvironment copies
/// to assert the results of a contract snippet running against the compiler and the interpreter.
pub fn crosscheck_compare_only_advancing_tip(snippet: &str, count: u32) {
    let mut env = TestEnvironment::new(TestConfig::latest_epoch(), TestConfig::clarity_version());
    env.advance_chain_tip(count);
    execute_crosscheck(env, snippet, |_| {});
}

pub fn crosscheck_with_epoch(
    snippet: &str,
    expected: Result<Option<Value>, VmExecutionError>,
    epoch: StacksEpochId,
) {
    crosscheck_with_epoch_and_version(snippet, expected, epoch, TestConfig::clarity_version());
}

pub fn crosscheck_with_epoch_and_version(
    snippet: &str,
    expected: Result<Option<Value>, VmExecutionError>,
    epoch: StacksEpochId,
    version: ClarityVersion,
) {
    if let Some(eval) = execute_crosscheck(TestEnvironment::new(epoch, version), snippet, |_| {}) {
        assert_eq!(
            eval.compiled, expected,
            "value is not the expected {:?}",
            eval.compiled
        );
    }
}

pub fn crosscheck_with_clarity_version(
    snippet: &str,
    expected: Result<Option<Value>, VmExecutionError>,
    version: ClarityVersion,
) {
    crosscheck_with_epoch_and_version(snippet, expected, TestConfig::latest_epoch(), version)
}

/// Crosscheck at the latest epoch, using the clarity version selected by the
/// `test-clarity-vN` features. Use this for tests whose snippet needs a recent
/// epoch even when an older clarity version is selected.
pub fn crosscheck_with_latest_epoch(
    snippet: &str,
    expected: Result<Option<Value>, VmExecutionError>,
) {
    crosscheck_with_epoch_and_version(
        snippet,
        expected,
        TestConfig::latest_epoch(),
        TestConfig::clarity_version(),
    )
}

pub fn crosscheck_validate<V: Fn(Value)>(snippet: &str, validator: V) {
    if let Some(eval) = execute_crosscheck(
        TestEnvironment::new(TestConfig::latest_epoch(), TestConfig::clarity_version()),
        snippet,
        |_| {},
    ) {
        let value = eval.compiled.unwrap().unwrap();
        validator(value)
    }
}

pub fn crosscheck_multi_contract(
    contracts: &[(ContractName, &str)],
    expected: Result<Option<Value>, VmExecutionError>,
) {
    crosscheck_multi_contract_with_env(contracts, expected, TestEnvironment::default())
}

pub fn crosscheck_multi_contract_with_env(
    contracts: &[(ContractName, &str)],
    expected: Result<Option<Value>, VmExecutionError>,
    env: TestEnvironment,
) {
    let (version, epoch) = (env.version, env.epoch);

    // compiled version
    let mut compiled_env = env.clone();
    let compiled_results: Vec<_> = contracts
        .iter()
        .map(|(name, snippet)| compiled_env.init_contract_with_snippet(name, snippet))
        .collect();

    // interpreted version
    let mut interpreted_env = env;
    let interpreted_results: Vec<_> = contracts
        .iter()
        .map(|(name, snippet)| interpreted_env.interpret_contract_with_snippet(name, snippet))
        .collect();

    // compare results contract by contract
    for ((cmp_res, int_res), (contract_name, snippet)) in compiled_results
        .iter()
        .zip(interpreted_results)
        .zip(contracts)
    {
        if let Some(bug) =
            KnownBug::check_for_known_bugs(cmp_res, &int_res, snippet, version, epoch)
        {
            println!("KNOW BUG TRIGGERED <{bug:?}>:\n\t{snippet}");
            return;
        }

        assert_eq!(
            cmp_res, &int_res,
            "Compiled and interpreted results diverge in contract \"{contract_name}\"\ncompiled: {cmp_res:?}\ninterpreted: {int_res:?}"
        );
    }

    // compare with expected final value
    let final_value = compiled_results.last().unwrap_or(&Ok(None));
    assert_eq!(
        final_value, &expected,
        "final value is not the expected {final_value:?}"
    );

    compare_events(interpreted_env.get_events(), compiled_env.get_events());
}

// TODO: This function is a temporary solution until issue #421 is addressed.
// Tests that call this function will need to be adjusted.
//
// Consider gating tests to epochs whenever possible
// using the `crosscheck_with_epoch` function.
pub fn crosscheck_expect_failure(snippet: &str) {
    crosscheck_expect_failure_with_clarity_version(snippet, TestConfig::clarity_version())
}

/// Same as [`crosscheck_expect_failure`], but at an explicit clarity version
/// instead of the one selected by the `test-clarity-vN` features.
pub fn crosscheck_expect_failure_with_clarity_version(snippet: &str, version: ClarityVersion) {
    let epoch = TestConfig::epoch_for_version(version);
    let compiled = evaluate_at(snippet, epoch, version);
    let interpreted = interpret_at(snippet, epoch, version);

    assert!(
        interpreted.is_err(),
        "Interpreted didn't err: {}\ninterpreted: {:?}",
        snippet,
        interpreted,
    );
    assert!(
        compiled.is_err(),
        "Compiled didn't err: {}\ncompiled: {:?}",
        snippet,
        compiled,
    );
}

fn compare_events(events_a: &[EventBatch], events_b: &[EventBatch]) {
    // `SmartContractEvent` `value` could differ but resulting in the same serialized
    // data (eg, serializing a `CallableContract` results in a contract principal)
    assert_eq!(
        events_a.len(),
        events_b.len(),
        "events batches size mismatch"
    );
    for (EventBatch { events: batch_a }, EventBatch { events: batch_b }) in
        events_a.iter().zip(events_b.iter())
    {
        assert_eq!(batch_a.len(), batch_b.len(), "events batch size mismatch");
        for (a, b) in batch_a.iter().zip(batch_b.iter()) {
            if let (
                StacksTransactionEvent::SmartContractEvent(SmartContractEventData {
                    key: key_a,
                    value: value_a,
                }),
                StacksTransactionEvent::SmartContractEvent(SmartContractEventData {
                    key: key_b,
                    value: value_b,
                }),
            ) = (a, b)
            {
                assert_eq!(key_a, key_b, "events key mismatch");

                let mut value_a_ser = vec![];
                value_a.serialize_write(&mut value_a_ser).unwrap();

                let mut value_b_ser = vec![];
                value_b.serialize_write(&mut value_b_ser).unwrap();

                assert_eq!(value_a_ser, value_b_ser, "events serialized value mismatch");
            } else {
                assert_eq!(a, b, "events mismatch")
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum Network {
    Mainnet,
    Testnet,
}

pub fn crosscheck_with_network(
    network: Network,
    snippet: &str,
    expected: Result<Option<Value>, VmExecutionError>,
) {
    let eval = match crosseval(
        snippet,
        TestEnvironment::new_with_network(
            TestConfig::latest_epoch(),
            TestConfig::clarity_version(),
            network,
        ),
    ) {
        Ok(result) => result,
        Err(_bug) => {
            return;
        }
    };

    eval.compare(snippet);

    assert_eq!(
        eval.compiled, expected,
        "value is not the expected {:?}",
        eval.compiled
    );
}

// Represents a boot contract on disk
struct BootContract {
    // The name of the contract
    name: &'static str,
    // The code of the contract
    code: &'static str,
    // Clarity version of the contract
    version: ClarityVersion,
    // Stacks epoch of deployment of the contract
    epoch: StacksEpochId,
}

macro_rules! boot_contract_code {
    ($name:literal) => {
        include_str!(concat!(
            "../tests/contracts/boot-contracts/",
            $name,
            ".clar"
        ))
    };
}

macro_rules! boot_contract {
    ($name:literal, $version:expr, $epoch:expr) => {
        BootContract {
            name: $name,
            code: boot_contract_code!($name),
            version: $version,
            epoch: $epoch,
        }
    };
    ($base:literal, $name:literal, $version:literal, $epoch:literal) => {
        BootContract {
            name: $name,
            code: concat!(boot_contract_code!($base), "\n", boot_contract_code!($name)),
            version: $version,
            epoch: $epoch,
        }
    };
}

const BOOT_CONTRACTS: &[BootContract] = &[
    COSTS_V1,
    COSTS_V2,
    COSTS_V2_TESTNET,
    COST_VOTING,
    COSTS_V3,
    COSTS_V4,
];

const COSTS_V1: BootContract =
    boot_contract!("costs", ClarityVersion::Clarity1, StacksEpochId::Epoch20);
const COSTS_V2: BootContract = boot_contract!(
    "costs-2",
    ClarityVersion::Clarity2,
    StacksEpochId::Epoch2_05
);
const COSTS_V2_TESTNET: BootContract = boot_contract!(
    "costs-2-testnet",
    ClarityVersion::Clarity2,
    StacksEpochId::Epoch2_05
);
const COST_VOTING: BootContract = boot_contract!(
    "cost-voting",
    ClarityVersion::Clarity2,
    StacksEpochId::Epoch2_05
);
const COSTS_V3: BootContract =
    boot_contract!("costs-3", ClarityVersion::Clarity2, StacksEpochId::Epoch21);
const COSTS_V4: BootContract =
    boot_contract!("costs-4", ClarityVersion::Clarity4, StacksEpochId::Epoch33);

/// Name of the buffer that will fill the empty space.
const IGNORE_BUFFER_NAME: &str = "ignore";
/// Size in memory for the buffer that will fill the empty space's (offset, len).
const IGNORE_BUFFER_SIZE: usize = 8;
/// Minimum size needed in memory to create a filling buffer
const IGNORE_BUFFER_MIN_SIZE_NEEDED: usize = IGNORE_BUFFER_SIZE + IGNORE_BUFFER_NAME.len();

/// Size of a page in Wasm
const WASM_PAGE_SIZE: usize = 65536;

#[allow(clippy::expect_used)]
pub fn as_oom_check_snippet(
    snippet: &str,
    args_types: &[TypeSignature],
    epoch: StacksEpochId,
    version: ClarityVersion,
) -> String {
    inner_as_oom_check_snippet(snippet, &[], args_types, epoch, version)
}

#[allow(clippy::expect_used)]
fn inner_as_oom_check_snippet(
    snippet: &str,
    contracts: &[(ContractName, &str)],
    args_types: &[TypeSignature],
    epoch: StacksEpochId,
    version: ClarityVersion,
) -> String {
    let mut datastore = Datastore::new();

    for (name, contract) in contracts {
        let contract_id =
            QualifiedContractIdentifier::new(StandardPrincipalData::transient(), name.clone());
        let contract_analysis = datastore
            .as_analysis_db()
            .execute(|analysis_db| {
                compile(
                    contract,
                    &contract_id,
                    LimitedCostTracker::new_free(),
                    version,
                    epoch,
                    analysis_db,
                    false,
                )
                .map_err(|e| {
                    StaticCheckErrorKind::Unreachable(format!("Compilation failure {e:?}"))
                })
            })
            .expect("Could not compile contract")
            .contract_analysis;

        datastore
            .as_analysis_db()
            .execute(|analysis_db| analysis_db.insert_contract(&contract_id, &contract_analysis))
            .expect("Could not insert contract analysis");
    }

    let compiled_module = datastore
        .as_analysis_db()
        .execute(|analysis_db| {
            compile(
                snippet,
                &QualifiedContractIdentifier::new(
                    StandardPrincipalData::transient(),
                    ContractName::from_literal("foo"),
                ),
                LimitedCostTracker::new_free(),
                version,
                epoch,
                analysis_db,
                false,
            )
            .map_err(|e| StaticCheckErrorKind::Unreachable(format!("Compilation failure {e:?}")))
        })
        .expect("Could not compile snippet")
        .module;

    // we look for the total number of pages that were allocated for the module.
    let memory_pages = compiled_module
        .memories
        .iter()
        .next()
        .expect("Couldn't find a memory")
        .initial as usize;
    // we look for the first byte in memory which doesn't contain useful data.
    let stack_pointer_value = match compiled_module
        .globals
        .iter()
        .find(|g| g.name.as_ref().is_some_and(|name| name == "stack-pointer"))
        .expect("Couldn't find stack-pointer global")
        .kind
    {
        walrus::GlobalKind::Local(walrus::InitExpr::Value(walrus::ir::Value::I32(val))) => {
            val as usize
        }
        _ => unreachable!("stack-pointer should be a locally declared global with a i32 value"),
    };

    // WORKAROUND: this is to ignore arguments that are computed at runtime and should be removed after fixing
    //             [issue #587](https://github.com/stacks-network/clarity-wasm/issues/587)
    let args_space_needed = args_types
        .iter()
        .map(|ty| get_type_in_memory_size(ty, false))
        .sum::<i32>() as usize;

    // the free space on the last page that we want to fill is the substraction of the total number of bytes
    // for all the available pages and the last byte which will contain useful data.
    let mut free_space_on_memory_page = memory_pages * WASM_PAGE_SIZE - stack_pointer_value;

    let total_space_needed = IGNORE_BUFFER_MIN_SIZE_NEEDED + args_space_needed;
    if free_space_on_memory_page < total_space_needed {
        free_space_on_memory_page += WASM_PAGE_SIZE;
    }

    format!(
        "(define-constant {IGNORE_BUFFER_NAME} 0x{})\n{snippet}",
        "00".repeat(free_space_on_memory_page - total_space_needed)
    )
}

// TODO: deprecate after fixing [issue #587](https://github.com/stacks-network/clarity-wasm/issues/587)
pub fn crosscheck_oom_with_non_literal_args(
    snippet: &str,
    args_types: &[TypeSignature],
    expected: Result<Option<Value>, VmExecutionError>,
) {
    crosscheck(
        &as_oom_check_snippet(
            snippet,
            args_types,
            TestConfig::latest_epoch(),
            TestConfig::clarity_version(),
        ),
        expected,
    );
}

pub fn crosscheck_oom_with_non_literal_args_compare_only(
    snippet: &str,
    args_types: &[TypeSignature],
    epoch: StacksEpochId,
    version: ClarityVersion,
) {
    crosscheck_compare_only(&as_oom_check_snippet(snippet, args_types, epoch, version));
}

pub fn crosscheck_oom(snippet: &str, expected: Result<Option<Value>, VmExecutionError>) {
    crosscheck_oom_with_non_literal_args(snippet, &[], expected)
}

/// Same as [`crosscheck_multi_contract`], but the last contract is padded to
/// fill its memory, so that it will run out of memory if it needs more space
/// than what was allocated for it.
#[allow(clippy::expect_used)]
pub fn crosscheck_oom_multi_contract(
    contracts: &[(ContractName, &str)],
    expected: Result<Option<Value>, VmExecutionError>,
) {
    let ((name, snippet), previous_contracts) = contracts
        .split_last()
        .expect("There should be at least one contract");

    let padded_snippet = inner_as_oom_check_snippet(
        snippet,
        previous_contracts,
        &[],
        TestConfig::latest_epoch(),
        TestConfig::clarity_version(),
    );

    let mut contracts = previous_contracts.to_vec();
    contracts.push((name.clone(), &padded_snippet));

    crosscheck_multi_contract(&contracts, expected);
}

pub fn crosscheck_oom_compare_only_with_epoch_and_version(
    snippet: &str,
    epoch: StacksEpochId,
    version: ClarityVersion,
) {
    crosscheck_oom_with_non_literal_args_compare_only(snippet, &[], epoch, version)
}

pub fn crosscheck_oom_with_env(
    snippet: &str,
    expected: Result<Option<Value>, VmExecutionError>,
    env: TestEnvironment,
) {
    crosscheck_with_env(
        &as_oom_check_snippet(snippet, &[], env.epoch, env.version),
        expected,
        env,
    );
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_evaluate_snippet() {
        assert_eq!(evaluate("(+ 1 2)"), Ok(Some(Value::Int(3))));
    }

    #[cfg(not(feature = "test-clarity-v1"))]
    #[test]
    fn test_compare_events() {
        let env = TestEnvironment::new(TestConfig::latest_epoch(), TestConfig::clarity_version());

        let mut env_interpreted = env.clone();
        let interpreted = env_interpreted.interpret("(stx-transfer-memo? u1 'S1G2081040G2081040G2081040G208105NK8PE5 'ST1PQHQKV0RJXZFY1DGX8MNSNYVE3VGZJSRTPGZGM 0x010203)");

        let mut env_compiled = env;
        let compiled = env_compiled.evaluate("(stx-transfer-memo? u1 'S1G2081040G2081040G2081040G208105NK8PE5 'ST1PQHQKV0RJXZFY1DGX8MNSNYVE3VGZJSRTPGZGM 0x010203)");

        CrossEvalResult {
            env_interpreted,
            env_compiled,
            interpreted,
            compiled,
        }
        .compare("");
    }

    #[cfg(not(feature = "test-clarity-v1"))]
    #[test]
    #[should_panic(expected = "events mismatch")]
    fn test_compare_events_mismatch() {
        let env = TestEnvironment::new(TestConfig::latest_epoch(), TestConfig::clarity_version());

        let mut env_interpreted = env.clone();
        let interpreted = env_interpreted.interpret("(stx-transfer-memo? u1 'S1G2081040G2081040G2081040G208105NK8PE5 'ST1PQHQKV0RJXZFY1DGX8MNSNYVE3VGZJSRTPGZGM 0x010203)");

        let mut env_compiled = env;
        let compiled = env_compiled.evaluate("(stx-transfer-memo? u1 'S1G2081040G2081040G2081040G208105NK8PE5 'ST1PQHQKV0RJXZFY1DGX8MNSNYVE3VGZJSRTPGZGM 0x0102FF)"); // different memo

        CrossEvalResult {
            env_interpreted,
            env_compiled,
            interpreted,
            compiled,
        }
        .compare("");
    }

    #[test]
    fn detect_list_of_qualified_principal_issue() {
        let snippet_no_wrap = r#"(index-of (list 'S53AR76V04QBY9CKZFQZ6FZF0730CEQS2AH761HTX.FoUtMZdXvouVYyvtvceMcRGotjQlzb) 'S53AR76V04QBY9CKZFQZ6FZF0730CEQS2AH761HTX.FoUtMZdXvouVYyvtvceMcRGotjQlzb)"#;

        // Pinned to the latest epoch: the bug being detected only reproduces
        // there, and `TestConfig` pairs Clarity 1 with Epoch 2.05.
        let e = interpret_at(
            snippet_no_wrap,
            TestConfig::latest_epoch(),
            TestConfig::clarity_version(),
        )
        .expect_err("Snippet should err due to bug");
        assert!(KnownBug::has_list_of_qualified_principal_issue(&e));
        crosscheck_with_latest_epoch(snippet_no_wrap, Ok(None)); // we don't care about the expected result

        let e = interpret_at(
            snippet_no_wrap,
            TestConfig::latest_epoch(),
            TestConfig::clarity_version(),
        )
        .expect_err("Snippet should err due to bug");
        assert!(KnownBug::has_list_of_qualified_principal_issue(&e));
        crosscheck_with_latest_epoch(snippet_no_wrap, Ok(None)); // we don't care about the expected result

        let snippet_simple = r#"(index-of (list (some 'S53AR76V04QBY9CKZFQZ6FZF0730CEQS2AH761HTX.FoUtMZdXvouVYyvtvceMcRGotjQlzb)) (some 'S53AR76V04QBY9CKZFQZ6FZF0730CEQS2AH761HTX.FoUtMZdXvouVYyvtvceMcRGotjQlzb))"#;

        let e = interpret_at(
            snippet_simple,
            TestConfig::latest_epoch(),
            TestConfig::clarity_version(),
        )
        .expect_err("Snippet should err due to bug");
        assert!(KnownBug::has_list_of_qualified_principal_issue(&e));
        crosscheck_with_latest_epoch(snippet_simple, Ok(None)); // we don't care about the expected result

        let e = interpret_at(
            snippet_simple,
            StacksEpochId::latest(),
            ClarityVersion::Clarity1,
        )
        .expect_err("Snippet should err due to bug");
        assert!(KnownBug::has_list_of_qualified_principal_issue(&e));
        crosscheck_with_latest_epoch(snippet_simple, Ok(None)); // we don't care about the expected result

        let snippet_no_rgx_2nd_match = r#"(index-of (list (ok 'S932CK89GTZ50W6ZHYT9FR8A625KMXTBN4FDHXFNW.a) (ok 'SH3MZSPN84M1NC77YFD2EV36NAS4EW9RNBXF4TGY3.A) (ok 'SME80C5G10ZJGHJA8Q1R4WH99ZV794GPH050DG87.A) (err u1409580484) (err u78298087165342409770641973297847909482) (ok 'ST1305A3CKDY8C2M3K9E7D8ZESND3W9RV4G7TSEAH.sSzXanZZmDqBadhzkhYweAFAdHVzWrlqToalG) (ok 'S61F1MAGPTM4Y3WEYE757PTZEGRY5D3FV2BG53STB.VXSrEfeDQmDpUQpbLcpTcpHhytHKnXQnbLLhw) (ok 'S939MQP0630GPK1S5RRKWDEXT5X8DEBW5T5PHXBTA.pBvEuNMOoLNHAkBpAyWkOgMQRXsuqs) (err u130787449693949619415771523117179796343) (ok 'SZ1NX5BPB8JTT5FZ86FD4R2H2A4FRSZYYYADEZPVM.GNlVpg)) (ok 'S61F1MAGPTM4Y3WEYE757PTZEGRY5D3FV2BG53STB.VXSrEfeDQmDpUQpbLcpTcpHhytHKnXQnbLLhw))"#;

        let e = interpret_at(
            snippet_no_rgx_2nd_match,
            TestConfig::latest_epoch(),
            TestConfig::clarity_version(),
        )
        .expect_err("Snippet should err due to bug");
        assert!(KnownBug::has_list_of_qualified_principal_issue(&e));
        crosscheck_with_latest_epoch(snippet_simple, Ok(None)); // we don't care about the expected result

        // Those tests below use `replace-at`, which didn't exist in Clarity 1
        #[cfg(not(feature = "test-clarity-v1"))]
        {
            let e = interpret_at(
                snippet_no_rgx_2nd_match,
                StacksEpochId::latest(),
                ClarityVersion::Clarity1,
            )
            .expect_err("Snippet should err due to bug");
            assert!(KnownBug::has_list_of_qualified_principal_issue(dbg!(&e)));
            crosscheck(snippet_simple, Ok(None)); // we don't care about the expected result

            let snippet_wrapped = r#"(replace-at?
            (list
                (err 'SX3M0F9YG3TS7YZDDV7B22H2C5J0BHG0WD0T3QSSN.DAHdSGMHgxMWaithtPBEqfuTWZGMqy)
                (ok 5)
            )
            u0
            (err 'SX3M0F9YG3TS7YZDDV7B22H2C5J0BHG0WD0T3QSSN.DAHdSGMHgxMWaithtPBEqfuTWZGMqy)
        )"#;

            let e = interpret(snippet_wrapped).expect_err("Snippet should err due to bug");
            assert!(KnownBug::has_list_of_qualified_principal_issue(&e));
            crosscheck(snippet_wrapped, Ok(None)); // we don't care about expected result

            let working_snippet = r#"(replace-at?
            (list
                (err 'SX3M0F9YG3TS7YZDDV7B22H2C5J0BHG0WD0T3QSSN)
                (err 'SX3M0F9YG3TS7YZDDV7B22H2C5J0BHG0WD0T3QSSN.DAHdSGMHgxMWaithtPBEqfuTWZGMqy)
                (ok 5)
            )
            u0
            (err 'SX3M0F9YG3TS7YZDDV7B22H2C5J0BHG0WD0T3QSSN.DAHdSGMHgxMWaithtPBEqfuTWZGMqy)
        )"#;
            assert!(interpret(working_snippet).is_ok());

            let snippet_different_err = r#"(replace-at?
            (list
                (err 'SX3M0F9YG3TS7YZDDV7B22H2C5J0BHG0WD0T3QSSN.DAHdSGMHgxMWaithtPBEqfuTWZGMqy)
                (ok 5)
            )
            u0
            (err 'SX3M0F9YG3TS7YZDDV7B22H2C5J0BHG0WD0T3QSSN.DAHdSGMHgxMWaithtPBEqfuTWZGMqy)
        "#;
            let res = interpret(snippet_different_err).expect_err("Should detect a syntax error");
            assert!(!KnownBug::has_list_of_qualified_principal_issue(&res));
        }
    }

    #[test]
    fn detect_string_ending_with_backslash_issue() {
        // A second string literal is needed after the offending one: the parser
        // v1 extends the first literal up to the next quote of the source, and
        // resumes lexing on the content of the second one. Depending on that
        // content, the failure is either an unlexable remainder or a missing
        // separator.
        for snippet in [
            r#"(list "a\\" "\\")"#,
            r#"(list u"a\\" u"\\")"#,
            r#"(list "a\\" "b")"#,
            r#"(list u"a\\" u"b")"#,
            r#"(list "\"a\\" "b")"#,
            r#"(list u"\u{1F600}a\\" u"b")"#,
        ] {
            let bug = crosseval(
                snippet,
                TestEnvironment::new(StacksEpochId::Epoch2_05, ClarityVersion::Clarity1),
            )
            .err()
            .expect("Snippet should trigger the known bug");
            assert!(matches!(bug, KnownBug::StringEndingWithBackslash));

            // The parser v2, used from epoch 2.1 on, lexes those snippets fine.
            crosseval(
                snippet,
                TestEnvironment::new(TestConfig::latest_epoch(), ClarityVersion::Clarity1),
            )
            .unwrap_or_else(|bug| panic!("Unexpected known bug <{bug:?}>"))
            .compare(snippet);
        }

        // A backslash which is not the last character of a string is lexed
        // correctly, even by the parser v1.
        for snippet in [r#"(list "a\\b" "c")"#, r#"(list u"a\\b" u"c")"#] {
            crosseval(
                snippet,
                TestEnvironment::new(StacksEpochId::Epoch2_05, ClarityVersion::Clarity1),
            )
            .unwrap_or_else(|bug| panic!("Unexpected known bug <{bug:?}>"))
            .compare(snippet);
        }
    }

    #[test]
    fn crosscheck_oom_compare_only_works() {
        let snippet = "(list 1 2 3)";
        crosscheck_oom_compare_only_with_epoch_and_version(
            snippet,
            StacksEpochId::latest(),
            ClarityVersion::latest(),
        );
    }
}
