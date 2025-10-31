//! The `tools` module contains tools for evaluating Clarity snippets.
//! It is intended for use in tooling and tests, but not intended to be used
//! in production.
#![allow(clippy::expect_used, clippy::unwrap_used)]

use std::collections::HashMap;
use std::sync::LazyLock;

use clarity::consts::{CHAIN_ID_MAINNET, CHAIN_ID_TESTNET};
use clarity::types::StacksEpochId;
use clarity::vm::analysis::run_analysis;
use clarity::vm::ast::build_ast;
use clarity::vm::contexts::{EventBatch, GlobalContext};
use clarity::vm::contracts::Contract;
use clarity::vm::costs::LimitedCostTracker;
use clarity::vm::database::ClarityDatabase;
use clarity::vm::errors::{CheckErrors, Error, WasmError};
use clarity::vm::events::{SmartContractEventData, StacksTransactionEvent};
use clarity::vm::types::{PrincipalData, QualifiedContractIdentifier, StandardPrincipalData};
use clarity::vm::{eval_all, ClarityVersion, ContractContext, ContractName, Value};
use regex::Regex;

use crate::compile;
use crate::datastore::{BurnDatastore, Datastore, StacksConstants};
use crate::initialize::initialize_contract;

#[derive(Clone)]
pub struct TestEnvironment {
    contract_contexts: HashMap<String, ContractContext>,
    pub epoch: StacksEpochId,
    pub version: ClarityVersion,
    datastore: Datastore,
    burn_datastore: BurnDatastore,
    cost_tracker: LimitedCostTracker,
    events: Vec<EventBatch>,
    network: Network,
}

impl TestEnvironment {
    pub fn new_with_amount(amount: u128, epoch: StacksEpochId, version: ClarityVersion) -> Self {
        let constants = StacksConstants::default();
        let burn_datastore = BurnDatastore::new(constants.clone());
        let mut datastore = Datastore::new();
        let cost_tracker = LimitedCostTracker::new_free();

        let mut db = ClarityDatabase::new(&mut datastore, &burn_datastore, &burn_datastore);
        db.begin();
        db.set_clarity_epoch_version(epoch)
            .expect("Failed to set epoch version.");
        db.commit().expect("Failed to commit.");

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

        Self {
            contract_contexts: HashMap::new(),
            epoch,
            version,
            datastore,
            burn_datastore,
            cost_tracker,
            events: vec![],
            network: Network::Testnet,
        }
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
    ///
    pub fn new(epoch: StacksEpochId, version: ClarityVersion) -> Self {
        let (epoch, version) = if !Self::epoch_and_clarity_match(epoch, version) {
            let valid_version = ClarityVersion::default_for_epoch(epoch);
            println!(
                "[WARN] Provided epoch ({epoch}) and Clarity version ({version}) do not match. \
                 Defaulting to epoch ({epoch}) and Clarity version ({valid_version})."
            );
            (epoch, valid_version)
        } else {
            (epoch, version)
        };

        Self::new_with_amount(1_000_000_000, epoch, version)
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

            // For epochs 20, 2_05, 21, 22, 23, 24, and 25,
            // Clarity1 and Clarity2 are supported but Clarity3 is not.
            (
                StacksEpochId::Epoch20
                | StacksEpochId::Epoch2_05
                | StacksEpochId::Epoch21
                | StacksEpochId::Epoch22
                | StacksEpochId::Epoch23
                | StacksEpochId::Epoch24
                | StacksEpochId::Epoch25,
                version,
            ) => version <= ClarityVersion::Clarity2,

            // For epochs 30, 31 and 32, all clarity versions are supported.
            (
                StacksEpochId::Epoch30
                | StacksEpochId::Epoch31
                | StacksEpochId::Epoch32
                | StacksEpochId::Epoch33,
                _,
            ) => true,
        }
    }

    pub fn new_with_network(
        epoch: StacksEpochId,
        version: ClarityVersion,
        network: Network,
    ) -> Self {
        let mut env = Self::new(epoch, version);
        env.network = network;
        env
    }

    pub fn init_contract_with_snippet(
        &mut self,
        contract_name: &str,
        snippet: &str,
    ) -> Result<Option<Value>, Error> {
        let contract_id = QualifiedContractIdentifier::new(
            StandardPrincipalData::transient(),
            (*contract_name).into(),
        );

        let mut compile_result = self
            .datastore
            .as_analysis_db()
            .execute(|analysis_db| {
                compile(
                    snippet,
                    &contract_id,
                    LimitedCostTracker::new_free(),
                    self.version,
                    self.epoch,
                    analysis_db,
                    false,
                )
                .map_err(|e| CheckErrors::Expects(format!("Compilation failure {e:?}")))
            })
            .map_err(|e| Error::Wasm(WasmError::WasmGeneratorError(format!("{e:?}"))))?;

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

        let (is_mainnet, chain_id) = match self.network {
            Network::Mainnet => (true, CHAIN_ID_MAINNET),
            Network::Testnet => (false, CHAIN_ID_TESTNET),
        };

        let mut global_context =
            GlobalContext::new(is_mainnet, chain_id, conn, cost_tracker, self.epoch);
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
        global_context.database.insert_contract(
            &contract_id,
            Contract {
                contract_context: contract_context.clone(),
            },
        )?;
        global_context
            .database
            .set_contract_data_size(&contract_id, data_size)
            .expect("Failed to set contract data size.");

        let (_, events) = global_context.commit().unwrap();
        if let Some(events) = events {
            self.events.push(events);
        }
        self.cost_tracker = global_context.cost_track;

        self.contract_contexts
            .insert(contract_name.to_string(), contract_context);

        Ok(return_val)
    }

    pub fn evaluate(&mut self, snippet: &str) -> Result<Option<Value>, Error> {
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
    ) -> Result<Option<Value>, Error> {
        let contract_id = QualifiedContractIdentifier::new(
            StandardPrincipalData::transient(),
            (*contract_name).into(),
        );

        let mut cost_tracker = LimitedCostTracker::new_free();
        std::mem::swap(&mut self.cost_tracker, &mut cost_tracker);

        let mut contract_analysis = self.datastore.as_analysis_db().execute(|analysis_db| {
            // Parse the contract
            let ast = build_ast(
                &contract_id,
                snippet,
                &mut self.cost_tracker,
                self.version,
                self.epoch,
            )
            .map_err(|e| Error::Wasm(WasmError::WasmGeneratorError(format!("{e:?}"))))?;

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
            )
            .map_err(|boxed| Error::Wasm(WasmError::WasmGeneratorError(format!("{:?}", boxed.0))))
        })?;

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

        let (is_mainnet, chain_id) = match self.network {
            Network::Mainnet => (true, CHAIN_ID_MAINNET),
            Network::Testnet => (false, CHAIN_ID_TESTNET),
        };

        let mut global_context = GlobalContext::new(
            is_mainnet,
            chain_id,
            conn,
            contract_analysis.cost_track.take().unwrap(),
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

        global_context.database.insert_contract(
            &contract_id,
            Contract {
                contract_context: contract_context.clone(),
            },
        )?;
        global_context
            .database
            .set_contract_data_size(&contract_id, contract_context.data_size)
            .expect("Failed to set contract data size.");

        let (_, events) = global_context.commit().unwrap();
        if let Some(events) = events {
            self.events.push(events);
        }
        self.cost_tracker = global_context.cost_track;

        self.contract_contexts
            .insert(contract_name.to_owned(), contract_context);

        Ok(result)
    }

    pub fn interpret(&mut self, snippet: &str) -> Result<Option<Value>, Error> {
        self.interpret_contract_with_snippet("snippet", snippet)
    }
}

impl Default for TestEnvironment {
    fn default() -> Self {
        Self::new(StacksEpochId::Epoch31, ClarityVersion::Clarity3)
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
) -> Result<Option<Value>, Error> {
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
) -> Result<Option<Value>, Error> {
    let mut env = TestEnvironment::new_with_amount(amount, epoch, version);
    env.evaluate(snippet)
}

/// Evaluate a Clarity snippet at the latest epoch and clarity version.
/// Returns an optional value -- the result of the evaluation.
pub fn evaluate(snippet: &str) -> Result<Option<Value>, Error> {
    evaluate_at(snippet, StacksEpochId::latest(), ClarityVersion::latest())
}

/// Interpret a Clarity snippet at a specific epoch and version.
/// Returns an optional value -- the result of the evaluation.
pub fn interpret_at(
    snippet: &str,
    epoch: StacksEpochId,
    version: ClarityVersion,
) -> Result<Option<Value>, Error> {
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
) -> Result<Option<Value>, Error> {
    let mut env = TestEnvironment::new_with_amount(amount, epoch, version);
    env.interpret(snippet)
}

/// Interprets a Clarity snippet at the latest epoch and clarity version.
/// Returns an optional value -- the result of the evaluation.
pub fn interpret(snippet: &str) -> Result<Option<Value>, Error> {
    interpret_at(snippet, StacksEpochId::latest(), ClarityVersion::latest())
}

pub struct TestConfig;

impl TestConfig {
    /// Select a Clarity version based on enabled features.
    pub fn clarity_version() -> ClarityVersion {
        match () {
            _ if cfg!(feature = "test-clarity-v1") => ClarityVersion::Clarity1,
            _ if cfg!(feature = "test-clarity-v2") => ClarityVersion::Clarity2,
            _ if cfg!(feature = "test-clarity-v3") => ClarityVersion::Clarity3,
            _ => ClarityVersion::latest(),
        }
    }

    /// Latest Stacks epoch.
    pub fn latest_epoch() -> StacksEpochId {
        StacksEpochId::latest()
    }
}

struct CrossEvalResult {
    env_interpreted: TestEnvironment,
    interpreted: Result<Option<Value>, Error>,

    env_compiled: TestEnvironment,
    compiled: Result<Option<Value>, Error>,
}

#[derive(Debug, Clone, Copy)]
enum KnownBug {
    /// [https://github.com/stacks-network/stacks-core/issues/4622]
    ListOfQualifiedPrincipal,
}

impl KnownBug {
    fn check_for_known_bugs(
        compiled: &Result<Option<Value>, Error>,
        interpreted: &Result<Option<Value>, Error>,
    ) -> Option<Self> {
        let check_predicate = |pred: &dyn Fn(&Error) -> bool| {
            interpreted.as_ref().is_err_and(pred) && compiled.as_ref().is_err_and(pred)
        };

        if check_predicate(&Self::has_list_of_qualified_principal_issue) {
            Some(KnownBug::ListOfQualifiedPrincipal)
        } else {
            None
        }
    }

    /// Allows to detect if an error suffers from this issue:
    /// [https://github.com/stacks-network/stacks-core/issues/4622].
    fn has_list_of_qualified_principal_issue(err: &Error) -> bool {
        static RGX: LazyLock<Regex> = LazyLock::new(|| {
            let regex = r#"expecting expression of type '.*(?:\(principal ([A-Z0-9]{41}\.[^\)]+)\)|principal).*', found '\(.*principal ([^\)]+).*\)'"#;
            Regex::new(regex).unwrap()
        });

        if let Error::Wasm(WasmError::WasmGeneratorError(message)) = err {
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
    let mut env_interpreted = env.clone();
    let interpreted = env_interpreted.interpret(snippet);

    let mut env_compiled = env;
    let compiled = env_compiled.evaluate(snippet);

    match KnownBug::check_for_known_bugs(&compiled, &interpreted) {
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

pub fn crosscheck(snippet: &str, expected: Result<Option<Value>, Error>) {
    if let Some(eval) = execute_crosscheck(
        TestEnvironment::new(TestConfig::latest_epoch(), TestConfig::clarity_version()),
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

pub fn crosscheck_with_amount(snippet: &str, amount: u128, expected: Result<Option<Value>, Error>) {
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
    expected: Result<Option<Value>, Error>,
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

pub fn crosscheck_compare_only_with_expected_error<E: Fn(&Error) -> bool>(
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
    expected: Result<Option<Value>, Error>,
    epoch: StacksEpochId,
) {
    if let Some(eval) = execute_crosscheck(
        TestEnvironment::new(epoch, TestConfig::clarity_version()),
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

pub fn crosscheck_with_clarity_version(
    snippet: &str,
    expected: Result<Option<Value>, Error>,
    version: ClarityVersion,
) {
    if let Some(eval) = execute_crosscheck(
        TestEnvironment::new(TestConfig::latest_epoch(), version),
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
    expected: Result<Option<Value>, Error>,
) {
    // compiled version
    let mut compiled_env = TestEnvironment::default();
    let compiled_results: Vec<_> = contracts
        .iter()
        .map(|(name, snippet)| compiled_env.init_contract_with_snippet(name, snippet))
        .collect();

    // interpreted version
    let mut interpreted_env = TestEnvironment::default();
    let interpreted_results: Vec<_> = contracts
        .iter()
        .map(|(name, snippet)| interpreted_env.interpret_contract_with_snippet(name, snippet))
        .collect();

    // compare results contract by contract
    for ((cmp_res, int_res), (contract_name, _)) in compiled_results
        .iter()
        .zip(interpreted_results)
        .zip(contracts)
    {
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
    let compiled = evaluate(snippet);
    let interpreted = interpret(snippet);

    assert!(
        interpreted.is_err(),
        "Interpreted didn't err: {}\ninterpreted: {:?}",
        snippet,
        &interpreted,
    );
    assert!(
        compiled.is_err(),
        "Compiled didn't err: {}\ncompiled: {:?}",
        snippet,
        &compiled,
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
    expected: Result<Option<Value>, Error>,
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

        let e = interpret(snippet_no_wrap).expect_err("Snippet should err due to bug");
        assert!(KnownBug::has_list_of_qualified_principal_issue(&e));
        crosscheck(snippet_no_wrap, Ok(None)); // we don't care about the expected result

        let e = interpret_at(
            snippet_no_wrap,
            StacksEpochId::latest(),
            ClarityVersion::Clarity1,
        )
        .expect_err("Snippet should err due to bug");
        assert!(KnownBug::has_list_of_qualified_principal_issue(&e));
        crosscheck(snippet_no_wrap, Ok(None)); // we don't care about the expected result

        let snippet_simple = r#"(index-of (list (some 'S53AR76V04QBY9CKZFQZ6FZF0730CEQS2AH761HTX.FoUtMZdXvouVYyvtvceMcRGotjQlzb)) (some 'S53AR76V04QBY9CKZFQZ6FZF0730CEQS2AH761HTX.FoUtMZdXvouVYyvtvceMcRGotjQlzb))"#;

        let e = interpret(snippet_simple).expect_err("Snippet should err due to bug");
        assert!(KnownBug::has_list_of_qualified_principal_issue(&e));
        crosscheck(snippet_simple, Ok(None)); // we don't care about the expected result

        let e = interpret_at(
            snippet_simple,
            StacksEpochId::latest(),
            ClarityVersion::Clarity1,
        )
        .expect_err("Snippet should err due to bug");
        assert!(KnownBug::has_list_of_qualified_principal_issue(&e));
        crosscheck(snippet_simple, Ok(None)); // we don't care about the expected result

        let snippet_no_rgx_2nd_match = r#"(index-of (list (ok 'S932CK89GTZ50W6ZHYT9FR8A625KMXTBN4FDHXFNW.a) (ok 'SH3MZSPN84M1NC77YFD2EV36NAS4EW9RNBXF4TGY3.A) (ok 'SME80C5G10ZJGHJA8Q1R4WH99ZV794GPH050DG87.A) (err u1409580484) (err u78298087165342409770641973297847909482) (ok 'ST1305A3CKDY8C2M3K9E7D8ZESND3W9RV4G7TSEAH.sSzXanZZmDqBadhzkhYweAFAdHVzWrlqToalG) (ok 'S61F1MAGPTM4Y3WEYE757PTZEGRY5D3FV2BG53STB.VXSrEfeDQmDpUQpbLcpTcpHhytHKnXQnbLLhw) (ok 'S939MQP0630GPK1S5RRKWDEXT5X8DEBW5T5PHXBTA.pBvEuNMOoLNHAkBpAyWkOgMQRXsuqs) (err u130787449693949619415771523117179796343) (ok 'SZ1NX5BPB8JTT5FZ86FD4R2H2A4FRSZYYYADEZPVM.GNlVpg)) (ok 'S61F1MAGPTM4Y3WEYE757PTZEGRY5D3FV2BG53STB.VXSrEfeDQmDpUQpbLcpTcpHhytHKnXQnbLLhw))"#;

        let e = interpret(snippet_no_rgx_2nd_match).expect_err("Snippet should err due to bug");
        assert!(KnownBug::has_list_of_qualified_principal_issue(&e));
        crosscheck(snippet_simple, Ok(None)); // we don't care about the expected result

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
}
