//! Just-in-time compilation of contracts which are already deployed.
//!
//! Contracts are normally compiled to Wasm when they are deployed, and the compiled module is
//! stored with the contract. Some contracts have no stored module: boot contracts, and any
//! contract which was deployed before Wasm compilation was enabled. This module compiles such a
//! contract from its stored source, resolving the analyses of the contracts it depends on
//! through an [`AnalysisLookup`].

use std::collections::HashSet;
use std::fmt;

use clarity::types::StacksEpochId;
use clarity::vm::analysis::{run_analysis, AnalysisDatabase};
use clarity::vm::ast::build_ast;
use clarity::vm::costs::LimitedCostTracker;
use clarity::vm::representations::{SymbolicExpression, SymbolicExpressionType, TraitDefinition};
use clarity::vm::resource_limiter::ResourceLimiter;
use clarity::vm::types::{PrincipalData, QualifiedContractIdentifier, Value};
use clarity::vm::ClarityVersion;

use crate::analysis_lookup::AnalysisLookup;
use crate::datastore::Datastore;
use crate::{compile, CompileError, CompileResult};

/// Why compiling an already-deployed contract failed: see [`compile_deployed_contract`].
#[derive(Debug)]
pub enum DeployedCompileError {
    /// No source is stored for the contract.
    MissingSource(QualifiedContractIdentifier),
    /// Reading a stored analysis or source through the [`AnalysisLookup`] failed, or a
    /// dependency could not be prepared for the type checker.
    Lookup(String),
    /// Parsing, type checking, or code generation failed.
    Compile(String),
}

impl fmt::Display for DeployedCompileError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DeployedCompileError::MissingSource(contract_identifier) => {
                write!(f, "no stored source for contract {contract_identifier}")
            }
            DeployedCompileError::Lookup(message) | DeployedCompileError::Compile(message) => {
                write!(f, "{message}")
            }
        }
    }
}

impl std::error::Error for DeployedCompileError {}

/// Compile the already-deployed contract `contract_identifier` to Wasm, without cost
/// instrumentation, resolving its source and the analyses of its dependencies through `lookup`.
///
/// The contract is compiled from its stored source, with the `clarity_version` and `epoch` it
/// was deployed with, so that the generated code matches the analysis the contract was accepted
/// with.
///
/// The type checker needs the analyses of every contract this one refers to. Those are read
/// through `lookup` and copied into a scratch analysis database for the compile: see
/// [`seed_dependency_analyses`].
pub fn compile_deployed_contract(
    lookup: &mut dyn AnalysisLookup,
    contract_identifier: &QualifiedContractIdentifier,
    clarity_version: ClarityVersion,
    epoch: StacksEpochId,
) -> Result<CompileResult, DeployedCompileError> {
    let source = lookup
        .contract_source(contract_identifier)
        .map_err(|e| DeployedCompileError::Lookup(e.to_string()))?
        .ok_or_else(|| DeployedCompileError::MissingSource(contract_identifier.clone()))?;

    // Parse the contract to find the contracts it depends on. `compile()` parses it again, but
    // the dependencies' analyses have to be in place before it runs.
    let ast = build_ast(
        contract_identifier,
        &source,
        &mut LimitedCostTracker::new_free(),
        clarity_version,
        epoch,
    )
    .map_err(|e| {
        DeployedCompileError::Compile(format!(
            "failed to parse contract {contract_identifier}: {e}"
        ))
    })?;

    let mut datastore = Datastore::new();
    let mut analysis_db = datastore.as_analysis_db();
    // This context is deliberately never committed: the analyses only have to be readable for
    // the duration of the compile, and an uncommitted write is served from the rollback layer
    // without the scratch store needing contract metadata prepared for it.
    analysis_db.begin();

    let mut seeded = HashSet::from([contract_identifier.clone()]);
    seed_dependency_analyses(
        lookup,
        &mut analysis_db,
        &ast.expressions,
        clarity_version,
        epoch,
        &mut seeded,
    )?;

    compile(
        &source,
        contract_identifier,
        LimitedCostTracker::new_free(),
        clarity_version,
        epoch,
        &mut analysis_db,
        false,
    )
    .map_err(|CompileError::Generic { diagnostics, .. }| {
        let diagnostics: Vec<String> = diagnostics.iter().map(|d| d.to_string()).collect();
        DeployedCompileError::Compile(format!(
            "failed to compile contract {contract_identifier}: {}",
            diagnostics.join("; ")
        ))
    })
}

/// Record, in `analysis_db`, the analysis of every contract referenced by `expressions`, so that
/// the type checker can resolve the calls and traits in the contract being compiled.
///
/// A contract's analysis is normally read straight from `lookup`, where the deploy path saved
/// it. When there is none stored -- test harnesses which publish contracts without saving an
/// analysis -- it is recomputed from the contract's source, after seeding that contract's own
/// dependencies. Recomputing uses the `clarity_version` and `epoch` of the contract being
/// compiled, since the deployment parameters of an unanalyzed contract are not recorded
/// anywhere.
///
/// A referenced contract with neither a stored analysis nor stored source is skipped: if the
/// type checker genuinely needs it, it reports it as an unresolved contract.
fn seed_dependency_analyses(
    lookup: &mut dyn AnalysisLookup,
    analysis_db: &mut AnalysisDatabase,
    expressions: &[SymbolicExpression],
    clarity_version: ClarityVersion,
    epoch: StacksEpochId,
    seeded: &mut HashSet<QualifiedContractIdentifier>,
) -> Result<(), DeployedCompileError> {
    let mut dependencies = vec![];
    collect_dependencies(expressions, &mut dependencies);

    for dependency in dependencies {
        if !seeded.insert(dependency.clone()) {
            continue;
        }

        if let Some(analysis) = lookup
            .contract_analysis(&dependency)
            .map_err(|e| DeployedCompileError::Lookup(e.to_string()))?
        {
            analysis_db
                .insert_contract(&dependency, &analysis)
                .map_err(|e| {
                    DeployedCompileError::Lookup(format!(
                        "failed to record the analysis of {dependency}: {e}"
                    ))
                })?;
            continue;
        }

        let Some(source) = lookup
            .contract_source(&dependency)
            .map_err(|e| DeployedCompileError::Lookup(e.to_string()))?
        else {
            continue;
        };

        let ast = build_ast(
            &dependency,
            &source,
            &mut LimitedCostTracker::new_free(),
            clarity_version,
            epoch,
        )
        .map_err(|e| {
            DeployedCompileError::Compile(format!("failed to parse contract {dependency}: {e}"))
        })?;

        seed_dependency_analyses(
            lookup,
            analysis_db,
            &ast.expressions,
            clarity_version,
            epoch,
            seeded,
        )?;

        run_analysis(
            &dependency,
            &ast.expressions,
            analysis_db,
            true,
            LimitedCostTracker::new_free(),
            epoch,
            clarity_version,
            true,
            ResourceLimiter::unlimited(),
        )
        .map_err(|e| {
            DeployedCompileError::Compile(format!(
                "failed to analyze contract {dependency}: {}",
                e.0
            ))
        })?;
    }

    Ok(())
}

/// Collect the contracts referenced by `expressions`: the targets of `contract-call?`, the
/// contracts defining the traits which are used or implemented, and any other contract principal
/// appearing in the source.
///
/// Over-collecting is harmless -- a contract which is named but has no analysis to copy is
/// simply skipped -- so every contract principal in the source is reported.
fn collect_dependencies(
    expressions: &[SymbolicExpression],
    dependencies: &mut Vec<QualifiedContractIdentifier>,
) {
    for expression in expressions {
        match &expression.expr {
            SymbolicExpressionType::List(inner) => collect_dependencies(inner, dependencies),
            SymbolicExpressionType::LiteralValue(Value::Principal(PrincipalData::Contract(
                contract_identifier,
            )))
            | SymbolicExpressionType::AtomValue(Value::Principal(PrincipalData::Contract(
                contract_identifier,
            ))) => dependencies.push(contract_identifier.clone()),
            SymbolicExpressionType::Field(trait_identifier) => {
                dependencies.push(trait_identifier.contract_identifier.clone())
            }
            SymbolicExpressionType::TraitReference(
                _,
                TraitDefinition::Defined(trait_identifier)
                | TraitDefinition::Imported(trait_identifier),
            ) => dependencies.push(trait_identifier.contract_identifier.clone()),
            _ => {}
        }
    }
}
