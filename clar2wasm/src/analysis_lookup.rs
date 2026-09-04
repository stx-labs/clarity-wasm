//! Read access to previously stored contract analyses, used to resolve the contracts that a
//! contract under compilation depends on.
//!
//! The compilation pipeline needs the declared function types and trait definitions of every
//! contract the compiled contract refers to. Where those analyses come from depends on the
//! caller: the transaction deploy path reads them through an [`AnalysisDatabase`], while
//! just-in-time compilation of an already-deployed contract reads them through the
//! [`ClarityDatabase`] of the running transaction. The [`AnalysisLookup`] trait abstracts over
//! the two.

use std::collections::BTreeMap;

use clarity::types::StacksEpochId;
use clarity::vm::analysis::{AnalysisDatabase, ContractAnalysis};
use clarity::vm::database::ClarityDatabase;
use clarity::vm::errors::{StaticCheckError, StaticCheckErrorKind};
use clarity::vm::types::signatures::FunctionSignature;
use clarity::vm::types::{FunctionType, QualifiedContractIdentifier};
use clarity_types::ClarityName;

/// Source of stored contract analyses (and, where available, contract sources), used to resolve
/// the contracts that a contract under compilation depends on.
pub trait AnalysisLookup {
    /// The stored analysis of `contract_identifier`, exactly as it was stored (no epoch
    /// canonicalization), or `None` when no analysis is stored for it.
    fn contract_analysis(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
    ) -> Result<Option<ContractAnalysis>, StaticCheckError>;

    /// The stored source of `contract_identifier`, or `None` when it is not available. A lookup
    /// which cannot provide sources simply returns `Ok(None)`; sources are only needed to
    /// recompute the analysis of a dependency which has none stored.
    fn contract_source(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
    ) -> Result<Option<String>, StaticCheckError>;
}

impl AnalysisLookup for AnalysisDatabase<'_> {
    fn contract_analysis(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
    ) -> Result<Option<ContractAnalysis>, StaticCheckError> {
        self.load_contract_non_canonical(contract_identifier)
    }

    /// An [`AnalysisDatabase`] stores analyses only, so no source is ever returned.
    fn contract_source(
        &mut self,
        _contract_identifier: &QualifiedContractIdentifier,
    ) -> Result<Option<String>, StaticCheckError> {
        Ok(None)
    }
}

impl AnalysisLookup for ClarityDatabase<'_> {
    fn contract_analysis(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
    ) -> Result<Option<ContractAnalysis>, StaticCheckError> {
        self.load_contract_analysis(contract_identifier)
            .map_err(|e| {
                StaticCheckErrorKind::Unreachable(format!(
                    "failed to load the analysis of {contract_identifier}: {e}"
                ))
                .into()
            })
    }

    fn contract_source(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
    ) -> Result<Option<String>, StaticCheckError> {
        Ok(self.get_contract_src(contract_identifier))
    }
}

/// The declared type of the public or read-only function `function_name` of
/// `contract_identifier`, canonicalized to `epoch`, or `None` when the contract does not define
/// it. Errors when no analysis is stored for the contract, mirroring
/// [`AnalysisDatabase::get_public_function_type`].
pub(crate) fn function_type(
    lookup: &mut dyn AnalysisLookup,
    contract_identifier: &QualifiedContractIdentifier,
    function_name: &str,
    epoch: &StacksEpochId,
) -> Result<Option<FunctionType>, StaticCheckError> {
    let analysis = lookup.contract_analysis(contract_identifier)?.ok_or(
        StaticCheckErrorKind::NoSuchContract(contract_identifier.to_string()),
    )?;
    Ok(analysis
        .get_public_function_type(function_name)
        .or_else(|| analysis.get_read_only_function_type(function_name))
        .map(|x| x.canonicalize(epoch)))
}

/// The trait `trait_name` defined by `contract_identifier`, with its function signatures
/// canonicalized to `epoch`, or `None` when the contract does not define it. Errors when no
/// analysis is stored for the contract, mirroring [`AnalysisDatabase::get_defined_trait`].
pub(crate) fn defined_trait(
    lookup: &mut dyn AnalysisLookup,
    contract_identifier: &QualifiedContractIdentifier,
    trait_name: &str,
    epoch: &StacksEpochId,
) -> Result<Option<BTreeMap<ClarityName, FunctionSignature>>, StaticCheckError> {
    let analysis = lookup.contract_analysis(contract_identifier)?.ok_or(
        StaticCheckErrorKind::NoSuchContract(contract_identifier.to_string()),
    )?;
    Ok(analysis.get_defined_trait(trait_name).map(|trait_map| {
        trait_map
            .iter()
            .map(|(name, sig)| (name.clone(), sig.canonicalize(epoch)))
            .collect()
    }))
}
