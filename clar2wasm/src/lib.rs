use clarity::types::StacksEpochId;
use clarity::vm::analysis::{run_analysis, AnalysisDatabase, ContractAnalysis};
use clarity::vm::ast::{build_ast_with_diagnostics, ContractAST};
use clarity::vm::costs::{ExecutionCost, LimitedCostTracker};
use clarity::vm::diagnostic::Diagnostic;
use clarity::vm::errors::StaticCheckError;
use clarity::vm::resource_limiter::ResourceLimiter;
use clarity::vm::types::QualifiedContractIdentifier;
use clarity::vm::ClarityVersion;
pub use walrus::Module;
use wasm_generator::{GeneratorError, WasmGenerator};

use crate::utils::annotate_types_for_contract_calls;

pub mod analysis_lookup;
mod cost;
mod deployed;

pub use analysis_lookup::AnalysisLookup;
pub use deployed::{compile_deployed_contract, DeployedCompileError};

mod deserialize;
pub mod initialize;
pub mod linker;
mod serialize;
pub mod wasm_generator;
pub mod wasm_utils;
mod words;

pub mod datastore;
pub mod tools;

mod copy;
mod debug_msg;
pub mod duck_type;
mod error_mapping;

#[cfg(feature = "developer-mode")]
pub mod test_utils;

// FIXME: This is copied from stacks-blockchain
// Block limit in Stacks 2.1
pub const BLOCK_LIMIT_MAINNET_21: ExecutionCost = ExecutionCost {
    write_length: 15_000_000,
    write_count: 15_000,
    read_length: 100_000_000,
    read_count: 15_000,
    runtime: 5_000_000_000,
};

#[derive(Debug)]
pub struct CompileResult {
    pub ast: ContractAST,
    pub diagnostics: Vec<Diagnostic>,
    pub module: Module,
    pub contract_analysis: ContractAnalysis,
}

#[derive(Debug)]
pub enum CompileError {
    Generic {
        ast: Box<ContractAST>,
        diagnostics: Vec<Diagnostic>,
        cost_tracker: Box<LimitedCostTracker>,
    },
}

pub fn compile(
    source: &str,
    contract_id: &QualifiedContractIdentifier,
    mut cost_tracker: LimitedCostTracker,
    clarity_version: ClarityVersion,
    epoch: StacksEpochId,
    analysis_db: &mut AnalysisDatabase,
    emit_cost_code: bool,
) -> Result<CompileResult, CompileError> {
    // Parse the contract
    let (ast, mut diagnostics, success) = build_ast_with_diagnostics(
        contract_id,
        source,
        &mut cost_tracker,
        clarity_version,
        epoch,
    );

    if !success {
        return Err(CompileError::Generic {
            ast: Box::new(ast),
            diagnostics,
            cost_tracker: Box::new(cost_tracker),
        });
    }

    // Run the analysis passes
    let mut contract_analysis = match run_analysis(
        contract_id,
        &ast.expressions,
        analysis_db,
        false,
        cost_tracker,
        epoch,
        clarity_version,
        true,
        ResourceLimiter::unlimited(),
    ) {
        Ok(contract_analysis) => contract_analysis,
        Err(boxed) => {
            let (e, cost_track) = *boxed;
            diagnostics.push(Diagnostic::err(e.err.as_ref()));
            return Err(CompileError::Generic {
                ast: Box::new(ast),
                diagnostics,
                cost_tracker: Box::new(cost_track),
            });
        }
    };

    match generate_module_from_analysis(&mut contract_analysis, &ast, analysis_db, emit_cost_code) {
        Ok(module) => Ok(CompileResult {
            ast,
            diagnostics,
            module,
            contract_analysis,
        }),
        Err(e) => {
            diagnostics.push(e.diagnostic());
            #[allow(clippy::expect_used)]
            Err(CompileError::Generic {
                ast: Box::new(ast),
                diagnostics,
                cost_tracker: Box::new(
                    contract_analysis
                        .cost_track
                        .take()
                        .expect("Failed to take cost tracker from contract analysis"),
                ),
            })
        }
    }
}

/// Why generating a Wasm module from an analyzed contract failed: see [`compile_contract`].
#[derive(Debug)]
pub enum ModuleGenerationError {
    /// Annotating or concretizing the contract's types failed.
    StaticCheck(StaticCheckError),
    /// Code generation failed.
    Generator(GeneratorError),
}

impl ModuleGenerationError {
    pub fn diagnostic(&self) -> Diagnostic {
        match self {
            ModuleGenerationError::StaticCheck(e) => e.diagnostic.clone(),
            ModuleGenerationError::Generator(e) => Diagnostic::err(e),
        }
    }

    pub fn message(&self) -> String {
        match self {
            ModuleGenerationError::StaticCheck(e) => e.to_string(),
            ModuleGenerationError::Generator(e) => {
                clarity::vm::diagnostic::DiagnosableError::message(e)
            }
        }
    }
}

impl std::fmt::Display for ModuleGenerationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message())
    }
}

impl std::error::Error for ModuleGenerationError {}

/// Compile an already-analyzed contract to a Wasm module, without cost instrumentation.
///
/// This runs the same post-analysis pipeline as [`compile`] -- Clarity 1 type-map annotation for
/// `contract-call?` arguments, concretization of the analysis types, then code generation -- so
/// that a caller which has already run the analysis (like the transaction deploy path) generates
/// exactly the same code as one compiling from source. `analysis_lookup` resolves the analyses
/// of the contracts this one refers to; the analysis passed in is consumed, and the annotation
/// and concretization it undergoes are not reflected back to the caller.
pub fn compile_contract(
    mut contract_analysis: ContractAnalysis,
    ast: &ContractAST,
    analysis_lookup: &mut dyn AnalysisLookup,
) -> Result<Module, ModuleGenerationError> {
    generate_module_from_analysis(&mut contract_analysis, ast, analysis_lookup, false)
}

/// The post-analysis compilation pipeline shared by every compile path: Clarity 1 type-map
/// annotation for `contract-call?` arguments, concretization of the analysis types, then Wasm
/// code generation. The annotation and concretization mutate `contract_analysis` in place.
fn generate_module_from_analysis(
    contract_analysis: &mut ContractAnalysis,
    ast: &ContractAST,
    analysis_lookup: &mut dyn AnalysisLookup,
    emit_cost_code: bool,
) -> Result<Module, ModuleGenerationError> {
    let epoch = contract_analysis.epoch;

    if contract_analysis.clarity_version == ClarityVersion::Clarity1 {
        annotate_types_for_contract_calls(contract_analysis, ast, analysis_lookup, epoch)
            .map_err(ModuleGenerationError::StaticCheck)?;
    }

    // Now that the typechecker pass is done, we can concretize the expressions types which
    // might contain `ListUnionType` or `CallableType`
    utils::concretize(contract_analysis).map_err(ModuleGenerationError::StaticCheck)?;

    let generator = match emit_cost_code {
        false => WasmGenerator::new(contract_analysis.clone()),
        true => WasmGenerator::with_cost_code(contract_analysis.clone()),
    };

    generator
        .and_then(WasmGenerator::generate)
        .map_err(ModuleGenerationError::Generator)
}

mod utils {
    use std::collections::{BTreeMap, HashMap};

    use clarity::types::StacksEpochId;
    use clarity::vm::analysis::ContractAnalysis;
    use clarity::vm::ast::ContractAST;
    use clarity::vm::errors::StaticCheckError;
    use clarity::vm::types::signatures::{FunctionReturnsSignature, FunctionSignature};
    use clarity::vm::types::{FixedFunction, FunctionType, QualifiedContractIdentifier};
    use clarity::vm::SymbolicExpression;
    use clarity_types::representations::TraitDefinition;
    use clarity_types::types::PrincipalData::Contract;
    use clarity_types::types::TypeSignature;
    use clarity_types::ClarityName;

    use crate::analysis_lookup::{self, AnalysisLookup};

    pub fn concretize(contract_analysis: &mut ContractAnalysis) -> Result<(), StaticCheckError> {
        // concretize Values types
        if let Some(mut typemap) = contract_analysis.type_map.take() {
            typemap.concretize()?;
            contract_analysis.type_map = Some(typemap);
        }

        // concretize constants
        for var_ty in contract_analysis.variable_types.values_mut() {
            *var_ty = var_ty.clone().concretize_deep()?;
        }

        // concretize private functions return types
        for fun_ty in contract_analysis.private_function_types.values_mut() {
            *fun_ty = concretize_function_return_type(fun_ty.clone())?;
        }

        // concretize public functions return types
        for fun_ty in contract_analysis.public_function_types.values_mut() {
            *fun_ty = concretize_function_return_type(fun_ty.clone())?;
        }

        // concretize read-only functions return types
        for fun_ty in contract_analysis.read_only_function_types.values_mut() {
            *fun_ty = concretize_function_return_type(fun_ty.clone())?;
        }

        Ok(())
    }

    fn concretize_function_return_type(ft: FunctionType) -> Result<FunctionType, StaticCheckError> {
        match ft {
            FunctionType::Variadic(args, return_type) => {
                Ok(FunctionType::Variadic(args, return_type.concretize_deep()?))
            }
            FunctionType::Fixed(FixedFunction { args, returns }) => {
                Ok(FunctionType::Fixed(FixedFunction {
                    args,
                    returns: returns.concretize_deep()?,
                }))
            }
            FunctionType::UnionArgs(args, ret_type) => {
                Ok(FunctionType::UnionArgs(args, ret_type.concretize_deep()?))
            }
            FunctionType::Binary(arg1, arg2, FunctionReturnsSignature::Fixed(return_type)) => {
                Ok(FunctionType::Binary(
                    arg1,
                    arg2,
                    FunctionReturnsSignature::Fixed(return_type.concretize_deep()?),
                ))
            }
            ft => Ok(ft),
        }
    }

    /// Walk the AST and, for every `contract-call?`, recover the callee's declared
    /// argument and return types from the analysis database and record them so they
    /// can be injected into the type map after analysis runs.
    ///
    /// `trait_args` maps an in-scope function argument name to the local alias of
    /// the trait it was declared with (e.g. `tt` -> `printer`), so that dynamic
    /// calls through a trait reference can be resolved too. See issue #819.
    ///
    /// `contract_identifier` and `defined_traits` describe the contract currently
    /// being compiled. A trait it defines itself is not in the analysis database
    /// yet, so it has to be resolved from the in-progress analysis instead.
    #[allow(clippy::too_many_arguments)]
    fn add_type_annotation_for_contracts(
        ast: &ContractAST,
        expr: &SymbolicExpression,
        analysis_lookup: &mut dyn AnalysisLookup,
        epoch: StacksEpochId,
        contract_identifier: &QualifiedContractIdentifier,
        defined_traits: &BTreeMap<ClarityName, BTreeMap<ClarityName, FunctionSignature>>,
        trait_args: &mut HashMap<ClarityName, ClarityName>,
    ) -> Result<Vec<(SymbolicExpression, TypeSignature)>, StaticCheckError> {
        let Some(list @ [first, rest @ ..]) = expr.match_list() else {
            return Ok(Vec::new());
        };

        // A `contract-call?` form: `(contract-call? <contract> <fn-name> <args...>)`
        if first.match_atom() == Some(&ClarityName::from_literal("contract-call?")) {
            let [contract_expr, function_expr, call_args @ ..] = rest else {
                return Ok(Vec::new());
            };
            let Some(function_name) = function_expr.match_atom() else {
                return Ok(Vec::new());
            };
            // Static call through a literal `.contract` principal.
            if let Some(literal) = contract_expr.match_literal_value() {
                if let Ok(Contract(contract)) = literal.clone().expect_principal() {
                    if let Some(FunctionType::Fixed(f)) = analysis_lookup::function_type(
                        analysis_lookup,
                        &contract,
                        function_name,
                        &epoch,
                    )? {
                        return Ok(call_args
                            .iter()
                            .zip(f.args.iter().map(|a| &a.signature))
                            .chain([(expr, &f.returns)])
                            .map(|(a, b)| (a.clone(), b.clone()))
                            .collect());
                    }
                }
            }
            // Dynamic call through a trait-typed argument, e.g. `(contract-call? tt ...)`.
            else if let Some(alias) = contract_expr.match_atom().and_then(|a| trait_args.get(a)) {
                if let Some(
                    TraitDefinition::Imported(trait_id) | TraitDefinition::Defined(trait_id),
                ) = ast.get_referenced_trait(alias)
                {
                    // A locally defined trait is not in the analysis database yet,
                    // so take it from the in-progress analysis instead.
                    let trait_signature = if trait_id.contract_identifier == *contract_identifier {
                        defined_traits.get(&trait_id.name).cloned()
                    } else {
                        analysis_lookup::defined_trait(
                            analysis_lookup,
                            &trait_id.contract_identifier,
                            &trait_id.name,
                            &epoch,
                        )?
                    };
                    if let Some(trait_signature) = trait_signature {
                        if let Some(function_signature) = trait_signature.get(function_name) {
                            return Ok(call_args
                                .iter()
                                .zip(&function_signature.args)
                                .chain([(expr, &function_signature.returns)])
                                .map(|(a, b)| (a.clone(), b.clone()))
                                .collect());
                        }
                    }
                }
            }
            return Ok(Vec::new());
        }

        // For a `define-*` form, collect any trait-typed arguments so that dynamic
        // `contract-call?`s in its body can be resolved, then recurse with them.
        if matches!(
            first.match_atom().map(ClarityName::as_str),
            Some("define-private" | "define-public" | "define-read-only")
        ) {
            if let Some(signature) = rest.first().and_then(|e| e.match_list()) {
                // signature = [fn-name, (arg-name arg-type)...]
                for arg in signature.iter().skip(1) {
                    if let Some([arg_name, arg_type]) = arg.match_list() {
                        if let (Some(name), Some(trait_ref)) =
                            (arg_name.match_atom(), arg_type.match_trait_reference())
                        {
                            trait_args.insert(name.clone(), trait_ref.clone());
                        }
                    }
                }
            }
        }

        list.iter()
            .map(|child| {
                add_type_annotation_for_contracts(
                    ast,
                    child,
                    analysis_lookup,
                    epoch,
                    contract_identifier,
                    defined_traits,
                    trait_args,
                )
            })
            .collect::<Result<Vec<_>, _>>()
            .map(|a| a.into_iter().flatten().collect())
    }

    /// The Clarity 1 typechecker does not fully annotate `contract-call?`
    /// arguments, so we recover their declared types up front and inject them after
    pub fn annotate_types_for_contract_calls(
        contract_analysis: &mut ContractAnalysis,
        ast: &ContractAST,
        analysis_lookup: &mut dyn AnalysisLookup,
        epoch: StacksEpochId,
    ) -> Result<(), StaticCheckError> {
        if let Some(type_map) = contract_analysis.type_map.as_mut() {
            let mut trait_args = HashMap::new();
            let types_to_add = ast
                .expressions
                .iter()
                .map(|expr| {
                    add_type_annotation_for_contracts(
                        ast,
                        expr,
                        analysis_lookup,
                        epoch,
                        &contract_analysis.contract_identifier,
                        &contract_analysis.defined_traits,
                        &mut trait_args,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?
                .into_iter()
                .flatten();

            for (expr, ty) in types_to_add {
                // We know that the type has already been set, that's why we change it in the first place.
                // Therefore we discard the TypeAlreadyAnnotatedFailure that would be produced here.
                let _ = type_map.set_type(&expr, ty);
            }
        }
        Ok(())
    }
}
