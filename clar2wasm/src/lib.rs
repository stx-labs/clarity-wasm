use clarity::types::StacksEpochId;
use clarity::vm::analysis::{run_analysis, AnalysisDatabase, ContractAnalysis};
use clarity::vm::ast::{build_ast_with_diagnostics, ContractAST};
use clarity::vm::costs::{ExecutionCost, LimitedCostTracker};
use clarity::vm::diagnostic::Diagnostic;
use clarity::vm::types::QualifiedContractIdentifier;
use clarity::vm::ClarityVersion;
pub use walrus::Module;
use wasm_generator::{GeneratorError, WasmGenerator};

use crate::utils::annotate_types_for_contract_calls;

mod cost;

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

    if clarity_version == ClarityVersion::Clarity1 {
        if let Err(e) =
            annotate_types_for_contract_calls(&mut contract_analysis, &ast, analysis_db, epoch)
        {
            diagnostics.push(e.diagnostic);
            #[allow(clippy::expect_used)]
            return Err(CompileError::Generic {
                ast: Box::new(ast),
                diagnostics: diagnostics.clone(),
                cost_tracker: Box::new(
                    contract_analysis
                        .cost_track
                        .take()
                        .expect("Failed to take cost tracker from contract analysis"),
                ),
            });
        }
    }

    // Now that the typechecker pass is done, we can concretize the expressions types which
    // might contain `ListUnionType` or `CallableType`
    #[allow(clippy::expect_used)]
    if let Err(e) = utils::concretize(&mut contract_analysis) {
        diagnostics.push(e.diagnostic);
        return Err(CompileError::Generic {
            ast: Box::new(ast),
            diagnostics: diagnostics.clone(),
            cost_tracker: Box::new(
                contract_analysis
                    .cost_track
                    .take()
                    .expect("Failed to take cost tracker from contract analysis"),
            ),
        });
    }

    #[allow(clippy::expect_used)]
    let generator = match emit_cost_code {
        false => WasmGenerator::new(contract_analysis.clone()),
        true => WasmGenerator::with_cost_code(contract_analysis.clone()),
    };

    match generator.and_then(WasmGenerator::generate) {
        Ok(module) => Ok(CompileResult {
            ast,
            diagnostics,
            module,
            contract_analysis,
        }),
        Err(e) => {
            diagnostics.push(Diagnostic::err(&e));
            Err(CompileError::Generic {
                ast: Box::new(ast),
                diagnostics,
                #[allow(clippy::expect_used)]
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

pub fn compile_contract(contract_analysis: ContractAnalysis) -> Result<Module, GeneratorError> {
    let generator = WasmGenerator::new(contract_analysis)?;
    generator.generate()
}

mod utils {
    use std::collections::HashMap;

    use clarity::types::StacksEpochId;
    use clarity::vm::analysis::{AnalysisDatabase, ContractAnalysis};
    use clarity::vm::ast::ContractAST;
    use clarity::vm::errors::StaticCheckError;
    use clarity::vm::types::signatures::FunctionReturnsSignature;
    use clarity::vm::types::{FixedFunction, FunctionType};
    use clarity::vm::SymbolicExpression;
    use clarity_types::representations::TraitDefinition;
    use clarity_types::types::PrincipalData::Contract;
    use clarity_types::types::TypeSignature;
    use clarity_types::ClarityName;

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
    /// calls through a trait reference can be resolved too.
    /// See issue #819
    fn add_type_annotation_for_contracts(
        ast: &ContractAST,
        expr: &SymbolicExpression,
        analysis_db: &mut AnalysisDatabase,
        epoch: StacksEpochId,
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
                    if let Some(FunctionType::Fixed(f)) = analysis_db
                        .get_public_function_type(&contract, function_name, &epoch)?
                        .or(analysis_db.get_read_only_function_type(
                            &contract,
                            function_name,
                            &epoch,
                        )?)
                    {
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
                    if let Some(trait_signature) = analysis_db.get_defined_trait(
                        &trait_id.contract_identifier,
                        &trait_id.name,
                        &epoch,
                    )? {
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
                add_type_annotation_for_contracts(ast, child, analysis_db, epoch, trait_args)
            })
            .collect::<Result<Vec<_>, _>>()
            .map(|a| a.into_iter().flatten().collect())
    }

    /// The Clarity 1 typechecker does not fully annotate `contract-call?`
    /// arguments, so we recover their declared types up front and inject them after
    pub fn annotate_types_for_contract_calls(
        contract_analysis: &mut ContractAnalysis,
        ast: &ContractAST,
        analysis_db: &mut AnalysisDatabase,
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
                        analysis_db,
                        epoch,
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
