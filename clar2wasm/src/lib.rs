use clarity::types::StacksEpochId;
use clarity::vm::analysis::{run_analysis, AnalysisDatabase, ContractAnalysis};
use clarity::vm::ast::{build_ast_with_diagnostics, ContractAST};
use clarity::vm::costs::{ExecutionCost, LimitedCostTracker};
use clarity::vm::diagnostic::Diagnostic;
use clarity::vm::types::QualifiedContractIdentifier;
use clarity::vm::ClarityVersion;
pub use walrus::Module;
use wasm_generator::{GeneratorError, WasmGenerator};

mod cost;
pub use cost::{AccessCostMeter, CostGlobals, CostLinker, CostMeter};

mod deserialize;
pub mod initialize;
pub mod linker;
mod serialize;
pub mod wasm_generator;
pub mod wasm_utils;
mod words;

#[cfg(feature = "developer-mode")]
pub mod datastore;
#[cfg(feature = "developer-mode")]
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
    use clarity::vm::analysis::{CheckError, ContractAnalysis};
    use clarity::vm::errors::CheckErrors;
    use clarity::vm::types::signatures::FunctionReturnsSignature;
    use clarity::vm::types::{FixedFunction, FunctionType};

    pub fn concretize(contract_analysis: &mut ContractAnalysis) -> Result<(), CheckError> {
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

    fn concretize_function_return_type(ft: FunctionType) -> Result<FunctionType, CheckErrors> {
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
}
