//! # clar2wasm
//!
//! `clar2wasm` is a compiler for generating [WebAssembly](https://webassembly.org/) from
//! [Clarity](https://github.com/clarity-lang/reference) smart contract source code.
//!
//! ## Overview
//!
//! This crate provides the core compilation functionality to transform Clarity smart contracts
//! into WebAssembly modules that can be executed in a Wasm runtime environment. The compilation
//! process includes parsing, type analysis, and code generation phases.
//!
//! ## Module Organization
//!
//! - [`wasm_generator`] - Core WebAssembly code generation from Clarity AST
//! - [`wasm_utils`] - Utility functions for WebAssembly operations
//! - [`linker`] - WebAssembly linker for connecting host functions
//! - [`initialize`] - Module initialization utilities
//! - [`datastore`] - Data storage interface for contract state
//! - [`tools`] - Development and debugging tools
//! - [`duck_type`] - Dynamic type checking utilities
//!
//! ## Usage
//!
//! The primary entry point is the [`compile`] function:
//!
//! ```ignore
//! use clar2wasm::compile;
//!
//! let source = "(define-read-only (hello) \"world\")";
//! let result = compile(
//!     source,
//!     &contract_id,
//!     cost_tracker,
//!     clarity_version,
//!     epoch,
//!     &mut analysis_db,
//!     false,
//! );
//! ```
//!
//! ## Features
//!
//! - `developer-mode` - Enables test utilities for development
//! - `test-clarity-v1` through `test-clarity-v4` - Test with specific Clarity versions
//! - `flamegraph` - Enable flamegraph profiling for benchmarks
//! - `pb` - Enable protobuf output for benchmarks

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

pub mod datastore;
pub mod tools;

mod copy;
mod debug_msg;
pub mod duck_type;
mod error_mapping;

#[cfg(feature = "developer-mode")]
pub mod test_utils;

/// Block execution cost limits for Stacks 2.1 mainnet.
///
/// These constants define the maximum execution costs allowed per block:
/// - `write_length`: Maximum bytes written (15 MB)
/// - `write_count`: Maximum write operations (15,000)
/// - `read_length`: Maximum bytes read (100 MB)
/// - `read_count`: Maximum read operations (15,000)
/// - `runtime`: Maximum runtime cost units (5 billion)
// FIXME: This is copied from stacks-blockchain
// Block limit in Stacks 2.1
pub const BLOCK_LIMIT_MAINNET_21: ExecutionCost = ExecutionCost {
    write_length: 15_000_000,
    write_count: 15_000,
    read_length: 100_000_000,
    read_count: 15_000,
    runtime: 5_000_000_000,
};

/// The successful result of compiling a Clarity contract to WebAssembly.
///
/// Contains all artifacts produced during compilation, including the AST,
/// any diagnostics (warnings), the generated Wasm module, and the contract analysis.
#[derive(Debug)]
pub struct CompileResult {
    /// The abstract syntax tree of the parsed Clarity source code.
    pub ast: ContractAST,
    /// Any diagnostic messages (typically warnings) produced during compilation.
    pub diagnostics: Vec<Diagnostic>,
    /// The generated WebAssembly module.
    pub module: Module,
    /// The result of type analysis on the contract.
    pub contract_analysis: ContractAnalysis,
}

/// Error type returned when contract compilation fails.
///
/// Contains the partial compilation state at the point of failure,
/// which can be useful for error reporting and debugging.
#[derive(Debug)]
pub enum CompileError {
    /// A generic compilation error containing the AST, diagnostics, and cost tracker.
    Generic {
        /// The AST at the point of failure.
        ast: Box<ContractAST>,
        /// Diagnostic messages including the error that caused the failure.
        diagnostics: Vec<Diagnostic>,
        /// The cost tracker at the point of failure.
        cost_tracker: Box<LimitedCostTracker>,
    },
}

/// Compiles Clarity source code into a WebAssembly module.
///
/// This is the primary entry point for the compilation process. It performs:
/// 1. Parsing: Converts source code to an AST
/// 2. Analysis: Type checking and semantic analysis
/// 3. Concretization: Resolves union and callable types
/// 4. Code generation: Produces the WebAssembly module
///
/// # Arguments
///
/// * `source` - The Clarity source code to compile
/// * `contract_id` - The qualified contract identifier
/// * `cost_tracker` - Tracks execution costs during compilation
/// * `clarity_version` - The Clarity language version to use
/// * `epoch` - The Stacks epoch for compatibility
/// * `analysis_db` - Database for contract analysis
/// * `emit_cost_code` - Whether to include cost tracking code in output
///
/// # Returns
///
/// Returns `Ok(CompileResult)` on success, or `Err(CompileError)` if compilation fails.
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

/// Compiles a pre-analyzed contract directly to a WebAssembly module.
///
/// This is a lower-level function that skips parsing and analysis,
/// directly generating WebAssembly from an existing `ContractAnalysis`.
/// Useful when you have already performed analysis separately.
///
/// # Arguments
///
/// * `contract_analysis` - The pre-analyzed contract to compile
///
/// # Returns
///
/// Returns `Ok(Module)` containing the WebAssembly module, or
/// `Err(GeneratorError)` if code generation fails.
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
