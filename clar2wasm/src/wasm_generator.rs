use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::ops::Deref;
use std::rc::Rc;

use clarity::vm::analysis::ContractAnalysis;
use clarity::vm::diagnostic::DiagnosableError;
use clarity::vm::types::signatures::{CallableSubtype, StringUTF8Length};
use clarity::vm::types::{
    ASCIIData, CharType, FixedFunction, FunctionType, ListTypeData, PrincipalData, SequenceData,
    SequenceSubtype, StringSubtype, TraitIdentifier, TupleTypeSignature, TypeSignature,
};
use clarity::vm::variables::NativeVariables;
use clarity::vm::{functions, variables, ClarityName, SymbolicExpression, SymbolicExpressionType};
use walrus::ir::{
    BinaryOp, IfElse, InstrSeqId, InstrSeqType, LoadKind, Loop, MemArg, StoreKind, UnaryOp,
};
use walrus::{
    ActiveData, DataKind, FunctionBuilder, FunctionId, GlobalId, InstrSeqBuilder, LocalId,
    MemoryId, Module, ValType,
};

use crate::cost::{ChargeContext, WordCharge};
use crate::error_mapping::ErrorMap;
use crate::wasm_utils::{
    check_argument_count, get_type_in_memory_size, get_type_size, signature_from_string,
    trait_identifier_as_bytes, ArgumentCountCheck, PRINCIPAL_BYTES_MAX,
};
use crate::{check_args, debug_msg, words};

// First free position after data directly defined in standard.wat
pub const END_OF_STANDARD_DATA: u32 = 1352;

/// WasmGenerator is a Clarity AST visitor that generates a WebAssembly module
/// as it traverses the AST.
pub struct WasmGenerator {
    /// The contract analysis, which contains the expressions and type
    /// information for the contract.
    pub(crate) contract_analysis: ContractAnalysis,
    /// The WebAssembly module that is being generated.
    pub(crate) module: Module,
    /// Offset of the end of the literal memory.
    pub(crate) literal_memory_end: u32,
    /// Global ID of the stack pointer.
    pub(crate) stack_pointer: GlobalId,
    /// Map strings saved in the literal memory to their offset.
    pub(crate) literal_memory_offset: HashMap<LiteralMemoryEntry, u32>,
    /// Map constants to an offset in the literal memory.
    pub(crate) constants: HashMap<String, TypeSignature>,
    /// The current function body block, used for early exit
    pub(crate) early_return_block_id: Option<InstrSeqId>,
    /// The type of the current function.
    pub(crate) current_function_type: Option<FixedFunction>,
    /// The types of defined data-vars
    pub(crate) datavars_types: HashMap<ClarityName, TypeSignature>,
    /// The types of (key, value) in defined maps
    pub(crate) maps_types: HashMap<ClarityName, (TypeSignature, TypeSignature)>,
    /// The type of defined NFTs
    pub(crate) nft_types: HashMap<ClarityName, TypeSignature>,
    /// The (offsets, lengths) of trait IDs
    pub(crate) used_traits: HashMap<TraitIdentifier, (u32, u32)>,
    /// The names of defined functions
    pub(crate) defined_functions: HashSet<String>,

    /// The locals for the current function.
    pub(crate) bindings: Bindings,

    /// Emits cost tracking code if set.
    pub(crate) cost_context: Option<ChargeContext>,

    /// Size of the current function's stack frame.
    frame_size: i32,
    /// Size of the maximum extra work space required by the stdlib functions
    /// to be available on the stack.
    max_work_space: u32,
    local_pool: Rc<RefCell<HashMap<ValType, Vec<LocalId>>>>,
}

#[derive(Debug, Clone, Default)]
pub(crate) struct Bindings(HashMap<ClarityName, InnerBindings>);

#[derive(Debug, Clone)]
struct InnerBindings {
    locals: Vec<LocalId>,
    ty: TypeSignature,
}

impl Bindings {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn insert(&mut self, name: ClarityName, ty: TypeSignature, locals: Vec<LocalId>) {
        self.0.insert(name, InnerBindings { locals, ty });
    }

    pub(crate) fn contains(&mut self, name: &ClarityName) -> bool {
        self.0.contains_key(name)
    }

    pub(crate) fn get_locals(&self, name: &ClarityName) -> Option<&[LocalId]> {
        self.0.get(name).map(|b| b.locals.as_slice())
    }

    pub(crate) fn get_trait_identifier(&self, name: &ClarityName) -> Option<&TraitIdentifier> {
        self.0.get(name).and_then(|b| match &b.ty {
            TypeSignature::CallableType(CallableSubtype::Trait(t)) => Some(t),
            _ => None,
        })
    }
}

#[derive(Hash, Eq, PartialEq)]
pub enum LiteralMemoryEntry {
    Ascii(String),
    Utf8(String),
    Bytes(Box<[u8]>),
}

#[derive(Debug)]
pub enum GeneratorError {
    NotImplemented,
    InternalError(String),
    TypeError(String),
    ArgumentCountMismatch,
}

pub enum FunctionKind {
    Public,
    Private,
    ReadOnly,
}

impl DiagnosableError for GeneratorError {
    fn message(&self) -> String {
        match self {
            GeneratorError::NotImplemented => "Not implemented".to_string(),
            GeneratorError::InternalError(msg) => format!("Internal error: {msg}"),
            GeneratorError::TypeError(msg) => format!("Type error: {msg}"),
            GeneratorError::ArgumentCountMismatch => "Argument count mismatch".to_string(),
        }
    }

    fn suggestion(&self) -> Option<String> {
        None
    }
}

pub trait ArgumentsExt {
    fn get_expr(&self, n: usize) -> Result<&SymbolicExpression, GeneratorError>;
    fn get_name(&self, n: usize) -> Result<&ClarityName, GeneratorError>;
    fn get_list(&self, n: usize) -> Result<&[SymbolicExpression], GeneratorError>;
}

impl ArgumentsExt for &[SymbolicExpression] {
    fn get_expr(&self, n: usize) -> Result<&SymbolicExpression, GeneratorError> {
        self.get(n).ok_or_else(|| {
            GeneratorError::InternalError(format!(
                "{self:?} does not have an argument of index {n}"
            ))
        })
    }

    fn get_name(&self, n: usize) -> Result<&ClarityName, GeneratorError> {
        self.get_expr(n)?.match_atom().ok_or_else(|| {
            GeneratorError::InternalError(format!(
                "{self:?} does not have a name at argument index {n}"
            ))
        })
    }

    fn get_list(&self, n: usize) -> Result<&[SymbolicExpression], GeneratorError> {
        self.get_expr(n)?.match_list().ok_or_else(|| {
            GeneratorError::InternalError(format!(
                "{self:?} does not have a list at argument index {n}"
            ))
        })
    }
}

/// Push a placeholder value for Wasm type `ty` onto the data stack.
/// `unreachable!` is used for Wasm types that should never be used.
#[allow(clippy::unreachable)]
pub(crate) fn add_placeholder_for_type(builder: &mut InstrSeqBuilder, ty: ValType) {
    match ty {
        ValType::I32 => builder.i32_const(0),
        ValType::I64 => builder.i64_const(0),
        ValType::F32 | ValType::F64 | ValType::V128 | ValType::Externref | ValType::Funcref => {
            unreachable!("Use of Wasm type {}", ty);
        }
    };
}

/// Push a placeholder value for Clarity type `ty` onto the data stack.
pub(crate) fn add_placeholder_for_clarity_type(builder: &mut InstrSeqBuilder, ty: &TypeSignature) {
    let wasm_types = clar2wasm_ty(ty);
    for wasm_type in wasm_types.iter() {
        add_placeholder_for_type(builder, *wasm_type);
    }
}

/// Convert a Clarity type signature to a wasm type signature.
pub(crate) fn clar2wasm_ty(ty: &TypeSignature) -> Vec<ValType> {
    match ty {
        TypeSignature::NoType => vec![ValType::I32], // TODO: can this just be empty?
        TypeSignature::IntType => vec![ValType::I64, ValType::I64],
        TypeSignature::UIntType => vec![ValType::I64, ValType::I64],
        TypeSignature::ResponseType(inner_types) => {
            let mut types = vec![ValType::I32];
            types.extend(clar2wasm_ty(&inner_types.0));
            types.extend(clar2wasm_ty(&inner_types.1));
            types
        }
        TypeSignature::SequenceType(_) | TypeSignature::ListUnionType(_) => vec![
            ValType::I32, // offset
            ValType::I32, // length
        ],
        TypeSignature::BoolType => vec![ValType::I32],
        TypeSignature::PrincipalType
        | TypeSignature::CallableType(_)
        | TypeSignature::TraitReferenceType(_) => vec![
            ValType::I32, // offset
            ValType::I32, // length
        ],
        TypeSignature::OptionalType(inner_ty) => {
            let mut types = vec![ValType::I32];
            types.extend(clar2wasm_ty(inner_ty));
            types
        }
        TypeSignature::TupleType(inner_types) => {
            let mut types = vec![];
            for inner_type in inner_types.get_type_map().values() {
                types.extend(clar2wasm_ty(inner_type));
            }
            types
        }
    }
}

#[derive(Debug)]
pub enum SequenceElementType {
    /// A byte, from a string-ascii or buffer.
    Byte,
    /// A 32-bit unicode scalar value, from a string-utf8.
    UnicodeScalar,
    /// Any other type.
    Other(TypeSignature),
}

/// Drop a value of type `ty` from the data stack.
pub(crate) fn drop_value(builder: &mut InstrSeqBuilder, ty: &TypeSignature) {
    let wasm_types = clar2wasm_ty(ty);
    (0..wasm_types.len()).for_each(|_| {
        builder.drop();
    });
}

pub fn type_from_sequence_element(se: &SequenceElementType) -> TypeSignature {
    match se {
        SequenceElementType::Other(o) => o.clone(),
        SequenceElementType::Byte => TypeSignature::BUFFER_1.clone(),
        SequenceElementType::UnicodeScalar => {
            TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(
                #[allow(clippy::unwrap_used)]
                StringUTF8Length::try_from(1u32).unwrap(),
            )))
        }
    }
}

pub fn get_global(module: &Module, name: &str) -> Result<GlobalId, GeneratorError> {
    module
        .globals
        .iter()
        .find(|global| {
            global
                .name
                .as_ref()
                .is_some_and(|other_name| name == other_name)
        })
        .map(|global| global.id())
        .ok_or_else(|| {
            GeneratorError::InternalError(format!("Expected to find a global named ${name}"))
        })
}

fn get_function(module: &Module, name: &str) -> Result<FunctionId, GeneratorError> {
    module.funcs.by_name(name).ok_or_else(|| {
        GeneratorError::InternalError(format!("Expected to find a function named ${name}"))
    })
}

pub(crate) struct BorrowedLocal {
    id: LocalId,
    ty: ValType,
    pool: Rc<RefCell<HashMap<ValType, Vec<LocalId>>>>,
}

impl Drop for BorrowedLocal {
    fn drop(&mut self) {
        match (*self.pool).borrow_mut().entry(self.ty) {
            Entry::Occupied(mut list) => list.get_mut().push(self.id),
            Entry::Vacant(e) => {
                e.insert(vec![self.id]);
            }
        }
    }
}

impl Deref for BorrowedLocal {
    type Target = LocalId;
    fn deref(&self) -> &Self::Target {
        &self.id
    }
}

impl WasmGenerator {
    pub fn new(contract_analysis: ContractAnalysis) -> Result<WasmGenerator, GeneratorError> {
        let standard_lib_wasm: &[u8] = include_bytes!("standard/standard.wasm");

        let module = Module::from_buffer(standard_lib_wasm).map_err(|_err| {
            GeneratorError::InternalError("failed to load standard library".to_owned())
        })?;
        // Get the stack-pointer global ID
        let global_id = get_global(&module, "stack-pointer")?;

        Ok(WasmGenerator {
            contract_analysis,
            module,
            literal_memory_end: END_OF_STANDARD_DATA,
            stack_pointer: global_id,
            literal_memory_offset: HashMap::new(),
            constants: HashMap::new(),
            bindings: Bindings::new(),
            cost_context: None,
            early_return_block_id: None,
            current_function_type: None,
            frame_size: 0,
            max_work_space: 0,
            datavars_types: HashMap::new(),
            maps_types: HashMap::new(),
            local_pool: Rc::new(RefCell::new(HashMap::new())),
            nft_types: HashMap::new(),
            used_traits: HashMap::new(),
            defined_functions: HashSet::new(),
        })
    }

    pub fn with_cost_code(contract_analysis: ContractAnalysis) -> Result<Self, GeneratorError> {
        let mut generator = Self::new(contract_analysis)?;
        generator.cost_context = Some(ChargeContext {
            clarity_version: generator.contract_analysis.clarity_version,
            runtime: get_global(&generator.module, "cost-runtime")?,
            read_count: get_global(&generator.module, "cost-read-count")?,
            read_length: get_global(&generator.module, "cost-read-length")?,
            write_count: get_global(&generator.module, "cost-write-count")?,
            write_length: get_global(&generator.module, "cost-write-length")?,
            runtime_error: get_function(&generator.module, "stdlib.runtime-error")?,
        });
        Ok(generator)
    }

    pub fn set_memory_pages(&mut self) -> Result<(), GeneratorError> {
        let memory = self
            .module
            .memories
            .iter_mut()
            .next()
            .ok_or_else(|| GeneratorError::InternalError("No Memory found".to_owned()))?;

        let total_memory_bytes =
            self.literal_memory_end + (self.frame_size as u32) + self.max_work_space;
        let pages_required = total_memory_bytes / (64 * 1024);
        let remainder = total_memory_bytes % (64 * 1024);

        memory.initial = pages_required + (remainder > 0) as u32;

        Ok(())
    }

    pub fn generate(mut self) -> Result<Module, GeneratorError> {
        let expressions = std::mem::take(&mut self.contract_analysis.expressions);

        if self.cost_context.is_some() {
            let module = &mut self.module;
            module.add_import_global("clarity", "cost-runtime", ValType::I64, true);
            module.add_import_global("clarity", "cost-read-count", ValType::I64, true);
            module.add_import_global("clarity", "cost-read-length", ValType::I64, true);
            module.add_import_global("clarity", "cost-write-count", ValType::I64, true);
            module.add_import_global("clarity", "cost-write-length", ValType::I64, true);
        }

        // Get the type of the last top-level expression with a return value
        // or default to `None`.
        let return_ty = expressions
            .iter()
            .rev()
            .find_map(|expr| self.get_expr_type(expr))
            .map_or_else(Vec::new, clar2wasm_ty);

        let mut current_function = FunctionBuilder::new(&mut self.module.types, &[], &return_ty);

        if !expressions.is_empty() {
            self.traverse_statement_list(&mut current_function.func_body(), &expressions)?;
        }

        self.contract_analysis.expressions = expressions;

        let top_level = current_function.finish(vec![], &mut self.module.funcs);
        self.module.exports.add(".top-level", top_level);

        self.set_memory_pages()?;

        // Update the initial value of the stack-pointer to point beyond the
        // literal memory.
        self.module.globals.get_mut(self.stack_pointer).kind = walrus::GlobalKind::Local(
            walrus::InitExpr::Value(walrus::ir::Value::I32(self.literal_memory_end as i32)),
        );

        Ok(self.module)
    }

    pub fn get_memory(&self) -> Result<MemoryId, GeneratorError> {
        Ok(self
            .module
            .memories
            .iter()
            .next()
            .ok_or(GeneratorError::InternalError("No memory found".to_owned()))?
            .id())
    }

    pub fn traverse_expr(
        &mut self,
        builder: &mut InstrSeqBuilder,
        expr: &SymbolicExpression,
    ) -> Result<(), GeneratorError> {
        match &expr.expr {
            SymbolicExpressionType::Atom(name) => self.visit_atom(builder, expr, name),
            SymbolicExpressionType::List(exprs) => self.traverse_list(builder, expr, exprs),
            SymbolicExpressionType::LiteralValue(value) => {
                self.visit_literal_value(builder, expr, value)
            }
            _ => Ok(()),
        }
    }

    fn traverse_list(
        &mut self,
        builder: &mut InstrSeqBuilder,
        expr: &SymbolicExpression,
        list: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        match list.split_first() {
            Some((
                SymbolicExpression {
                    expr: SymbolicExpressionType::Atom(function_name),
                    ..
                },
                args,
            )) => {
                // Extract the types from the args and return
                let get_types = || {
                    let arg_types: Result<Vec<TypeSignature>, GeneratorError> = args
                        .iter()
                        .map(|e| {
                            self.get_expr_type(e).cloned().ok_or_else(|| {
                                GeneratorError::TypeError("expected valid argument type".to_owned())
                            })
                        })
                        .collect();
                    let return_type = self
                        .get_expr_type(expr)
                        .ok_or_else(|| {
                            GeneratorError::TypeError("Simple words must be typed".to_owned())
                        })
                        .cloned();
                    Ok((arg_types?, return_type?))
                };

                // Complex words handle their own argument traversal, and have priority
                // since we need to have a slight overlap for the words `and` and `or`
                // which exist in both complex and simple forms
                if let Some(word) = words::lookup_complex(function_name) {
                    word.traverse(self, builder, expr, args)?;
                } else if let Some(simpleword) = words::lookup_simple(function_name) {
                    let (arg_types, return_type) = get_types()?;

                    // traverse arguments
                    for arg in args {
                        self.traverse_expr(builder, arg)?;
                    }

                    simpleword.visit(self, builder, &arg_types, &return_type)?;
                } else if let Some(variadic) = words::lookup_variadic_simple(function_name) {
                    let (arg_types, return_type) = get_types()?;

                    variadic.charge(self, builder, arg_types.len() as u32)?;

                    let mut args_enumerated = args.iter().enumerate();

                    let first_arg = args_enumerated
                        .next()
                        .ok_or_else(|| {
                            GeneratorError::InternalError(
                                "Variadic called without arguments".to_owned(),
                            )
                        })?
                        .1;

                    self.traverse_expr(builder, first_arg)?;

                    if arg_types.len() == 1 {
                        variadic.visit(self, builder, &arg_types[..1], &return_type)?;
                    } else {
                        for (i, expr) in args_enumerated {
                            self.traverse_expr(builder, expr)?;
                            variadic.visit(self, builder, &arg_types[i - 1..=i], &return_type)?;
                        }
                    }

                    // first argument is traversed outside loop
                } else {
                    self.traverse_call_user_defined(builder, expr, function_name, args)?;
                }
            }
            _ => return Err(GeneratorError::InternalError("Invalid list".into())),
        }
        Ok(())
    }

    pub fn traverse_define_function(
        &mut self,
        builder: &mut InstrSeqBuilder,
        name: &ClarityName,
        body: &SymbolicExpression,
        kind: FunctionKind,
    ) -> Result<FunctionId, GeneratorError> {
        let opt_function_type = match kind {
            FunctionKind::ReadOnly => {
                builder.i32_const(0);
                self.contract_analysis
                    .get_read_only_function_type(name.as_str())
            }
            FunctionKind::Public => {
                builder.i32_const(1);
                self.contract_analysis
                    .get_public_function_type(name.as_str())
            }
            FunctionKind::Private => {
                builder.i32_const(2);
                self.contract_analysis.get_private_function(name.as_str())
            }
        };
        let function_type = if let Some(FunctionType::Fixed(fixed)) = opt_function_type {
            fixed.clone()
        } else {
            return Err(GeneratorError::TypeError(match opt_function_type {
                Some(_) => "expected fixed function type".to_string(),
                None => format!("unable to find function type for {}", name.as_str()),
            }));
        };

        self.current_function_type = Some(function_type.clone());

        // Call the host interface to save this function
        // Arguments are kind (already pushed) and name (offset, length)
        let (id_offset, id_length) = self.add_string_literal(name)?;
        builder
            .i32_const(id_offset as i32)
            .i32_const(id_length as i32);

        // Call the host interface function, `define_function`
        builder.call(self.func_by_name("stdlib.define_function"));

        let mut bindings = Bindings::new();

        // Setup the parameters
        let mut param_locals = Vec::new();
        let mut params_types = Vec::new();
        let mut reused_arg = None;
        for param in function_type.args.iter() {
            // Interpreter returns the first reused arg as NameAlreadyUsed argument
            if reused_arg.is_none() && bindings.contains(&param.name) {
                reused_arg = Some(param.name.clone());
            }

            let param_types = clar2wasm_ty(&param.signature);
            let mut plocals = Vec::with_capacity(param_types.len());
            for ty in param_types {
                let local = self.module.locals.add(ty);
                param_locals.push(local);
                plocals.push(local);
                params_types.push(ty);
            }
            bindings.insert(param.name.clone(), param.signature.clone(), plocals);
        }

        let results_types = clar2wasm_ty(&function_type.returns);
        let mut func_builder = FunctionBuilder::new(
            &mut self.module.types,
            params_types.as_slice(),
            results_types.as_slice(),
        );
        func_builder.name(name.as_str().to_string());
        let mut func_body = func_builder.func_body();

        // Function prelude
        // Save the frame pointer in a local variable.
        let frame_pointer = self.module.locals.add(ValType::I32);
        func_body
            .global_get(self.stack_pointer)
            .local_set(frame_pointer);

        // Setup the locals map for this function, saving the top-level map to
        // restore after.
        let top_level_locals = std::mem::replace(&mut self.bindings, bindings);

        let mut block = func_body.dangling_instr_seq(InstrSeqType::new(
            &mut self.module.types,
            &[],
            results_types.as_slice(),
        ));
        let block_id = block.id();

        self.early_return_block_id = Some(block_id);

        // Traverse the body of the function
        self.set_expr_type(body, function_type.returns.clone())?;
        self.traverse_expr(&mut block, body)?;

        // If the same arg name is used multiple times, the interpreter throws an
        // `Unchecked` error at runtime, so we do the same here
        if let Some(arg_name) = reused_arg {
            let (arg_name_offset, arg_name_len) =
                self.add_clarity_string_literal(&CharType::ASCII(ASCIIData {
                    data: arg_name.as_bytes().to_vec(),
                }))?;

            // Clear function body
            block.instrs_mut().clear();

            block
                .i32_const(arg_name_offset as i32)
                .global_set(get_global(&self.module, "runtime-error-arg-offset")?)
                .i32_const(arg_name_len as i32)
                .global_set(get_global(&self.module, "runtime-error-arg-len")?)
                .i32_const(ErrorMap::NameAlreadyUsed as i32)
                .call(self.func_by_name("stdlib.runtime-error"))
                // To avoid having to generate correct return values
                .unreachable();
        }

        // Insert the function body block into the function
        func_body.instr(walrus::ir::Block { seq: block_id });

        // Function postlude
        // Restore the initial stack pointer.
        func_body
            .local_get(frame_pointer)
            .global_set(self.stack_pointer);

        // Restore the top-level locals map.
        self.bindings = top_level_locals;

        // Reset the return type and early block to None
        self.current_function_type = None;
        self.early_return_block_id = None;

        Ok(func_builder.finish(param_locals, &mut self.module.funcs))
    }

    /// Generates the wasm code for a ShortReturn error.
    ///
    /// It takes for the `runtime_error`
    /// argument either a [ErrorMap::ShortReturnAssertionFailure], a
    /// [ErrorMap::ShortReturnExpectedValue], a [ErrorMap::ShortReturnExpectedValueResponse]
    /// or a [ErrorMap::ShortReturnExpectedValueOptional].
    pub(crate) fn short_return_error(
        &mut self,
        builder: &mut InstrSeqBuilder,
        ty: &TypeSignature,
        runtime_error: ErrorMap,
    ) -> Result<(), GeneratorError> {
        match runtime_error {
            ErrorMap::ShortReturnAssertionFailure
            | ErrorMap::ShortReturnExpectedValue
            | ErrorMap::ShortReturnExpectedValueResponse => {
                let (val_offset, _) = self.create_call_stack_local(builder, ty, false, true);
                self.write_to_memory(builder, val_offset, 0, ty)?;

                let serialized_ty = self.type_for_serialization(ty).to_string();

                // Validate serialized type
                signature_from_string(
                    &serialized_ty,
                    self.contract_analysis.clarity_version,
                    self.contract_analysis.epoch,
                )
                .map_err(|e| {
                    GeneratorError::TypeError(format!("type cannot be deserialized: {e:?}"))
                })?;

                let (type_ser_offset, type_ser_len) =
                    self.add_clarity_string_literal(&CharType::ASCII(ASCIIData {
                        data: serialized_ty.into_bytes(),
                    }))?;

                // Set runtime error globals
                builder
                    .local_get(val_offset)
                    .global_set(get_global(&self.module, "runtime-error-value-offset")?)
                    .i32_const(type_ser_offset as i32)
                    .global_set(get_global(&self.module, "runtime-error-type-ser-offset")?)
                    .i32_const(type_ser_len as i32)
                    .global_set(get_global(&self.module, "runtime-error-type-ser-len")?)
                    .i32_const(runtime_error as i32)
                    .call(self.func_by_name("stdlib.runtime-error"));
            }
            ErrorMap::ShortReturnExpectedValueOptional => {
                // Simple case: just call runtime error
                builder
                    .i32_const(runtime_error as i32)
                    .call(self.func_by_name("stdlib.runtime-error"));
            }
            _ => {
                return Err(GeneratorError::InternalError(
                    "Unhandled runtime error for try! function".to_owned(),
                ))
            }
        }

        builder.unreachable();

        Ok(())
    }

    /// Try to change `ty` for serialization/deserialization (as stringified signature)
    /// In case of failure, clones the input `ty`
    #[allow(clippy::only_used_in_recursion)]
    pub fn type_for_serialization(&self, ty: &TypeSignature) -> TypeSignature {
        use clarity::vm::types::signatures::TypeSignature::*;
        match ty {
            // NoType and BoolType have the same size (both type and inner)
            NoType => BoolType,
            // Avoid serialization like `(list 2 <S1G2081040G2081040G2081040G208105NK8PE5.my-trait.my-trait>)`
            CallableType(CallableSubtype::Trait(_)) => PrincipalType,
            // Recursive types
            ResponseType(types) => ResponseType(Box::new((
                self.type_for_serialization(&types.0),
                self.type_for_serialization(&types.1),
            ))),
            OptionalType(value_ty) => OptionalType(Box::new(self.type_for_serialization(value_ty))),
            SequenceType(SequenceSubtype::ListType(list_ty)) => {
                SequenceType(SequenceSubtype::ListType(
                    ListTypeData::new_list(
                        self.type_for_serialization(list_ty.get_list_item_type()),
                        list_ty.get_max_len(),
                    )
                    .unwrap_or_else(|_| list_ty.clone()),
                ))
            }
            TupleType(tuple_ty) => TupleType(
                TupleTypeSignature::try_from(
                    tuple_ty
                        .get_type_map()
                        .iter()
                        .map(|(k, v)| (k.clone(), self.type_for_serialization(v)))
                        .collect::<Vec<_>>(),
                )
                .unwrap_or_else(|_| tuple_ty.clone()),
            ),
            t => t.clone(),
        }
    }

    /// Gets the result type of the given `SymbolicExpression`.
    pub fn get_expr_type(&self, expr: &SymbolicExpression) -> Option<&TypeSignature> {
        self.contract_analysis
            .type_map
            .as_ref()
            .and_then(|ty| ty.get_type_expected(expr))
    }

    /// Sets the result type of the given `SymbolicExpression`. This is
    /// necessary to overcome some weaknesses in the type-checker and
    /// hopefully can be removed in the future.
    pub fn set_expr_type(
        &mut self,
        expr: &SymbolicExpression,
        ty: TypeSignature,
    ) -> Result<(), GeneratorError> {
        // Safely ignore the error because we know this type has already been set.
        let _ = self
            .contract_analysis
            .type_map
            .as_mut()
            .ok_or_else(|| {
                GeneratorError::InternalError(
                    "type-checker must be called before Wasm generation".to_owned(),
                )
            })?
            .set_type(expr, ty);
        Ok(())
    }

    /// Adds a new string literal into the memory, and returns the offset and length.
    pub(crate) fn add_clarity_string_literal(
        &mut self,
        s: &CharType,
    ) -> Result<(u32, u32), GeneratorError> {
        // If this string has already been saved in the literal memory,
        // just return the offset and length.
        let (data, entry) = match s {
            CharType::ASCII(s) => {
                let entry = LiteralMemoryEntry::Ascii(s.to_string());
                if let Some(offset) = self.literal_memory_offset.get(&entry) {
                    return Ok((*offset, s.data.len() as u32));
                }
                (s.data.clone(), entry)
            }
            CharType::UTF8(u) => {
                let data_str = String::from_utf8(u.data.iter().flatten().cloned().collect())
                    .map_err(|_e| {
                        GeneratorError::InternalError("Invalid UTF-8 sequence".to_owned())
                    })?;
                let entry = LiteralMemoryEntry::Utf8(data_str.clone());
                if let Some(offset) = self.literal_memory_offset.get(&entry) {
                    return Ok((*offset, u.data.len() as u32 * 4));
                }
                // Convert the string into 4-byte big-endian unicode scalar values.
                let data = data_str
                    .chars()
                    .flat_map(|c| (c as u32).to_be_bytes())
                    .collect();
                (data, entry)
            }
        };
        let memory = self.get_memory()?;
        let offset = self.literal_memory_end;
        let len = data.len() as u32;
        self.module.data.add(
            DataKind::Active(ActiveData {
                memory,
                location: walrus::ActiveDataLocation::Absolute(offset),
            }),
            data,
        );
        self.literal_memory_end += len;

        // Save the offset in the literal memory for this string
        self.literal_memory_offset.insert(entry, offset);

        Ok((offset, len))
    }

    /// Adds a new string literal into the memory for an identifier
    pub(crate) fn add_string_literal(&mut self, name: &str) -> Result<(u32, u32), GeneratorError> {
        // If this identifier has already been saved in the literal memory,
        // just return the offset and length.
        let entry = LiteralMemoryEntry::Ascii(name.to_string());
        if let Some(offset) = self.literal_memory_offset.get(&entry) {
            return Ok((*offset, name.len() as u32));
        }

        let memory = self.get_memory()?;
        let offset = self.literal_memory_end;
        let len = name.len() as u32;
        self.module.data.add(
            DataKind::Active(ActiveData {
                memory,
                location: walrus::ActiveDataLocation::Absolute(offset),
            }),
            name.as_bytes().to_vec(),
        );
        self.literal_memory_end += name.len() as u32;

        // Save the offset in the literal memory for this identifier
        self.literal_memory_offset.insert(entry, offset);

        Ok((offset, len))
    }

    pub(crate) fn add_bytes_literal(&mut self, bytes: &[u8]) -> Result<(u32, u32), GeneratorError> {
        let entry = LiteralMemoryEntry::Bytes(bytes.into());
        if let Some(offset) = self.literal_memory_offset.get(&entry) {
            return Ok((*offset, bytes.len() as u32));
        }

        let memory = self.get_memory()?;
        let offset = self.literal_memory_end;
        let len = bytes.len() as u32;
        self.module.data.add(
            DataKind::Active(ActiveData {
                memory,
                location: walrus::ActiveDataLocation::Absolute(offset),
            }),
            bytes.to_vec(),
        );
        self.literal_memory_end += len;

        self.literal_memory_offset.insert(entry, offset);

        Ok((offset, len))
    }

    /// Adds a serialized [TraitIdentifier] to the wasm memory.
    /// Returns the offset and length of the bytes written.
    pub(crate) fn add_trait_identifier(
        &mut self,
        trait_id: &TraitIdentifier,
    ) -> Result<(u32, u32), GeneratorError> {
        self.add_bytes_literal(&trait_identifier_as_bytes(trait_id))
    }

    /// Adds a new literal into the memory, and returns the offset and length.
    pub(crate) fn add_literal(
        &mut self,
        value: &clarity::vm::Value,
    ) -> Result<(u32, u32), GeneratorError> {
        let data = match value {
            clarity::vm::Value::Int(i) => {
                let mut data = (((*i as u128) & 0xFFFFFFFFFFFFFFFF) as i64)
                    .to_le_bytes()
                    .to_vec();
                data.extend_from_slice(&(((*i as u128) >> 64) as i64).to_le_bytes());
                data
            }
            clarity::vm::Value::UInt(u) => {
                let mut data = ((*u & 0xFFFFFFFFFFFFFFFF) as i64).to_le_bytes().to_vec();
                data.extend_from_slice(&((*u >> 64) as i64).to_le_bytes());
                data
            }
            clarity::vm::Value::Principal(p) => match p {
                PrincipalData::Standard(standard) => {
                    let mut data = vec![standard.version()];
                    data.extend_from_slice(&standard.1);
                    // Append a 0 for the length of the contract name
                    data.push(0);
                    data
                }
                PrincipalData::Contract(contract) => {
                    let mut data = vec![contract.issuer.version()];
                    data.extend_from_slice(&contract.issuer.1);
                    let contract_length = contract.name.len();
                    data.push(contract_length);
                    data.extend_from_slice(contract.name.as_bytes());
                    data
                }
            },
            clarity::vm::Value::Sequence(SequenceData::Buffer(buff_data)) => buff_data.data.clone(),
            clarity::vm::Value::Sequence(SequenceData::String(string_data)) => {
                return self.add_clarity_string_literal(string_data);
            }
            clarity::vm::Value::Bool(_)
            | clarity::vm::Value::Tuple(_)
            | clarity::vm::Value::Optional(_)
            | clarity::vm::Value::Response(_)
            | clarity::vm::Value::CallableContract(_)
            | clarity::vm::Value::Sequence(_) => {
                return Err(GeneratorError::TypeError(format!(
                    "Not a valid literal type: {value:?}"
                )))
            }
        };
        let memory = self.get_memory()?;
        let offset = self.literal_memory_end;
        let len = data.len() as u32;
        self.module.data.add(
            DataKind::Active(ActiveData {
                memory,
                location: walrus::ActiveDataLocation::Absolute(offset),
            }),
            data.clone(),
        );
        self.literal_memory_end += data.len() as u32;

        Ok((offset, len))
    }

    pub(crate) fn block_from_expr(
        &mut self,
        builder: &mut InstrSeqBuilder,
        expr: &SymbolicExpression,
    ) -> Result<InstrSeqId, GeneratorError> {
        let return_type = clar2wasm_ty(self.get_expr_type(expr).ok_or_else(|| {
            GeneratorError::TypeError("Expression results must be typed".to_owned())
        })?);

        let mut block = builder.dangling_instr_seq(InstrSeqType::new(
            &mut self.module.types,
            &[],
            &return_type,
        ));
        self.traverse_expr(&mut block, expr)?;

        Ok(block.id())
    }

    /// Push a new local onto the call stack, adjusting the stack pointer and
    /// tracking the current function's frame size accordingly.
    /// - `include_repr` indicates if space should be reserved for the
    ///   representation of the value (e.g. the offset, length for an in-memory
    ///   type)
    /// - `include_value` indicates if space should be reserved for the value
    ///
    /// Returns a local which is a pointer to the beginning of the allocated
    /// stack space and the size of the allocated space.
    pub(crate) fn create_call_stack_local(
        &mut self,
        builder: &mut InstrSeqBuilder,
        ty: &TypeSignature,
        include_repr: bool,
        include_value: bool,
    ) -> (LocalId, i32) {
        let size = match (include_value, include_repr) {
            (true, true) => get_type_in_memory_size(ty, include_repr) + get_type_size(ty),
            (true, false) => get_type_in_memory_size(ty, include_repr),
            (false, true) => get_type_size(ty),
            (false, false) => unreachable!("must include either repr or value"),
        };

        // Save the offset (current stack pointer) into a local
        let offset = self.module.locals.add(ValType::I32);
        builder
            // []
            .global_get(self.stack_pointer)
            // [ stack_ptr ]
            .local_tee(offset);
        // [ stack_ptr ]

        // TODO: The frame stack size can be computed at compile time, so we
        //       should be able to increment the stack pointer once in the function
        //       prelude with a constant instead of incrementing it for each local.
        // (global.set $stack-pointer (i32.add (global.get $stack-pointer) (i32.const <size>))
        builder
            // [ stack_ptr ]
            .i32_const(size)
            // [ stack_ptr, size ]
            .binop(BinaryOp::I32Add)
            // [ new_stack_ptr ]
            .global_set(self.stack_pointer);
        // [  ]
        self.frame_size += size;

        (offset, size)
    }

    pub(crate) fn borrow_local(&mut self, ty: ValType) -> BorrowedLocal {
        let reuse = (*self.local_pool)
            .borrow_mut()
            .get_mut(&ty)
            .and_then(Vec::pop);
        BorrowedLocal {
            id: reuse.unwrap_or_else(|| self.module.locals.add(ty)),
            ty,
            pool: self.local_pool.clone(),
        }
    }

    /// Write the value that is on the top of the data stack, which has type
    /// `ty`, to the memory, at offset stored in local variable,
    /// `offset_local`, plus constant offset `offset`. Returns the number of
    /// bytes written.
    pub(crate) fn write_to_memory(
        &mut self,
        builder: &mut InstrSeqBuilder,
        offset_local: LocalId,
        offset: u32,
        ty: &TypeSignature,
    ) -> Result<u32, GeneratorError> {
        let memory = self.get_memory()?;
        match ty {
            TypeSignature::IntType | TypeSignature::UIntType => {
                // Data stack: TOP | High | Low | ...
                // Save the high/low to locals.
                let high = self.borrow_local(ValType::I64);
                let low = self.borrow_local(ValType::I64);
                builder.local_set(*high).local_set(*low);

                // Store the high/low to memory.
                builder.local_get(offset_local).local_get(*low).store(
                    memory,
                    StoreKind::I64 { atomic: false },
                    MemArg { align: 8, offset },
                );
                builder.local_get(offset_local).local_get(*high).store(
                    memory,
                    StoreKind::I64 { atomic: false },
                    MemArg {
                        align: 8,
                        offset: offset + 8,
                    },
                );
                Ok(16)
            }
            TypeSignature::PrincipalType
            | TypeSignature::CallableType(_)
            | TypeSignature::TraitReferenceType(_)
            | TypeSignature::SequenceType(_) => {
                // Data stack: TOP | Length | Offset | ...
                // Save the offset/length to locals.
                let seq_offset = self.module.locals.add(ValType::I32);
                let seq_length = self.module.locals.add(ValType::I32);
                builder.local_set(seq_length).local_set(seq_offset);

                // Store the offset/length to memory.
                builder.local_get(offset_local).local_get(seq_offset).store(
                    memory,
                    StoreKind::I32 { atomic: false },
                    MemArg { align: 4, offset },
                );
                builder.local_get(offset_local).local_get(seq_length).store(
                    memory,
                    StoreKind::I32 { atomic: false },
                    MemArg {
                        align: 4,
                        offset: offset + 4,
                    },
                );
                Ok(8)
            }
            TypeSignature::BoolType => {
                // Data stack: TOP | Value | ...
                // Save the value to a local.
                let bool_val = self.module.locals.add(ValType::I32);
                builder.local_set(bool_val);

                // Store the value to memory.
                builder.local_get(offset_local).local_get(bool_val).store(
                    memory,
                    StoreKind::I32 { atomic: false },
                    MemArg { align: 4, offset },
                );
                Ok(4)
            }
            TypeSignature::NoType => {
                // Data stack: TOP | (Place holder i32)
                // We just have to drop the placeholder and write a i32
                builder.drop().local_get(offset_local).i32_const(0).store(
                    memory,
                    StoreKind::I32 { atomic: false },
                    MemArg { align: 4, offset },
                );
                Ok(4)
            }
            TypeSignature::OptionalType(some_ty) => {
                // Data stack: TOP | inner value | (some|none) variant
                // recursively store the inner value

                let bytes_written =
                    self.write_to_memory(builder, offset_local, offset + 4, some_ty)?;

                // Save the variant to a local and store it to memory
                let variant_val = self.module.locals.add(ValType::I32);
                builder
                    .local_set(variant_val)
                    .local_get(offset_local)
                    .local_get(variant_val)
                    .store(
                        memory,
                        StoreKind::I32 { atomic: false },
                        MemArg { align: 4, offset },
                    );

                // recursively store the inner value
                Ok(4 + bytes_written)
            }
            TypeSignature::ResponseType(ok_err_ty) => {
                // Data stack: TOP | err_value | ok_value | (ok|err) variant
                let mut bytes_written = 0;

                // write err value at offset + size of variant (4) + size of ok_value
                bytes_written += self.write_to_memory(
                    builder,
                    offset_local,
                    offset + 4 + get_type_size(&ok_err_ty.0) as u32,
                    &ok_err_ty.1,
                )?;

                // write ok value at offset + size of variant (4)
                bytes_written +=
                    self.write_to_memory(builder, offset_local, offset + 4, &ok_err_ty.0)?;

                let variant_val = self.module.locals.add(ValType::I32);
                builder
                    .local_set(variant_val)
                    .local_get(offset_local)
                    .local_get(variant_val)
                    .store(
                        memory,
                        StoreKind::I32 { atomic: false },
                        MemArg { align: 4, offset },
                    );

                Ok(bytes_written + 4)
            }
            TypeSignature::TupleType(tuple_ty) => {
                // Data stack: TOP | last_value | value_before_last | ... | first_value
                // we will write the values from last to first by setting the correct offset at which it's supposed to be written
                let mut bytes_written = 0;
                let types: Vec<_> = tuple_ty.get_type_map().values().cloned().collect();
                let offsets_delta: Vec<_> = std::iter::once(0u32)
                    .chain(
                        types
                            .iter()
                            .map(|t| get_type_size(t) as u32)
                            .scan(0, |acc, i| {
                                *acc += i;
                                Some(*acc)
                            }),
                    )
                    .collect();
                for (elem_ty, offset_delta) in types.into_iter().zip(offsets_delta).rev() {
                    bytes_written += self.write_to_memory(
                        builder,
                        offset_local,
                        offset + offset_delta,
                        &elem_ty,
                    )?;
                }
                Ok(bytes_written)
            }
            TypeSignature::ListUnionType(_) => Err(GeneratorError::TypeError(
                "Not a valid value type: ListUnionType".to_owned(),
            ))?,
        }
    }

    /// Read a value from memory at offset stored in local variable `offset`,
    /// with type `ty`, and push it onto the top of the data stack.
    pub(crate) fn read_from_memory(
        &mut self,
        builder: &mut InstrSeqBuilder,
        offset: LocalId,
        literal_offset: u32,
        ty: &TypeSignature,
    ) -> Result<i32, GeneratorError> {
        let memory = self
            .module
            .memories
            .iter()
            .next()
            .ok_or_else(|| GeneratorError::InternalError("No memory found".to_owned()))?;
        match ty {
            TypeSignature::IntType | TypeSignature::UIntType => {
                // Memory: Offset -> | Low | High |
                builder.local_get(offset).load(
                    memory.id(),
                    LoadKind::I64 { atomic: false },
                    MemArg {
                        align: 8,
                        offset: literal_offset,
                    },
                );
                builder.local_get(offset).load(
                    memory.id(),
                    LoadKind::I64 { atomic: false },
                    MemArg {
                        align: 8,
                        offset: literal_offset + 8,
                    },
                );
                Ok(16)
            }
            TypeSignature::OptionalType(inner) => {
                // Memory: Offset -> | Indicator | Value |
                builder.local_get(offset).load(
                    memory.id(),
                    LoadKind::I32 { atomic: false },
                    MemArg {
                        align: 4,
                        offset: literal_offset,
                    },
                );
                Ok(4 + self.read_from_memory(builder, offset, literal_offset + 4, inner)?)
            }
            TypeSignature::ResponseType(inner) => {
                // Memory: Offset -> | Indicator | Ok Value | Err Value |
                builder.local_get(offset).load(
                    memory.id(),
                    LoadKind::I32 { atomic: false },
                    MemArg {
                        align: 4,
                        offset: literal_offset,
                    },
                );
                let mut offset_adjust = 4;
                offset_adjust += self.read_from_memory(
                    builder,
                    offset,
                    literal_offset + offset_adjust,
                    &inner.0,
                )? as u32;
                offset_adjust += self.read_from_memory(
                    builder,
                    offset,
                    literal_offset + offset_adjust,
                    &inner.1,
                )? as u32;
                Ok(offset_adjust as i32)
            }
            // Principals and sequence types are stored in-memory and
            // represented by an offset and length.
            TypeSignature::PrincipalType
            | TypeSignature::CallableType(_)
            | TypeSignature::TraitReferenceType(_)
            | TypeSignature::SequenceType(_) => {
                // Memory: Offset -> | ValueOffset | ValueLength |
                builder.local_get(offset).load(
                    memory.id(),
                    LoadKind::I32 { atomic: false },
                    MemArg {
                        align: 4,
                        offset: literal_offset,
                    },
                );
                builder.local_get(offset).load(
                    memory.id(),
                    LoadKind::I32 { atomic: false },
                    MemArg {
                        align: 4,
                        offset: literal_offset + 4,
                    },
                );
                Ok(8)
            }
            TypeSignature::TupleType(tuple) => {
                // Memory: Offset -> | Value1 | Value2 | ... |
                let mut offset_adjust = 0;
                for ty in tuple.get_type_map().values() {
                    offset_adjust +=
                        self.read_from_memory(builder, offset, literal_offset + offset_adjust, ty)?
                            as u32;
                }
                Ok(offset_adjust as i32)
            }
            // Unknown types just get a placeholder i32 value.
            TypeSignature::NoType => {
                builder.i32_const(0);
                Ok(4)
            }
            TypeSignature::BoolType => {
                builder.local_get(offset).load(
                    memory.id(),
                    LoadKind::I32 { atomic: false },
                    MemArg {
                        align: 4,
                        offset: literal_offset,
                    },
                );
                Ok(4)
            }
            TypeSignature::ListUnionType(_) => Err(GeneratorError::TypeError(
                "Not a valid value type: ListUnionType".to_owned(),
            ))?,
        }
    }

    pub(crate) fn traverse_statement_list(
        &mut self,
        builder: &mut InstrSeqBuilder,
        statements: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        if statements.is_empty() {
            return Err(GeneratorError::InternalError(
                "statement list must have at least one statement".to_owned(),
            ));
        }

        let mut last_ty = None;
        // Traverse the statements, saving the last non-none value.
        for stmt in statements {
            // If stmt has a type, save that type. If there was a previous type
            // saved, then drop that value.
            if let Some(ty) = self.get_expr_type(stmt) {
                if let Some(last_ty) = &last_ty {
                    drop_value(builder, last_ty);
                }
                last_ty = Some(ty.clone());
            }
            self.traverse_expr(builder, stmt)?;
        }

        Ok(())
    }

    /// If `name` is a reserved variable, push its value onto the data stack.
    pub fn lookup_reserved_variable(
        &mut self,
        builder: &mut InstrSeqBuilder,
        name: &str,
        expr: &SymbolicExpression,
    ) -> Result<bool, GeneratorError> {
        if let Some(variable) = NativeVariables::lookup_by_name_at_version(
            name,
            &self.contract_analysis.clarity_version,
        ) {
            match variable {
                NativeVariables::TxSender => {
                    // Create a new local to hold the result on the call stack
                    let (offset, size);
                    (offset, size) = self.create_call_stack_local(
                        builder,
                        &TypeSignature::PrincipalType,
                        false,
                        true,
                    );

                    // Push the offset and size to the data stack
                    builder.local_get(offset).i32_const(size);

                    builder.call(self.func_by_name("stdlib.tx_sender"));

                    Ok(true)
                }
                NativeVariables::ContractCaller => {
                    // Create a new local to hold the result on the call stack
                    let (offset, size);
                    (offset, size) = self.create_call_stack_local(
                        builder,
                        &TypeSignature::PrincipalType,
                        false,
                        true,
                    );

                    // Push the offset and size to the data stack
                    builder.local_get(offset).i32_const(size);

                    // Call the host interface function, `contract_caller`
                    builder.call(self.func_by_name("stdlib.contract_caller"));
                    Ok(true)
                }
                NativeVariables::TxSponsor => {
                    // Create a new local to hold the result on the call stack
                    let (offset, size);
                    (offset, size) = self.create_call_stack_local(
                        builder,
                        &TypeSignature::PrincipalType,
                        false,
                        true,
                    );

                    // Push the offset and size to the data stack
                    builder.local_get(offset).i32_const(size);

                    // Call the host interface function, `tx_sponsor`

                    builder.call(self.func_by_name("stdlib.tx_sponsor"));
                    Ok(true)
                }
                NativeVariables::BlockHeight => {
                    // Call the host interface function, `block_height`
                    builder.call(self.func_by_name("stdlib.block_height"));
                    Ok(true)
                }
                NativeVariables::StacksBlockHeight => {
                    // Call the host interface function, `stacks_block_height`
                    builder.call(self.func_by_name("stdlib.stacks_block_height"));
                    Ok(true)
                }
                NativeVariables::TenureHeight => {
                    // Call the host interface function, `tenure_height`
                    builder.call(self.func_by_name("stdlib.tenure_height"));
                    Ok(true)
                }
                NativeVariables::BurnBlockHeight => {
                    // Call the host interface function, `burn_block_height`
                    builder.call(self.func_by_name("stdlib.burn_block_height"));
                    Ok(true)
                }
                NativeVariables::NativeNone => {
                    let ty = self.get_expr_type(expr).ok_or_else(|| {
                        GeneratorError::TypeError("'none' must be typed".to_owned())
                    })?;
                    add_placeholder_for_clarity_type(builder, ty);
                    Ok(true)
                }
                NativeVariables::NativeTrue => {
                    builder.i32_const(1);
                    Ok(true)
                }
                NativeVariables::NativeFalse => {
                    builder.i32_const(0);
                    Ok(true)
                }
                NativeVariables::TotalLiquidMicroSTX => {
                    // Call the host interface function, `stx_liquid_supply`
                    builder.call(self.func_by_name("stdlib.stx_liquid_supply"));
                    Ok(true)
                }
                NativeVariables::Regtest => {
                    // Call the host interface function, `is_in_regtest`
                    builder.call(self.func_by_name("stdlib.is_in_regtest"));
                    Ok(true)
                }
                NativeVariables::Mainnet => {
                    // Call the host interface function, `is_in_mainnet`
                    builder.call(self.func_by_name("stdlib.is_in_mainnet"));
                    Ok(true)
                }
                NativeVariables::ChainId => {
                    // Call the host interface function, `chain_id`
                    builder.call(self.func_by_name("stdlib.chain_id"));
                    Ok(true)
                }
                NativeVariables::StacksBlockTime | NativeVariables::CurrentContract => {
                    todo!("Implement NativeVariable")
                }
            }
        } else {
            Ok(false)
        }
    }

    /// If `name` is a constant, push its value onto the data stack.
    pub fn lookup_constant_variable(
        &mut self,
        builder: &mut InstrSeqBuilder,
        name: &str,
        expr: &SymbolicExpression,
    ) -> Result<bool, GeneratorError> {
        if let Some(cst_ty) = self.constants.get(name).cloned() {
            let expected_ty = self
                .get_expr_type(expr)
                .ok_or_else(|| {
                    GeneratorError::TypeError("expression using constant must be typed".to_owned())
                })?
                .clone();

            // Reserve stack space for the constant copy
            let (result_local, result_size) =
                self.create_call_stack_local(builder, &expected_ty, true, true);

            let (name_offset, name_length) = self.add_string_literal(name)?;

            // Push constant attributes to the stack.
            builder
                .i32_const(name_offset as i32)
                .i32_const(name_length as i32)
                .local_get(result_local)
                .i32_const(result_size);

            // Call a host interface function to load
            // constant attributes from a data structure.
            builder.call(self.func_by_name("stdlib.load_constant"));

            self.read_from_memory(builder, result_local, 0, &cst_ty)?;
            self.duck_type(builder, &cst_ty, &expected_ty)?;

            Ok(true)
        } else {
            Ok(false)
        }
    }

    /// Save the expression on the top of the stack, with Clarity type `ty`, to
    /// local variables. If `fix_ordering` is true, then the vector is reversed
    /// so that the types are in logical order. Without this, they will be in
    /// reverse order, due to the order we pop values from the stack. Return
    /// the list of local variables.
    pub fn save_to_locals(
        &mut self,
        builder: &mut walrus::InstrSeqBuilder,
        ty: &TypeSignature,
        fix_ordering: bool,
    ) -> Vec<LocalId> {
        let wasm_types = clar2wasm_ty(ty);
        let mut locals = Vec::with_capacity(wasm_types.len());
        // Iterate in reverse order, since we are popping items off of the top
        // in reverse order.
        for wasm_ty in wasm_types.iter().rev() {
            let local = self.module.locals.add(*wasm_ty);
            locals.push(local);
            builder.local_set(local);
        }

        if fix_ordering {
            // Reverse the locals to put them back in the correct order.
            locals.reverse();
        }
        locals
    }

    pub fn func_by_name(&self, name: &str) -> FunctionId {
        #[allow(clippy::unwrap_used)]
        get_function(&self.module, name).unwrap()
    }

    pub fn get_function_type(&self, name: &str) -> Option<&FunctionType> {
        let analysis = &self.contract_analysis;

        analysis
            .get_public_function_type(name)
            .or(analysis.get_read_only_function_type(name))
            .or(analysis.get_private_function(name))
    }

    fn visit_literal_value(
        &mut self,
        builder: &mut InstrSeqBuilder,
        _expr: &SymbolicExpression,
        value: &clarity::vm::Value,
    ) -> Result<(), GeneratorError> {
        match value {
            clarity::vm::Value::Int(i) => {
                builder.i64_const((i & 0xFFFFFFFFFFFFFFFF) as i64);
                builder.i64_const(((i >> 64) & 0xFFFFFFFFFFFFFFFF) as i64);
                Ok(())
            }
            clarity::vm::Value::UInt(u) => {
                builder.i64_const((u & 0xFFFFFFFFFFFFFFFF) as i64);
                builder.i64_const(((u >> 64) & 0xFFFFFFFFFFFFFFFF) as i64);
                Ok(())
            }
            clarity::vm::Value::Sequence(SequenceData::String(s)) => {
                let (offset, len) = self.add_clarity_string_literal(s)?;
                builder.i32_const(offset as i32);
                builder.i32_const(len as i32);
                Ok(())
            }
            clarity::vm::Value::Principal(_)
            | clarity::vm::Value::Sequence(SequenceData::Buffer(_)) => {
                let (offset, len) = self.add_literal(value)?;
                builder.i32_const(offset as i32);
                builder.i32_const(len as i32);
                Ok(())
            }
            clarity::vm::Value::Bool(_)
            | clarity::vm::Value::Tuple(_)
            | clarity::vm::Value::Optional(_)
            | clarity::vm::Value::Response(_)
            | clarity::vm::Value::CallableContract(_)
            | clarity::vm::Value::Sequence(_) => Err(GeneratorError::TypeError(format!(
                "Not a valid literal type: {value:?}"
            ))),
        }
    }

    fn visit_atom(
        &mut self,
        builder: &mut InstrSeqBuilder,
        expr: &SymbolicExpression,
        atom: &ClarityName,
    ) -> Result<(), GeneratorError> {
        // Handle builtin variables
        if self.lookup_reserved_variable(builder, atom.as_str(), expr)? {
            return Ok(());
        }

        if self.lookup_constant_variable(builder, atom.as_str(), expr)? {
            return Ok(());
        }

        // Handle parameters and local bindings
        let values = self.bindings.get_locals(atom).ok_or_else(|| {
            GeneratorError::InternalError(format!("unable to find local for {}", atom.as_str()))
        })?;

        for value in values {
            builder.local_get(*value);
        }

        Ok(())
    }

    fn traverse_call_user_defined(
        &mut self,
        builder: &mut InstrSeqBuilder,
        expr: &SymbolicExpression,
        name: &ClarityName,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        // WORKAROUND: the typechecker in epoch < 2.1 fails to set correct types for functions
        //             arguments. We set them ourselves. We don't make the distinction between
        //             epochs since it would require a deeper modification and it doesn't impact
        //             the newer ones.
        let return_ty = match self.get_function_type(name).cloned() {
            Some(FunctionType::Fixed(FixedFunction {
                args: function_args,
                returns,
            })) => {
                check_args!(
                    self,
                    builder,
                    function_args.len(),
                    args.len(),
                    ArgumentCountCheck::Exact
                );
                for (arg, signature) in args
                    .iter()
                    .zip(function_args.into_iter().map(|a| a.signature))
                {
                    self.set_expr_type(arg, signature)?;
                }
                returns
            }
            fn_ty => {
                return Err(GeneratorError::TypeError(format!(
                    "Wrong type for a user defined function: {fn_ty:?}"
                )));
            }
        };
        self.traverse_args(builder, args)?;

        let expected_ty = self
            .get_expr_type(expr)
            .ok_or_else(|| {
                GeneratorError::TypeError("function call expression must be typed".to_owned())
            })?
            .clone();
        self.visit_call_user_defined(builder, name, &return_ty, Some(&expected_ty), None)
    }

    /// Visit a function call to a user-defined function. Arguments must have
    /// already been traversed and pushed to the stack.
    ///
    /// If needed, the final answer can be duck-typed to another compatible type.
    ///
    /// If needed, if some space has been pre-allocated, we can pass a local containing the offset of the space. Otherwise,
    /// the space is allocated at $stack-pointer.
    pub fn visit_call_user_defined(
        &mut self,
        builder: &mut InstrSeqBuilder,
        name: &ClarityName,
        return_ty: &TypeSignature,
        duck_ty: Option<&TypeSignature>,
        preallocated_memory: Option<LocalId>,
    ) -> Result<(), GeneratorError> {
        // this local contains the offset at which we will copy the each new element of the result
        // if there is an in-memory type
        let in_memory_offset = has_in_memory_type(return_ty).then(|| {
            preallocated_memory.unwrap_or_else(|| {
                let return_offset = self.module.locals.add(ValType::I32);

                // in case there is an in-memory type to copy, we reserve some space in memory
                let return_size = count_in_memory_space(return_ty) as i32;
                self.frame_size += return_size;

                builder
                    .global_get(self.stack_pointer)
                    .local_tee(return_offset)
                    .i32_const(return_size)
                    .binop(BinaryOp::I32Add)
                    .global_set(self.stack_pointer);

                return_offset
            })
        });

        if self
            .contract_analysis
            .get_public_function_type(name.as_str())
            .is_some()
        {
            self.local_call_public(builder, return_ty, name)?;
        } else if self
            .contract_analysis
            .get_read_only_function_type(name.as_str())
            .is_some()
        {
            self.local_call_read_only(builder, name)?;
        } else if self
            .contract_analysis
            .get_private_function(name.as_str())
            .is_some()
        {
            self.local_call(builder, name)?;
        } else {
            return Err(GeneratorError::TypeError(format!(
                "function not found: {name}",
                name = name.as_str()
            )));
        }

        let expected_ty = duck_ty.unwrap_or(return_ty);

        // if needed, we can convert the argument to another compatible type.
        self.duck_type(builder, return_ty, expected_ty)?;

        // If an in-memory value is returned from the function, we need to copy
        // it to our frame, from the callee's frame.
        if let Some(return_offset) = in_memory_offset {
            let locals = self.save_to_locals(builder, expected_ty, true);
            self.copy_value(builder, expected_ty, &locals, return_offset)?;

            for l in locals {
                builder.local_get(l);
            }
        }

        Ok(())
    }

    /// Copies a value in *locals* to *copy_offset* while taking care of the in-memory values
    /// , especilly inner in-memory values.
    ///
    /// This is a subroutine of [`Self::visit_call_user_defined`].
    fn copy_value(
        &mut self,
        builder: &mut InstrSeqBuilder,
        ty: &TypeSignature,
        locals: &[LocalId],
        copy_offset: LocalId,
    ) -> Result<(), GeneratorError> {
        match ty {
            TypeSignature::NoType
            | TypeSignature::IntType
            | TypeSignature::UIntType
            | TypeSignature::BoolType => Ok(()),
            TypeSignature::SequenceType(SequenceSubtype::ListType(ltd)) => {
                let [offset, len] = locals else {
                    return Err(GeneratorError::InternalError(
                        "Copy: a list type should be (offset, length)".to_owned(),
                    ));
                };
                let memory = self.get_memory()?;

                // we will copy the entire list as is to its destination first
                builder
                    .local_get(copy_offset)
                    .local_get(*offset)
                    .local_get(*len)
                    .memory_copy(memory, memory);

                // update the offset to copy_offset, then move copy_offset to point after the list
                builder.local_get(copy_offset).local_set(*offset);
                builder
                    .local_get(copy_offset)
                    .local_get(*len)
                    .binop(BinaryOp::I32Add)
                    .local_set(copy_offset);

                // now we will iterate through the list elements, copy the in-memory parts and update the pointers
                let copy_loop = {
                    let mut loop_ = builder.dangling_instr_seq(None);
                    let loop_id = loop_.id();

                    let elem_ty = ltd.get_list_item_type();

                    let size = self.read_from_memory(&mut loop_, *offset, 0, elem_ty)?;
                    let elem_locals = self.save_to_locals(&mut loop_, elem_ty, true);

                    self.copy_value(&mut loop_, elem_ty, &elem_locals, copy_offset)?;
                    for l in elem_locals {
                        loop_.local_get(l);
                    }
                    self.write_to_memory(&mut loop_, *offset, 0, elem_ty)?;

                    loop_
                        .local_get(*offset)
                        .i32_const(size)
                        .binop(BinaryOp::I32Add)
                        .local_set(*offset);
                    loop_
                        .local_get(*len)
                        .i32_const(size)
                        .binop(BinaryOp::I32Sub)
                        .local_tee(*len)
                        .br_if(loop_id);

                    loop_id
                };

                // if we have elements, we will store the (offset, len) on the stack, execute the copy loop, then get back the (offset, len)
                builder.local_get(*len).if_else(
                    None,
                    |then| {
                        then.local_get(*offset)
                            .local_get(*len)
                            .instr(Loop { seq: copy_loop })
                            .local_set(*len)
                            .local_set(*offset);
                    },
                    |_| {},
                );

                Ok(())
            }
            TypeSignature::SequenceType(_)
            | TypeSignature::PrincipalType
            | TypeSignature::CallableType(_)
            | TypeSignature::TraitReferenceType(_) => {
                let [offset, len] = locals else {
                    return Err(GeneratorError::InternalError(
                        "Copy: a simple in-memory type should be (offset, length)".to_owned(),
                    ));
                };

                let memory = self.get_memory()?;
                builder
                    .local_get(copy_offset)
                    .local_get(*offset)
                    .local_get(*len)
                    .memory_copy(memory, memory);
                // Set the new offset
                builder.local_get(copy_offset).local_set(*offset);
                // Increment the copy offset
                builder
                    .local_get(copy_offset)
                    .local_get(*len)
                    .binop(BinaryOp::I32Add)
                    .local_set(copy_offset);
                Ok(())
            }
            TypeSignature::OptionalType(opt) => {
                let some_id = {
                    let mut some = builder.dangling_instr_seq(None);
                    self.copy_value(&mut some, opt, &locals[1..], copy_offset)?;
                    some.id()
                };
                let none_id = builder.dangling_instr_seq(None).id();

                builder.local_get(locals[0]).instr(IfElse {
                    consequent: some_id,
                    alternative: none_id,
                });

                Ok(())
            }
            TypeSignature::ResponseType(resp) => {
                let (ok_ty, err_ty) = &**resp;
                let variant = locals[0];
                let (ok_locals, err_locals) = locals[1..].split_at(clar2wasm_ty(ok_ty).len());
                let ok_id = {
                    let mut ok = builder.dangling_instr_seq(None);
                    if has_in_memory_type(ok_ty) {
                        self.copy_value(&mut ok, ok_ty, ok_locals, copy_offset)?;
                    }
                    ok.id()
                };
                let err_id = {
                    let mut err = builder.dangling_instr_seq(None);
                    if has_in_memory_type(err_ty) {
                        self.copy_value(&mut err, err_ty, err_locals, copy_offset)?;
                    }
                    err.id()
                };
                builder.local_get(variant).instr(IfElse {
                    consequent: ok_id,
                    alternative: err_id,
                });
                Ok(())
            }
            TypeSignature::TupleType(tuple_type_signature) => {
                let inner_ty_and_locals = tuple_type_signature.get_type_map().values().scan(
                    locals,
                    |remaining_locals, ty| {
                        let current_locals;
                        (current_locals, *remaining_locals) =
                            remaining_locals.split_at(clar2wasm_ty(ty).len());
                        Some((ty, current_locals))
                    },
                );

                for (ty, locals) in inner_ty_and_locals {
                    if has_in_memory_type(ty) {
                        self.copy_value(builder, ty, locals, copy_offset)?;
                    }
                }
                Ok(())
            }
            TypeSignature::ListUnionType(_) => {
                unreachable!("ListUnionType is not a value type")
            }
        }
    }

    /// Call a function defined in the current contract.
    fn local_call(
        &mut self,
        builder: &mut InstrSeqBuilder,
        name: &ClarityName,
    ) -> Result<(), GeneratorError> {
        builder.call(self.func_by_name(name.as_str()));

        Ok(())
    }

    /// Call a public function defined in the current contract. This requires
    /// going through the host interface to handle roll backs.
    fn local_call_public(
        &mut self,
        builder: &mut InstrSeqBuilder,
        return_ty: &TypeSignature,
        name: &ClarityName,
    ) -> Result<(), GeneratorError> {
        // Call the host interface function, `begin_public_call`
        builder.call(self.func_by_name("stdlib.begin_public_call"));

        self.local_call(builder, name)?;

        // Save the result to a local
        let result_locals = self.save_to_locals(builder, return_ty, true);

        // If the result is an `ok`, then we can commit the call, and if it
        // is an `err`, then we roll it back. `result_locals[0]` is the
        // response indicator (all public functions return a response).
        let if_id = {
            let mut if_case: InstrSeqBuilder<'_> = builder.dangling_instr_seq(None);
            if_case.call(self.func_by_name("stdlib.commit_call"));
            if_case.id()
        };

        let else_id = {
            let mut else_case: InstrSeqBuilder<'_> = builder.dangling_instr_seq(None);
            else_case.call(self.func_by_name("stdlib.roll_back_call"));
            else_case.id()
        };

        builder.local_get(result_locals[0]).instr(IfElse {
            consequent: if_id,
            alternative: else_id,
        });

        // Restore the result to the top of the stack.
        for local in &result_locals {
            builder.local_get(*local);
        }

        Ok(())
    }

    /// Call a read-only function defined in the current contract.
    fn local_call_read_only(
        &mut self,
        builder: &mut InstrSeqBuilder,
        name: &ClarityName,
    ) -> Result<(), GeneratorError> {
        // Call the host interface function, `begin_readonly_call`
        builder.call(self.func_by_name("stdlib.begin_read_only_call"));

        self.local_call(builder, name)?;

        // Call the host interface function, `roll_back_call`
        builder.call(self.func_by_name("stdlib.roll_back_call"));

        Ok(())
    }

    pub fn traverse_args(
        &mut self,
        builder: &mut InstrSeqBuilder,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        for arg in args.iter() {
            self.traverse_expr(builder, arg)?;
        }
        Ok(())
    }

    pub fn debug_msg<M: Into<String>>(&mut self, builder: &mut InstrSeqBuilder, message: M) {
        let id = debug_msg::register(message.into());
        builder.i32_const(id);
        builder.call(self.func_by_name("debug_msg"));
    }

    /// Dump the top of the stack to debug messages
    pub fn debug_dump_stack<M: Into<String>>(
        &mut self,
        builder: &mut InstrSeqBuilder,
        message: M,
        expected_types: &[ValType],
    ) {
        self.debug_msg(builder, message);
        self.debug_msg(builder, "<stack dump start>");
        let mut locals = vec![];

        for t in expected_types {
            let l = self.borrow_local(*t);
            builder.local_tee(*l);
            locals.push(l);
            match t {
                ValType::I32 => self.debug_log_i32(builder),
                ValType::I64 => self.debug_log_i64(builder),
                _ => {
                    // allow unimplemented in debug code
                    #[allow(clippy::unimplemented)]
                    {
                        unimplemented!("unsupported stack dump type")
                    }
                }
            }
        }
        self.debug_msg(builder, "<stack dump end>");

        // restore the stack
        while let Some(l) = locals.pop() {
            builder.local_get(*l);
        }
    }

    pub fn debug_log_local_i32<M: Into<String>>(
        &mut self,
        builder: &mut InstrSeqBuilder,
        message: M,
        local_id: &LocalId,
    ) {
        self.debug_msg(builder, message);
        builder.local_get(*local_id);
        self.debug_log_i32(builder)
    }

    pub fn debug_log_local_i64<M: Into<String>>(
        &mut self,
        builder: &mut InstrSeqBuilder,
        message: M,
        local_id: &LocalId,
    ) {
        self.debug_msg(builder, message);
        builder.local_get(*local_id);
        self.debug_log_i64(builder)
    }

    #[allow(dead_code)]
    /// Log an i64 that is on top of the stack.
    pub fn debug_log_i64(&self, builder: &mut InstrSeqBuilder) {
        builder.call(self.func_by_name("log"));
    }

    #[allow(dead_code)]
    /// Log an i32 that is on top of the stack.
    pub fn debug_log_i32(&self, builder: &mut InstrSeqBuilder) {
        builder
            .unop(UnaryOp::I64ExtendUI32)
            .call(self.func_by_name("log"));
    }

    pub(crate) fn is_reserved_name(&self, name: &ClarityName) -> bool {
        let version = self.contract_analysis.clarity_version;

        functions::lookup_reserved_functions(name.as_str(), &version).is_some()
            || variables::is_reserved_name(name, &version)
    }

    pub fn get_sequence_element_type(
        &self,
        sequence: &SymbolicExpression,
    ) -> Result<SequenceElementType, GeneratorError> {
        match self.get_expr_type(sequence).ok_or_else(|| {
            GeneratorError::TypeError("sequence expression must be typed".to_owned())
        })? {
            TypeSignature::SequenceType(seq_ty) => match &seq_ty {
                SequenceSubtype::ListType(list_type) => Ok(SequenceElementType::Other(
                    list_type.get_list_item_type().clone(),
                )),
                SequenceSubtype::BufferType(_)
                | SequenceSubtype::StringType(StringSubtype::ASCII(_)) => {
                    // For buffer and string-ascii return none, which indicates
                    // that elements should be read byte-by-byte.
                    Ok(SequenceElementType::Byte)
                }
                SequenceSubtype::StringType(StringSubtype::UTF8(_)) => {
                    Ok(SequenceElementType::UnicodeScalar)
                }
            },
            _ => Err(GeneratorError::TypeError(
                "expected sequence type".to_string(),
            )),
        }
    }

    /// Ensure enough work space is going to be available in memory
    pub(crate) fn ensure_work_space(&mut self, bytes_len: u32) {
        self.max_work_space = self.max_work_space.max(bytes_len);
    }

    pub(crate) fn get_current_function_return_type(&self) -> Option<&TypeSignature> {
        self.current_function_type.as_ref().map(|f| &f.returns)
    }

    pub(crate) fn get_current_function_arg_type(
        &self,
        arg_name: &ClarityName,
    ) -> Option<&TypeSignature> {
        self.current_function_type
            .as_ref()
            .map(|f| &f.args)
            .and_then(|args| {
                args.iter()
                    .find_map(|arg| (&arg.name == arg_name).then_some(&arg.signature))
            })
    }
}

/// Returns true if a composed type has an inner in-memory type.
fn has_in_memory_type(ty: &TypeSignature) -> bool {
    match ty {
        TypeSignature::OptionalType(opt) => has_in_memory_type(opt),
        TypeSignature::ResponseType(resp) => {
            has_in_memory_type(&resp.0) || has_in_memory_type(&resp.1)
        }
        TypeSignature::TupleType(tup) => tup.get_type_map().values().any(has_in_memory_type),
        TypeSignature::NoType
        | TypeSignature::IntType
        | TypeSignature::UIntType
        | TypeSignature::BoolType => false,
        TypeSignature::SequenceType(_)
        | TypeSignature::PrincipalType
        | TypeSignature::CallableType(_)
        | TypeSignature::TraitReferenceType(_) => true,
        TypeSignature::ListUnionType(_) => unreachable!("not a value type"),
    }
}

/// Counts the amount of bytes needed in memory for a type.
fn count_in_memory_space(ty: &TypeSignature) -> u32 {
    match ty {
        TypeSignature::BoolType
        | TypeSignature::IntType
        | TypeSignature::UIntType
        | TypeSignature::NoType => 0,
        TypeSignature::OptionalType(opt) => count_in_memory_space(opt),
        TypeSignature::ResponseType(resp) => {
            count_in_memory_space(&resp.0) + count_in_memory_space(&resp.1)
        }
        TypeSignature::PrincipalType
        | TypeSignature::CallableType(_)
        | TypeSignature::TraitReferenceType(_) => PRINCIPAL_BYTES_MAX as u32,
        TypeSignature::SequenceType(SequenceSubtype::BufferType(len))
        | TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(len))) => {
            len.into()
        }
        TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(len))) => {
            4 * u32::from(len)
        }
        TypeSignature::SequenceType(SequenceSubtype::ListType(ltd)) => {
            ltd.get_max_len() * get_type_in_memory_size(ltd.get_list_item_type(), true) as u32
        }
        TypeSignature::TupleType(tup) => {
            tup.get_type_map().values().map(count_in_memory_space).sum()
        }
        TypeSignature::ListUnionType(_) => unreachable!("not a value type"),
    }
}

#[cfg(test)]
mod tests {
    use std::env;

    use clarity::types::StacksEpochId;
    use clarity::vm::analysis::AnalysisDatabase;
    use clarity::vm::costs::LimitedCostTracker;
    use clarity::vm::database::MemoryBackingStore;
    use clarity::vm::errors::{CheckErrors, Error};
    use clarity::vm::types::{QualifiedContractIdentifier, StandardPrincipalData, TupleData};
    use clarity::vm::{ClarityVersion, Value};
    use walrus::Module;

    // Tests that don't relate to specific words
    use crate::{
        compile,
        tools::{crosscheck, evaluate},
        wasm_generator::END_OF_STANDARD_DATA,
    };

    #[test]
    fn is_in_regtest() {
        crosscheck(
            "
(define-public (regtest)
  (ok is-in-regtest))

(regtest)
",
            evaluate("(ok false)"),
        );
    }

    #[test]
    fn should_set_memory_pages() {
        let string_size = 262000;
        let a = "a".repeat(string_size);
        let b = "b".repeat(string_size);
        let c = "c".repeat(string_size);
        let d = "d".repeat(string_size);

        let snippet = format!("(is-eq u\"{a}\" u\"{b}\" u\"{c}\" u\"{d}\")");
        crosscheck(&snippet, Ok(Some(clarity::vm::Value::Bool(false))));
    }

    #[test]
    fn test_work_space() {
        let buff_len = 1048576;
        let buff = "aa".repeat(buff_len);

        let get_initial_memory = |snippet: String| {
            let module = compile(
                &snippet,
                &QualifiedContractIdentifier::new(
                    StandardPrincipalData::transient(),
                    ("tmp").into(),
                ),
                LimitedCostTracker::new_free(),
                ClarityVersion::Clarity2,
                StacksEpochId::Epoch25,
                &mut AnalysisDatabase::new(&mut MemoryBackingStore::new()),
                false,
            )
            .unwrap()
            .module;
            let mem = module.memories.iter().next().unwrap().initial;
            mem
        };
        let prologue = format!("(let ((foo 0x{buff})) ");
        // sha256 requires some extra work space, thus extra pages
        assert!(
            get_initial_memory(format!("{prologue} (len foo))"))
                < get_initial_memory(format!("{prologue} (sha256 foo))"))
        );
        // but multiple calls do not cause more pages
        assert_eq!(
            get_initial_memory(format!("{prologue} (sha256 foo))")),
            get_initial_memory(format!("{prologue} (sha256 foo) (sha256 foo))"))
        );
    }

    #[test]
    fn end_of_standard_data_is_correct() {
        const STANDARD_LIB_PATH: &str =
            concat!(env!("CARGO_MANIFEST_DIR"), "/src/standard/standard.wasm");
        let standard_lib_wasm = std::fs::read(STANDARD_LIB_PATH).expect("Failed to read WASM file");
        let module = Module::from_buffer(&standard_lib_wasm).unwrap();
        let initial_data_size: usize = module.data.iter().map(|d| d.value.len()).sum();

        assert!((initial_data_size as u32) == END_OF_STANDARD_DATA);
    }

    #[test]
    fn function_argument_have_correct_type() {
        let snippet = r#"
            (define-private (foo (arg (optional uint)))
                true
            )

            (foo none)
        "#;
        crosscheck(snippet, Ok(Some(clarity::vm::Value::Bool(true))));

        // issue 340 showed a bug for epoch < 2.1
        assert!(crate::tools::evaluate_at(
            snippet,
            clarity::types::StacksEpochId::Epoch20,
            clarity::vm::version::ClarityVersion::latest(),
        )
        .is_ok());
    }

    #[test]
    fn top_level_result_none() {
        crosscheck(
            "
(define-public (foo)
  (ok true))

(define-public (bar)
  (ok true))
",
            Ok(None),
        );
    }

    #[test]
    fn top_level_result_some_last() {
        crosscheck(
            "
(define-private (foo) 42)
(define-public (bar)
  (ok true))
(foo)
",
            evaluate("42"),
        );
    }

    #[test]
    fn top_level_result_some_not_last() {
        crosscheck(
            "
(define-public (foo)
  (ok true))
(foo)
(define-public (bar)
  (ok true))
",
            evaluate("(ok true)"),
        );
    }

    #[test]
    fn function_has_correct_argument_count() {
        // TODO: see issue #488
        // The inconsistency in function arguments should have been caught by the typechecker.
        // The runtime error below is being used as a workaround for a typechecker issue
        // where certain errors are not properly handled.
        // This test should be re-worked once the typechecker is fixed
        // and can correctly detect all argument inconsistencies.
        crosscheck(
            "
(define-public (foo (arg int))
  (ok true))
(foo 1 2)
(define-public (bar (arg int))
  (ok true))
(bar)
",
            Err(Error::Unchecked(CheckErrors::IncorrectArgumentCount(1, 2))),
        );
    }

    #[test]
    fn function_result_dont_erase_previous() {
        // from issue #475
        let snippet = r#"
        (define-map mymap int int)
        (define-private (somefn)
            (begin
                (map-set mymap 0 99)
                (err (list u"foo"))
            )
        )
        { fn: (somefn), mymap: (map-get? mymap 0) }
        "#;

        let expected = Value::from(
            TupleData::from_data(vec![
                (
                    "fn".into(),
                    Value::error(
                        Value::cons_list_unsanitized(vec![Value::string_utf8_from_bytes(
                            b"foo".to_vec(),
                        )
                        .unwrap()])
                        .unwrap(),
                    )
                    .unwrap(),
                ),
                ("mymap".into(), Value::some(Value::Int(99)).unwrap()),
            ])
            .unwrap(),
        );

        crosscheck(snippet, Ok(Some(expected)));
    }

    #[test]
    fn function_call_needs_ducktyping() {
        let snippet = r#"
            (define-public (execute)
                (if true (foo) (err u42))
            )

            (define-private (foo)
                (ok u123)
            )

            (execute)
    "#;

        crosscheck(snippet, Ok(Some(Value::okay(Value::UInt(123)).unwrap())));
    }

    //
    // Module with tests that should only be executed
    // when running Clarity::V2 or Clarity::v3.
    //
    #[cfg(not(feature = "test-clarity-v1"))]
    #[cfg(test)]
    mod clarity_v2_v3 {
        use super::*;

        #[test]
        fn is_in_mainnet() {
            crosscheck(
                "
    (define-public (mainnet)
      (ok is-in-mainnet))

    (mainnet)
    ",
                evaluate("(ok false)"),
            );
        }
    }
}
