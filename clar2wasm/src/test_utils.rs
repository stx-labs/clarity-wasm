#![allow(clippy::expect_used, clippy::unwrap_used)]

use clarity::types::StacksEpochId;
use clarity::vm::analysis::ContractAnalysis;
use clarity::vm::costs::LimitedCostTracker;
use clarity::vm::types::{
    QualifiedContractIdentifier, SequenceData, SequenceSubtype, TypeSignature,
};
use clarity::vm::{ClarityVersion, Value};
use walrus::{FunctionBuilder, InstrSeqBuilder, MemoryId};
use wasmtime::{Engine, Module, Store};

use crate::linker::dummy_linker;
use crate::wasm_generator::{
    add_placeholder_for_clarity_type, clar2wasm_ty, GeneratorError, WasmGenerator,
};
use crate::wasm_utils::{placeholder_for_type, wasm_to_clarity_value};

impl WasmGenerator {
    /// Creates an empty WasmGenerator.
    pub fn empty() -> Self {
        let empty_analysis = ContractAnalysis::new(
            QualifiedContractIdentifier::transient(),
            vec![],
            LimitedCostTracker::Free,
            StacksEpochId::latest(),
            ClarityVersion::latest(),
        );
        WasmGenerator::new(empty_analysis)
            .expect("failed to build WasmGenerator for empty contract")
    }

    pub fn get_memory_with_pages(&mut self, pages: u32) -> MemoryId {
        let memory = self.module.memories.iter_mut().next().unwrap();
        memory.initial = pages;
        memory.id()
    }

    /// Adds the instructions to have a value of some type on top of the stack.
    pub fn pass_value(
        &mut self,
        builder: &mut InstrSeqBuilder,
        value: &Value,
        ty: &TypeSignature,
    ) -> Result<(), GeneratorError> {
        match value {
            Value::Bool(b) => {
                builder.i32_const(*b as i32);
                Ok(())
            }
            Value::Int(i) => {
                builder.i64_const((i & 0xFFFFFFFFFFFFFFFF) as i64);
                builder.i64_const(((i >> 64) & 0xFFFFFFFFFFFFFFFF) as i64);
                Ok(())
            }
            Value::UInt(u) => {
                builder.i64_const((u & 0xFFFFFFFFFFFFFFFF) as i64);
                builder.i64_const(((u >> 64) & 0xFFFFFFFFFFFFFFFF) as i64);
                Ok(())
            }
            Value::Sequence(SequenceData::String(s)) => {
                let (offset, len) = self.add_clarity_string_literal(s)?;
                builder.i32_const(offset as i32);
                builder.i32_const(len as i32);
                Ok(())
            }
            Value::Principal(_) | Value::Sequence(SequenceData::Buffer(_)) => {
                let (offset, len) = self.add_literal(value)?;
                builder.i32_const(offset as i32);
                builder.i32_const(len as i32);
                Ok(())
            }
            Value::Optional(opt) => {
                let TypeSignature::OptionalType(inner_ty) = ty else {
                    return Err(GeneratorError::InternalError(
                        "Mismatched value/type".to_owned(),
                    ));
                };
                match &opt.data {
                    Some(inner) => {
                        builder.i32_const(1);
                        self.pass_value(builder, inner, inner_ty)?;
                    }
                    None => {
                        builder.i32_const(0);
                        add_placeholder_for_clarity_type(builder, inner_ty);
                    }
                }
                Ok(())
            }
            Value::Response(resp) => {
                let TypeSignature::ResponseType(resp_ty) = ty else {
                    return Err(GeneratorError::InternalError(
                        "Mismatched value/type".to_owned(),
                    ));
                };
                builder.i32_const(resp.committed as i32);
                if resp.committed {
                    self.pass_value(builder, &resp.data, &resp_ty.0)?;
                    add_placeholder_for_clarity_type(builder, &resp_ty.1);
                } else {
                    add_placeholder_for_clarity_type(builder, &resp_ty.0);
                    self.pass_value(builder, &resp.data, &resp_ty.1)?;
                }
                Ok(())
            }
            Value::Tuple(tuple) => {
                let TypeSignature::TupleType(tuple_ty) = ty else {
                    return Err(GeneratorError::InternalError(
                        "Mismatched value/type".to_owned(),
                    ));
                };
                for (elem, elem_ty) in tuple
                    .data_map
                    .values()
                    .zip(tuple_ty.get_type_map().values())
                {
                    self.pass_value(builder, elem, elem_ty)?;
                }
                Ok(())
            }
            Value::Sequence(SequenceData::List(list)) => {
                let TypeSignature::SequenceType(SequenceSubtype::ListType(ltd)) = ty else {
                    return Err(GeneratorError::InternalError(
                        "Mismatched value/type".to_owned(),
                    ));
                };
                let offset = self.module.locals.add(walrus::ValType::I32);

                for value in list.data.iter().rev() {
                    self.pass_value(builder, value, ltd.get_list_item_type())?;
                }

                builder.global_get(self.stack_pointer).local_set(offset);
                let mut length = 0;
                for _ in 0..list.data.len() {
                    let written =
                        self.write_to_memory(builder, offset, 0, ltd.get_list_item_type())?;
                    builder
                        .local_get(offset)
                        .i32_const(written as i32)
                        .binop(walrus::ir::BinaryOp::I32Add)
                        .local_set(offset);
                    length += written;
                }

                // the offset is already on the stack
                builder
                    .global_get(self.stack_pointer)
                    .i32_const(length as i32);

                builder.local_get(offset).global_set(self.stack_pointer);
                Ok(())
            }
            #[allow(clippy::unimplemented)]
            Value::CallableContract(_) => unimplemented!("We can already test principals"),
        }
    }

    /// Creates a module containing a `.top-level` function which will contain the instructions
    /// passed in the closure `add_instruction`. This closure takes as argument the current
    /// generator and the current builder.
    pub fn create_module(
        &mut self,
        return_ty: &TypeSignature,
        mut add_instructions: impl FnMut(&mut Self, &mut InstrSeqBuilder),
    ) {
        let return_ty = clar2wasm_ty(return_ty);
        let mut top_level = FunctionBuilder::new(&mut self.module.types, &[], &return_ty);

        add_instructions(self, &mut top_level.func_body());

        let top_level = top_level.finish(vec![], &mut self.module.funcs);
        self.module.exports.add(".top-level", top_level);

        // TODO: remove magic number 20000
        self.module.globals.get_mut(self.stack_pointer).kind =
            walrus::GlobalKind::Local(walrus::InitExpr::Value(walrus::ir::Value::I32(20000)));
    }

    /// Compiles and executes the current module and returns the value on top of the stack.
    /// If the value isn't of the type passed as a parameter, the function panics.
    pub fn execute_module(&mut self, return_ty: &TypeSignature) -> Value {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let linker = dummy_linker(&engine).expect("failed to create linker");
        let module =
            Module::new(&engine, self.module.emit_wasm()).expect("failed to create module");
        let instance = linker
            .instantiate(&mut store, &module)
            .expect("failed to instanciate module");

        let top_level = instance
            .get_func(&mut store, ".top-level")
            .expect("cannot find .top-level function");

        let mut result: Vec<_> = top_level
            .ty(&mut store)
            .results()
            .map(placeholder_for_type)
            .collect();

        top_level
            .call(&mut store, &[], &mut result)
            .expect("couldn't call .top-level");

        let memory = instance
            .get_memory(&mut store, "memory")
            .expect("couldn't find memory");

        wasm_to_clarity_value(
            return_ty,
            0,
            &result,
            memory,
            &mut store,
            StacksEpochId::latest(),
        )
        .expect("error in execution")
        .0
        .expect("no value computed???")
    }
}
