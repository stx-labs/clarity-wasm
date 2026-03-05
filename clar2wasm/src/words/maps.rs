use clarity::types::StacksEpochId;
use clarity::vm::analysis::ContractAnalysis;
use clarity::vm::types::{TypeSignature, TypeSignatureExt};
use clarity::vm::{ClarityName, SymbolicExpression};
use walrus::ir::{BinaryOp, IfElse, InstrSeqType};
use walrus::ValType;

use super::{ComplexWord, Word};
use crate::check_args;
use crate::cost::WordCharge;
use crate::error_mapping::ErrorMap;
use crate::wasm_generator::{
    clar2wasm_ty, ArgumentsExt, GeneratorError, LiteralMemoryEntry, WasmGenerator,
};
use crate::wasm_utils::ArgumentCountCheck;

#[derive(Debug)]
pub struct MapDefinition;

impl Word for MapDefinition {
    fn name(&self) -> ClarityName {
        "define-map".into()
    }
}

impl ComplexWord for MapDefinition {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 3, args.len(), ArgumentCountCheck::Exact);

        let name = args.get_name(0)?;
        // Making sure if name is not reserved
        if generator.is_reserved_name(name) {
            return Err(GeneratorError::InternalError(format!(
                "Name already used {name:?}"
            )));
        }

        let key_type = args.get_expr(1).and_then(|sym_ty| {
            TypeSignature::parse_type_repr(generator.contract_analysis.epoch, sym_ty, &mut ())
                .map_err(|e| GeneratorError::TypeError(format!("invalid type for map key: {e}")))
        })?;
        let value_type = args.get_expr(2).and_then(|sym_ty| {
            TypeSignature::parse_type_repr(generator.contract_analysis.epoch, sym_ty, &mut ())
                .map_err(|e| GeneratorError::TypeError(format!("invalid type for map value: {e}")))
        })?;

        // Store the identifier as a string literal in the memory
        let (name_offset, name_length) = generator.add_string_literal(name)?;

        // Push the name onto the data stack
        builder
            .i32_const(name_offset as i32)
            .i32_const(name_length as i32);

        builder.call(generator.func_by_name("stdlib.define_map"));

        // Add the map types to generator
        generator
            .maps_types
            .insert(name.clone(), (key_type, value_type));

        Ok(())
    }
}

#[derive(Debug)]
pub struct MapGet;

impl Word for MapGet {
    fn name(&self) -> ClarityName {
        "map-get?".into()
    }
}

impl ComplexWord for MapGet {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 2, args.len(), ArgumentCountCheck::Exact);

        let name = args.get_name(0)?;
        let key = args.get_expr(1)?;

        let (key_ty, original_value_type) = generator
            .maps_types
            .get(name)
            .ok_or_else(|| {
                GeneratorError::TypeError("Type should have been set in map creation".to_owned())
            })?
            .clone();

        // Get the offset and length for this identifier in the literal memory
        let id_offset = *generator
            .literal_memory_offset
            .get(&LiteralMemoryEntry::Ascii(name.as_str().into()))
            .ok_or_else(|| GeneratorError::InternalError(format!("map not found: {name}")))?;
        let id_length = name.len();

        // Push the identifier offset and length onto the data stack
        builder
            .i32_const(id_offset as i32)
            .i32_const(id_length as i32);

        let (key_offset, _) = generator.create_call_stack_local(builder, &key_ty, true, false);

        // In epoch >= 2.05, we generate a local to compute intermediary results used in the
        // cost tracking. In this case, the cost tracking charge is applied after the delete operation.
        // In epoch < 2.05, the charge is immediately computed like it is in the interpreter.
        let post205_cost_local = if generator.contract_analysis.epoch >= StacksEpochId::Epoch2_05 {
            let l = generator.borrow_local(ValType::I32);
            Some(l)
        } else {
            let contract_analysis = generator.contract_analysis_original.clone();
            let (key_ty, value_ty) = get_original_types(&contract_analysis, name)?;
            charge_default_cost_value_and_key_size(value_ty, key_ty, generator, builder, self)?;
            None
        };

        // Push the key to the data stack
        generator.set_expr_type(key, key_ty.clone())?;
        generator.traverse_expr(builder, key)?;
        // for epoch >= 2.05, we compute the serialization size of the key.
        if let Some(cost_local) = &post205_cost_local {
            generator.serialization_size(builder, &key_ty)?;
            builder.local_set(**cost_local);
        }

        // Write the key to the memory (it's already on the data stack)
        let key_size = generator.write_to_memory(builder, key_offset, 0, &key_ty)?;

        // Push the key offset and size to the data stack
        builder.local_get(key_offset).i32_const(key_size as i32);

        let value_type = TypeSignature::OptionalType(Box::new(original_value_type.clone()));
        let (return_offset, size) =
            generator.create_call_stack_local(builder, &value_type, true, true);

        let return_size = generator.module.locals.add(ValType::I32);
        builder.i32_const(size).local_set(return_size);

        // Push the return value offset and size to the data stack
        builder.local_get(return_offset).local_get(return_size);

        // Call the host-interface function, `map_get`
        builder.call(generator.func_by_name("stdlib.map_get"));

        // Host interface fills the result into the specified memory. Read it
        // back out, and place the value on the data stack.
        generator.read_from_memory(builder, return_offset, 0, &value_type)?;

        let ty = clar2wasm_ty(&value_type);

        let block_ty = InstrSeqType::new(&mut generator.module.types, &ty.clone(), &ty);
        // In > 2.05 we have three different costs depending if
        //      - an error occurred in the interpreter
        //      - no error occurred
        //          - and the value the operation is performed on is found
        //          - and the value the operation is performed on is not found
        let success_block_id = {
            // When the linked operation does not fail due to an interpreter error
            let mut success_block = builder.dangling_instr_seq(block_ty);
            if let Some(cost_local) = &post205_cost_local {
                generator.serialization_size(&mut success_block, &value_type)?;
                let value_serialization_size = generator.borrow_local(ValType::I32);
                // We check if the serialized size of the returned value is different than 1, aka the serialization size of a none
                success_block
                    .local_tee(*value_serialization_size)
                    .i32_const(1)
                    .binop(BinaryOp::I32Ne)
                    .if_else(
                        None,
                        |then| {
                            // If it is different it means that a value was found in the map
                            // In which case we charge the serialization size of the key + the serialization size of the found value
                            then.local_get(**cost_local)
                                .local_get(*value_serialization_size)
                                .binop(BinaryOp::I32Add)
                                .local_set(**cost_local);
                        },
                        |_| {
                            // If it is equal then we charge only the serialization size of the key, which has already been assigned to post205_cost_local
                        },
                    );
                self.charge(generator, &mut success_block, **cost_local)?;
            }
            success_block.id()
        };

        let error_block_id = {
            // When the linked operation fails due to an interpreter error
            let mut error_block = builder.dangling_instr_seq(None);
            if post205_cost_local.is_some() {
                let contract_analysis = generator.contract_analysis_original.clone();
                let (key_ty, value_ty) = get_original_types(&contract_analysis, name)?;
                charge_default_cost_value_and_key_size(
                    value_ty,
                    key_ty,
                    generator,
                    &mut error_block,
                    self,
                )?;
            }

            // Throws back the runtime error that occurred in the interpreter after charging the cost
            error_block
                .i32_const(ErrorMap::ExternError as i32)
                .call(generator.func_by_name("stdlib.runtime-error"));
            error_block.id()
        };

        builder
            .global_get(generator.linked_error)
            .ref_is_null()
            .instr(IfElse {
                consequent: success_block_id,
                alternative: error_block_id,
            });

        Ok(())
    }
}

#[derive(Debug)]
pub struct MapSet;

impl Word for MapSet {
    fn name(&self) -> ClarityName {
        "map-set".into()
    }
}

impl ComplexWord for MapSet {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 3, args.len(), ArgumentCountCheck::Exact);

        let name = args.get_name(0)?;
        let key = args.get_expr(1)?;
        let value = args.get_expr(2)?;

        let (key_ty, value_type) = generator
            .maps_types
            .get(name)
            .ok_or_else(|| {
                GeneratorError::TypeError("Types should have been set in map creation".to_owned())
            })?
            .clone();

        // Get the offset and length for this identifier in the literal memory
        let id_offset = *generator
            .literal_memory_offset
            .get(&LiteralMemoryEntry::Ascii(name.as_str().into()))
            .ok_or_else(|| GeneratorError::InternalError(format!("map not found: {name}")))?;
        let id_length = name.len();

        // Push the identifier offset and length onto the data stack
        builder
            .i32_const(id_offset as i32)
            .i32_const(id_length as i32);

        let (key_offset, _) = generator.create_call_stack_local(builder, &key_ty, true, false);

        // In epoch >= 2.05, we generate a local to compute intermediary results used in the
        // cost tracking. In this case, the cost tracking charge is applied after the delete operation.
        // In epoch < 2.05, the charge is immediately computed like it is in the interpreter.
        let post205_cost_local = if generator.contract_analysis.epoch >= StacksEpochId::Epoch2_05 {
            let l = generator.borrow_local(ValType::I32);
            Some(l)
        } else {
            let contract_analysis = generator.contract_analysis_original.clone();
            let (key_ty, value_ty) = get_original_types(&contract_analysis, name)?;
            charge_default_cost_value_and_key_size(value_ty, key_ty, generator, builder, self)?;
            None
        };

        // Push the key to the data stack
        generator.set_expr_type(key, key_ty.clone())?;
        generator.traverse_expr(builder, key)?;

        if let Some(cost_local) = &post205_cost_local {
            generator.serialization_size(builder, &key_ty)?;
            builder.local_set(**cost_local);
        }

        // Write the key to the memory (it's already on the data stack)
        let key_size = generator.write_to_memory(builder, key_offset, 0, &key_ty)?;

        // Push the key offset and size to the data stack
        builder.local_get(key_offset).i32_const(key_size as i32);

        // Create space on the call stack to write the value
        let (val_offset, _) = generator.create_call_stack_local(builder, &value_type, true, false);

        // Push the value to the data stack
        generator.set_expr_type(value, value_type.clone())?;
        generator.traverse_expr(builder, value)?;
        if let Some(cost_local) = &post205_cost_local {
            generator.serialization_size(builder, &value_type)?;
            builder
                .local_get(**cost_local)
                .binop(BinaryOp::I32Add)
                .local_set(**cost_local);
        }

        // Write the value to the memory (it's already on the data stack)
        let val_size = generator.write_to_memory(builder, val_offset, 0, &value_type)?;

        // Push the value offset and size to the data stack
        builder.local_get(val_offset).i32_const(val_size as i32);

        // Call the host interface function, `map_set`
        builder.call(generator.func_by_name("stdlib.map_set"));

        // In > 2.05 we have two different costs depending if
        //      - an error occurred in the interpreter
        //      - no error occurred
        let success_block_id = {
            // When the linked operation does not fail due to an interpreter error
            let mut success_block = builder.dangling_instr_seq(None);
            if let Some(cost_local) = &post205_cost_local {
                self.charge(generator, &mut success_block, **cost_local)?;
            }
            success_block.id()
        };

        let error_block_id = {
            // When the linked operation fails due to an interpreter error
            let mut error_block = builder.dangling_instr_seq(None);

            if post205_cost_local.is_some() {
                // The cost in < 2.05 has already been handled before
                let contract_analysis = generator.contract_analysis_original.clone();
                let (key_ty, value_ty) = get_original_types(&contract_analysis, name)?;
                charge_default_cost_value_and_key_size(
                    value_ty,
                    key_ty,
                    generator,
                    &mut error_block,
                    self,
                )?;
            }

            // Throws back the runtime error that occurred in the interpreter after charging the cost
            error_block
                .i32_const(ErrorMap::ExternError as i32)
                .call(generator.func_by_name("stdlib.runtime-error"));

            error_block.id()
        };

        builder
            .global_get(generator.linked_error)
            .ref_is_null()
            .instr(IfElse {
                consequent: success_block_id,
                alternative: error_block_id,
            });

        Ok(())
    }
}

#[derive(Debug)]
pub struct MapInsert;

impl Word for MapInsert {
    fn name(&self) -> ClarityName {
        "map-insert".into()
    }
}

impl ComplexWord for MapInsert {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 3, args.len(), ArgumentCountCheck::Exact);

        let name = args.get_name(0)?;
        let key = args.get_expr(1)?;
        let value = args.get_expr(2)?;

        let (key_ty, value_type) = generator
            .maps_types
            .get(name)
            .ok_or_else(|| {
                GeneratorError::TypeError("Types should have been set in map creation".to_owned())
            })?
            .clone();

        // Get the offset and length for this identifier in the literal memory
        let id_offset = *generator
            .literal_memory_offset
            .get(&LiteralMemoryEntry::Ascii(name.as_str().into()))
            .ok_or_else(|| GeneratorError::InternalError(format!("map not found: {name}")))?;
        let id_length = name.len();

        // Push the identifier offset and length onto the data stack
        builder
            .i32_const(id_offset as i32)
            .i32_const(id_length as i32);

        let (key_offset, _) = generator.create_call_stack_local(builder, &key_ty, true, false);

        // In epoch >= 2.05, we generate a local to compute intermediary results used in the
        // cost tracking. In this case, the cost tracking charge is applied after the delete operation.
        // In epoch < 2.05, the charge is immediately computed like it is in the interpreter.
        let post205_cost_local = if generator.contract_analysis.epoch >= StacksEpochId::Epoch2_05 {
            let l = generator.borrow_local(ValType::I32);
            Some(l)
        } else {
            let contract_analysis = generator.contract_analysis_original.clone();
            let (key_ty, value_ty) = get_original_types(&contract_analysis, name)?;
            charge_default_cost_value_and_key_size(value_ty, key_ty, generator, builder, self)?;
            None
        };

        // Push the key to the data stack
        generator.set_expr_type(key, key_ty.clone())?;
        generator.traverse_expr(builder, key)?;

        if let Some(cost_local) = &post205_cost_local {
            generator.serialization_size(builder, &key_ty)?;
            builder.local_set(**cost_local);
        }

        // Write the key to the memory (it's already on the data stack)
        let key_size = generator.write_to_memory(builder, key_offset, 0, &key_ty)?;

        // Push the key offset and size to the data stack
        builder.local_get(key_offset).i32_const(key_size as i32);

        // Create space on the call stack to write the value
        let (val_offset, _) = generator.create_call_stack_local(builder, &value_type, true, false);

        // Push the value to the data stack
        generator.set_expr_type(value, value_type.clone())?;
        generator.traverse_expr(builder, value)?;
        // for epoch >= 2.05, we compute the serialization size of the key.
        let post205_serialized_sized_value_local = if post205_cost_local.is_some() {
            let l = generator.borrow_local(ValType::I32);
            generator.serialization_size(builder, &value_type)?;
            builder.local_set(*l);
            Some(l)
        } else {
            None
        };

        // Write the value to the memory (it's already on the data stack)
        let val_size = generator.write_to_memory(builder, val_offset, 0, &value_type)?;

        // Push the value offset and size to the data stack
        builder.local_get(val_offset).i32_const(val_size as i32);

        // Call the host interface function, `map_set`
        builder.call(generator.func_by_name("stdlib.map_insert"));

        let block_ty = InstrSeqType::new(
            &mut generator.module.types,
            &[ValType::I32],
            &[ValType::I32],
        );

        // In > 2.05 we have three different costs depending if
        //      - an error occurred in the interpreter
        //      - no error occurred
        //          - and the value the operation is performed on is found
        //          - and the value the operation is performed on is not found
        let success_block_id = {
            // When the linked operation does not fail due to an interpreter error
            let mut success_block = builder.dangling_instr_seq(block_ty);
            if let (Some(cost_local), Some(value_serialized_size_local)) =
                (&post205_cost_local, &post205_serialized_sized_value_local)
            {
                let entry_status = generator.borrow_local(ValType::I32);
                // The cost in < 2.05 has already been handled before
                success_block.local_tee(*entry_status).if_else(
                    None,
                    |then| {
                        // When the element the operation is performed on was found in the map
                        // Then we charge the serialized size of the entry we want to store + serialized size of the key
                        then.local_get(**cost_local)
                            .local_get(**value_serialized_size_local)
                            .binop(BinaryOp::I32Add)
                            .local_set(**cost_local);
                    },
                    |_| {
                        // When the element the operation is performed on was not found in the map
                        // Then we only charge the serialized size of the key which is already stored in cost_local
                    },
                );
                self.charge(generator, &mut success_block, **cost_local)?;
                success_block.local_get(*entry_status);
            }
            success_block.id()
        };

        let error_block_id = {
            // When the linked operation fails due to an interpreter error
            let mut error_block = builder.dangling_instr_seq(None);
            if post205_cost_local.is_some() {
                let contract_analysis = generator.contract_analysis_original.clone();
                let (key_ty, value_ty) = get_original_types(&contract_analysis, name)?;
                charge_default_cost_value_and_key_size(
                    value_ty,
                    key_ty,
                    generator,
                    &mut error_block,
                    self,
                )?;
            }

            // Throws back the runtime error that occurred in the interpreter after charging the cost
            error_block
                .i32_const(ErrorMap::ExternError as i32)
                .call(generator.func_by_name("stdlib.runtime-error"));

            error_block.id()
        };

        builder
            .global_get(generator.linked_error)
            .ref_is_null()
            .instr(IfElse {
                consequent: success_block_id,
                alternative: error_block_id,
            });

        Ok(())
    }
}

#[derive(Debug)]
pub struct MapDelete;

impl Word for MapDelete {
    fn name(&self) -> ClarityName {
        "map-delete".into()
    }
}

impl ComplexWord for MapDelete {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 2, args.len(), ArgumentCountCheck::Exact);

        let name = args.get_name(0)?;
        let key = args.get_expr(1)?;

        let (key_ty, _) = generator
            .maps_types
            .get(name)
            .ok_or_else(|| {
                GeneratorError::TypeError("Types should have been set in map creation".to_owned())
            })?
            .clone();

        // This will compute the key type size and charge on it. If this operation fails,
        // we still need to be able to compile the contract, so we generate a runtime error.
        let charge_default_cost_key_size = |generator: &mut WasmGenerator,
                                            builder: &mut walrus::InstrSeqBuilder,
                                            key_type: &TypeSignature,
                                            word: &dyn ComplexWord|
         -> Result<(), GeneratorError> {
            // The two cases it is used in are:
            // 1) for cost computation in epoch < 2.05
            // 2) for cost computation in case of an interpreter error in epoch >= 2.05
            match key_type.size() {
                Ok(key_size) => {
                    word.charge(generator, builder, key_size)?;
                }
                Err(_) => {
                    builder
                        .i32_const(ErrorMap::SignatureTypeSizeCheckError as i32)
                        .call(generator.func_by_name("stdlib.runtime-error"));
                }
            }
            Ok(())
        };

        // In epoch >= 2.05, we generate a local to compute intermediary results used in the
        // cost tracking. In this case, the cost tracking charge is applied after the delete operation.
        // In epoch < 2.05, the charge is immediately computed like it is in the interpreter.
        let post205_cost_local = if generator.contract_analysis.epoch >= StacksEpochId::Epoch2_05 {
            let l = generator.borrow_local(ValType::I32);
            Some(l)
        } else {
            let contract_analysis = generator.contract_analysis_original.clone();
            let (key_ty, _) = get_original_types(&contract_analysis, name)?;
            charge_default_cost_key_size(generator, builder, key_ty, self)?;
            None
        };

        // Get the offset and length for this identifier in the literal memory
        let id_offset = *generator
            .literal_memory_offset
            .get(&LiteralMemoryEntry::Ascii(name.as_str().into()))
            .ok_or_else(|| GeneratorError::InternalError(format!("map not found: {name}")))?;

        let id_length = name.len();

        // Push the identifier offset and length onto the data stack
        builder
            .i32_const(id_offset as i32)
            .i32_const(id_length as i32);

        // Create space on the call stack to write the key
        let (key_offset, _) = generator.create_call_stack_local(builder, &key_ty, true, false);

        // Push the key to the data stack
        generator.set_expr_type(key, key_ty.clone())?;
        generator.traverse_expr(builder, key)?;

        // for epoch >= 2.05, we compute the serialization size of the key.
        if let Some(cost_local) = &post205_cost_local {
            generator.serialization_size(builder, &key_ty)?;
            builder.local_set(**cost_local);
        }

        // Write the key to the memory (it's already on the data stack)
        let key_size = generator.write_to_memory(builder, key_offset, 0, &key_ty)?;

        // Push the key offset and size to the data stack
        builder.local_get(key_offset).i32_const(key_size as i32);

        // Call the host interface function, `map_delete`
        builder.call(generator.func_by_name("stdlib.map_delete"));

        let result = generator.borrow_local(ValType::I32);
        builder.local_set(*result);

        // In > 2.05 we have three different costs depending if
        //      - an error occurred in the interpreter
        //      - no error occurred
        //          - and the value the operation is performed on is found
        //          - and the value the operation is performed on is not found
        let success_block_id = {
            // When the linked operation does not fail due to an interpreter error
            let mut success_block = builder.dangling_instr_seq(None);

            if let Some(cost_local) = &post205_cost_local {
                // the cost here will be the serialization size of the key (already in cost_local)
                //  + the size of a None if the operation succeeds. Fortunately, this size is 1 when
                // a value is found, which is the same as the value inside result. If no value was
                // deleted, we add 0, which is the value of result.
                success_block
                    .local_get(**cost_local)
                    .local_get(*result)
                    .binop(BinaryOp::I32Add)
                    .local_set(**cost_local);
                self.charge(generator, &mut success_block, **cost_local)?;
            }

            success_block.id()
        };

        let error_block_id = {
            // When the linked operation fails due to an interpreter error
            let mut error_block = builder.dangling_instr_seq(None);

            // in epoch >= 2.05, we charge depending on the size of the key.
            if post205_cost_local.is_some() {
                let contract_analysis = generator.contract_analysis_original.clone();
                let (key_ty, _) = get_original_types(&contract_analysis, name)?;
                charge_default_cost_key_size(generator, &mut error_block, key_ty, self)?;
            }

            // Throws back the runtime error that occurred in the interpreter after charging the cost
            error_block
                .i32_const(ErrorMap::ExternError as i32)
                .call(generator.func_by_name("stdlib.runtime-error"));

            error_block.id()
        };

        builder
            .global_get(generator.linked_error)
            .ref_is_null()
            .instr(IfElse {
                consequent: success_block_id,
                alternative: error_block_id,
            });

        builder.local_get(*result);

        Ok(())
    }
}

/// helper function to compute the cost of value and key type sizes
/// This function charges the the size of the value type + the size of the key type (non serialized)
/// It is used for Get, Insert,and Set functions
/// The two cases it is used in are:
/// 1) for cost computation in epoch < 2.05
/// 2) for cost computation in case of an interpreter error in epoch >= 2.05
fn charge_default_cost_value_and_key_size(
    value_type: &TypeSignature,
    key_type: &TypeSignature,
    generator: &mut WasmGenerator,
    builder: &mut walrus::InstrSeqBuilder,
    word: &dyn ComplexWord,
) -> Result<(), GeneratorError> {
    match (value_type.size(), key_type.size()) {
        (Ok(value_size), Ok(key_size)) => {
            word.charge(generator, builder, value_size + key_size)?;
        }
        (_, Err(_)) | (Err(_), _) => {
            builder
                .i32_const(ErrorMap::SignatureTypeSizeCheckError as i32)
                .call(generator.func_by_name("stdlib.runtime-error"));
        }
    }
    Ok(())
}

fn get_original_types<'a>(
    contract_analysis: &'a ContractAnalysis,
    name: &str,
) -> Result<&'a (TypeSignature, TypeSignature), GeneratorError> {
    contract_analysis.get_map_type(name).ok_or_else(|| {
        GeneratorError::TypeError("Types should have been set in contract analysis".to_owned())
    })
}

#[cfg(test)]
mod tests {
    // use clarity::vm::errors::{CheckErrors, Error};

    use clarity::vm::errors::{CheckErrors, Error};
    use clarity::vm::Value;

    use crate::tools::{crosscheck, crosscheck_expect_failure, evaluate};

    //
    // Module with tests that should only be executed
    // when running Clarity::V1.
    //
    #[cfg(feature = "test-clarity-v1")]
    mod clarity_v1 {
        use clarity::types::StacksEpochId;

        use crate::tools::crosscheck_with_epoch;

        #[test]
        fn validate_define_map_epoch() {
            // Epoch
            crosscheck_with_epoch(
                "(define-map index-of? {x: int} {square: int})",
                Ok(None),
                StacksEpochId::Epoch20,
            );
        }
    }

    #[test]
    fn map_define_get() {
        crosscheck(
            r#"(define-map counters principal uint) (map-get? counters tx-sender)"#,
            Ok(Some(Value::none())),
        )
    }

    #[test]
    fn map_define_set() {
        crosscheck("(define-map approved-contracts principal bool) (map-set approved-contracts tx-sender true)", Ok(Some(Value::Bool(true))));
    }

    #[test]
    fn map_define_insert() {
        crosscheck("(define-map approved-contracts principal bool) (map-insert approved-contracts tx-sender true)", Ok(Some(Value::Bool(true))));
    }

    #[test]
    fn map_define_set_delete() {
        crosscheck("(define-map approved-contracts principal bool) (map-insert approved-contracts tx-sender true) (map-delete approved-contracts tx-sender)", Ok(Some(Value::Bool(true))));
    }

    #[test]
    fn map_define_set_get() {
        crosscheck("(define-map approved-contracts principal bool) (map-insert approved-contracts tx-sender true) (map-get? approved-contracts tx-sender)", Ok(Some(Value::some(Value::Bool(true)).unwrap())));
    }

    #[test]
    fn validate_define_map() {
        // Reserved keyword
        crosscheck_expect_failure("(define-map map {x: int} {square: int})");

        // Custom map name
        crosscheck("(define-map a {x: int} {square: int})", Ok(None));

        // Custom map name duplicate
        crosscheck_expect_failure(
            "(define-map a {x: int} {square: int}) (define-map a {x: int} {square: int})",
        );
    }

    #[test]
    fn define_map_less_than_three_args() {
        let result = evaluate("(define-map some-map)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 3 arguments, got 1"));
    }

    #[test]
    fn define_map_more_than_three_args() {
        let result = evaluate("(define-map some-map int 5 6)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 3 arguments, got 4"));
    }

    #[test]
    fn map_get_less_than_two_args() {
        let result = evaluate("(map-get? some-map)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 1"));
    }

    #[test]
    fn map_set_less_than_two_args() {
        let result = evaluate("(map-set some-map)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting >= 3 arguments, got 1"));
    }

    #[test]
    fn map_insert_less_than_two_args() {
        let result = evaluate("(map-insert some-map)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting >= 3 arguments, got 1"));
    }

    #[test]
    fn map_delete_less_than_two_args() {
        let snippet = "
        (define-map some-map int {x: int})
        (map-insert some-map 21 {x: 21})
        (map-delete some-map)";
        let result = evaluate(snippet);
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting >= 2 arguments, got 1"));
    }

    #[test]
    fn map_get_more_than_two_args() {
        let snippet = "
        (define-map some-map int {x: int})
        (map-insert some-map 21 {x: 21})
        (map-get? some-map 21 21)";
        let result = evaluate(snippet);
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 3"));
    }

    #[test]
    fn map_set_more_than_two_args() {
        // TODO: see issue #488
        // The inconsistency in function arguments should have been caught by the typechecker.
        // The runtime error below is being used as a workaround for a typechecker issue
        // where certain errors are not properly handled.
        // This test should be re-worked once the typechecker is fixed
        // and can correctly detect all argument inconsistencies.
        let snippet = "(define-map some-map int {x: int})
        (map-set some-map 21 {x: 21} {x: 21})";
        let expected = Err(Error::Unchecked(CheckErrors::IncorrectArgumentCount(3, 4)));
        crosscheck(snippet, expected);
    }

    #[test]
    fn map_insert_more_than_three_args() {
        // TODO: see issue #488
        // The inconsistency in function arguments should have been caught by the typechecker.
        // The runtime error below is being used as a workaround for a typechecker issue
        // where certain errors are not properly handled.
        // This test should be re-worked once the typechecker is fixed
        // and can correctly detect all argument inconsistencies.
        let snippet = "
        (define-map some-map int {x: int})
        (map-insert some-map 21 {x: 21} {x: 21})";
        let expected = Err(Error::Unchecked(CheckErrors::IncorrectArgumentCount(3, 4)));
        crosscheck(snippet, expected);
    }

    #[test]
    fn map_delete_more_than_two_args() {
        // TODO: see issue #488
        // The inconsistency in function arguments should have been caught by the typechecker.
        // The runtime error below is being used as a workaround for a typechecker issue
        // where certain errors are not properly handled.
        // This test should be re-worked once the typechecker is fixed
        // and can correctly detect all argument inconsistencies.
        let snippet = "
        (define-map some-map int {x: int})
        (map-insert some-map 21 {x: 21})
        (map-delete some-map 21 21)";
        let expected = Err(Error::Unchecked(CheckErrors::IncorrectArgumentCount(2, 3)));
        crosscheck(snippet, expected);
    }
}
