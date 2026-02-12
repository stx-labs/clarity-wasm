use clarity::types::StacksEpochId;
use clarity::vm::types::{TypeSignature, TypeSignatureExt};
use clarity::vm::{ClarityName, SymbolicExpression};
use walrus::ir::{BinaryOp, IfElse, InstrSeqType};
use walrus::ValType;

use super::{ComplexWord, Word};
use crate::check_args;
use crate::cost::WordCharge;
use crate::error_mapping::ErrorMap;
use crate::wasm_generator::{ArgumentsExt, GeneratorError, LiteralMemoryEntry, WasmGenerator};
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

        let (key_ty, value_type) = generator
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

        let (key_offset, key_size) =
            generator.create_call_stack_local(builder, &key_ty, true, false);

        // Push the key to the data stack
        generator.set_expr_type(key, key_ty.clone())?;
        generator.traverse_expr(builder, key)?;
        let serialized_key_size = generator.borrow_local(ValType::I32);
        if generator.contract_analysis.epoch >= StacksEpochId::Epoch2_05 {
            // in this case we need to compute the serialized key size
            generator.serialization_size(builder, &key_ty)?;
            builder.local_set(*serialized_key_size);
        }

        // Write the key to the memory (it's already on the data stack)
        generator.write_to_memory(builder, key_offset, 0, &key_ty)?;

        // Push the key offset and size to the data stack
        builder.local_get(key_offset).i32_const(key_size);

        let value_type = TypeSignature::OptionalType(Box::new(value_type));
        let (return_offset, size) =
            generator.create_call_stack_local(builder, &value_type, true, true);

        let return_size = generator.module.locals.add(ValType::I32);
        builder.i32_const(size).local_set(return_size);

        // Push the return value offset and size to the data stack
        builder.local_get(return_offset).local_get(return_size);

        // Call the host-interface function, `map_get`
        builder.call(generator.func_by_name("stdlib.map_get"));
        let entry_status = generator.borrow_local(ValType::I32);
        builder.local_set(*entry_status);

        // Host interface fills the result into the specified memory. Read it
        // back out, and place the value on the data stack.
        generator.read_from_memory(builder, return_offset, 0, &value_type)?;

        let serialize_size = generator.borrow_local(ValType::I32);
        if generator.contract_analysis.epoch >= StacksEpochId::Epoch2_05 {
            generator.serialization_size(builder, &value_type)?;
            builder.local_set(*serialize_size);
        }

        let block_ty = InstrSeqType::new(&mut generator.module.types, &[], &[]);

        let error_block_id = {
            let mut error_block = builder.dangling_instr_seq(block_ty);
            if generator.contract_analysis.epoch >= StacksEpochId::Epoch2_05 {
                let cost = generator.borrow_local(ValType::I32);
                error_block
                    .local_get(return_size)
                    .i32_const(key_size)
                    .binop(BinaryOp::I32Add)
                    .local_set(*cost);
                self.charge(generator, &mut error_block, *cost)?;
            }
            error_block
                .i32_const(ErrorMap::ExternError as i32)
                .call(generator.func_by_name("stdlib.runtime-error"));
            error_block.id()
        };

        let success_block_id = {
            let cost = generator.borrow_local(ValType::I32);
            let mut success_block = builder.dangling_instr_seq(block_ty);
            if generator.contract_analysis.epoch < StacksEpochId::Epoch2_05 {
                success_block
                    .local_get(return_size)
                    .i32_const(key_size)
                    .binop(BinaryOp::I32Add)
                    .local_set(*cost);
            } else {
                let found_block_id = {
                    let mut found_block = success_block.dangling_instr_seq(block_ty);
                    found_block
                        .local_get(*serialize_size)
                        .local_get(*serialized_key_size)
                        .binop(BinaryOp::I32Add)
                        .local_set(*cost);
                    found_block.id()
                };

                let not_found_block_id = {
                    let mut not_found_block = success_block.dangling_instr_seq(block_ty);
                    not_found_block
                        .local_get(*serialized_key_size)
                        .local_set(*cost);
                    not_found_block.id()
                };

                success_block
                    .local_get(*serialize_size)
                    // Size of none
                    .i32_const(1)
                    .binop(BinaryOp::I32Ne);
                success_block.instr(IfElse {
                    consequent: found_block_id,
                    alternative: not_found_block_id,
                });
            }
            self.charge(generator, &mut success_block, *cost)?;
            success_block.id()
        };

        builder.local_get(*entry_status);
        builder
            .i32_const(-1i32)
            .binop(BinaryOp::I32Ne)
            .instr(IfElse {
                consequent: success_block_id,
                alternative: error_block_id,
            });

        Ok(())
    }
}

enum StoreType {
    Insert,
    Set,
}
/// Trait that rassemble the traverse code of set and insert
trait StoreWord: ComplexWord {
    fn traverse_store(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
        put_type: StoreType,
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

        let (key_offset, key_size) =
            generator.create_call_stack_local(builder, &key_ty, true, false);

        // Push the key to the data stack
        generator.set_expr_type(key, key_ty.clone())?;
        generator.traverse_expr(builder, key)?;

        let serialized_key_size = generator.borrow_local(ValType::I32);
        if generator.contract_analysis.epoch >= StacksEpochId::Epoch2_05 {
            // in this case we need to compute the serialized key size
            generator.serialization_size(builder, &key_ty)?;
            builder.local_set(*serialized_key_size);
        }

        // Write the key to the memory (it's already on the data stack)
        generator.write_to_memory(builder, key_offset, 0, &key_ty)?;

        // Push the key offset and size to the data stack
        builder.local_get(key_offset).i32_const(key_size);

        // Create space on the call stack to write the value
        let (val_offset, size) =
            generator.create_call_stack_local(builder, &value_type, true, false);

        let val_size = generator.borrow_local(ValType::I32);
        builder.i32_const(size).local_set(*val_size);

        // Push the value to the data stack
        generator.set_expr_type(value, value_type.clone())?;
        generator.traverse_expr(builder, value)?;
        let value_serialized_size = generator.borrow_local(ValType::I32);
        if generator.contract_analysis.epoch >= StacksEpochId::Epoch2_05 {
            generator.serialization_size(builder, &value_type)?;
            builder.local_set(*value_serialized_size);
        }

        // Write the value to the memory (it's already on the data stack)
        generator.write_to_memory(builder, val_offset, 0, &value_type)?;

        // Push the value offset and size to the data stack
        builder.local_get(val_offset).local_get(*val_size);

        // Call the host interface function, `map_set`
        builder.call(generator.func_by_name(match put_type {
            StoreType::Set => "stdlib.map_set",
            StoreType::Insert => "stdlib.map_insert",
        }));

        let entry_status = generator.borrow_local(ValType::I32);
        let block_ty = InstrSeqType::new(&mut generator.module.types, &[], &[]);

        let error_block_id = {
            let mut error_block = builder.dangling_instr_seq(block_ty);

            if generator.contract_analysis.epoch >= StacksEpochId::Epoch2_05 {
                let cost = generator.borrow_local(ValType::I32);
                error_block
                    .local_get(*val_size)
                    .i32_const(key_size)
                    .binop(BinaryOp::I32Add)
                    .local_set(*cost);
                self.charge(generator, &mut error_block, *cost)?;
            }

            error_block
                .i32_const(ErrorMap::ExternError as i32)
                .call(generator.func_by_name("stdlib.runtime-error"));

            error_block.id()
        };

        let success_block_id = {
            let mut success_block = builder.dangling_instr_seq(block_ty);
            let cost = generator.borrow_local(ValType::I32);

            if generator.contract_analysis.epoch < StacksEpochId::Epoch2_05 {
                success_block
                    .i32_const(size)
                    .i32_const(key_size)
                    .binop(BinaryOp::I32Add)
                    .local_set(*cost);
            } else {
                success_block
                    .local_get(*serialized_key_size)
                    .local_set(*cost);

                let found_block_id = {
                    let mut found_block = success_block.dangling_instr_seq(block_ty);
                    found_block
                        .local_get(*value_serialized_size)
                        .local_get(*cost)
                        .binop(BinaryOp::I32Add)
                        .local_set(*cost);

                    found_block.id()
                };
                let not_found_block_id = {
                    let not_found_block = success_block.dangling_instr_seq(block_ty);
                    not_found_block.id()
                };

                success_block.local_get(*entry_status).instr(IfElse {
                    consequent: found_block_id,
                    alternative: not_found_block_id,
                });
            }
            self.charge(generator, &mut success_block, *cost)?;
            success_block.id()
        };

        builder
            .local_tee(*entry_status)
            .i32_const(-1i32)
            .binop(BinaryOp::I32Ne)
            .instr(IfElse {
                consequent: success_block_id,
                alternative: error_block_id,
            });
        builder.local_get(*entry_status);

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

impl StoreWord for MapSet {}

impl ComplexWord for MapSet {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        self.traverse_store(generator, builder, _expr, args, StoreType::Set)
    }
}

#[derive(Debug)]
pub struct MapInsert;

impl StoreWord for MapInsert {}

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
        self.traverse_store(generator, builder, _expr, args, StoreType::Insert)
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
        let (key_offset, size) = generator.create_call_stack_local(builder, &key_ty, true, false);

        let key_size = generator.borrow_local(ValType::I32);
        builder.i32_const(size).local_set(*key_size);

        // Push the key to the data stack
        generator.set_expr_type(key, key_ty.clone())?;
        generator.traverse_expr(builder, key)?;
        let serialize_size = generator.borrow_local(ValType::I32);
        if generator.contract_analysis.epoch >= StacksEpochId::Epoch2_05 {
            generator.serialization_size(builder, &key_ty)?;
            builder.local_set(*serialize_size);
        }

        // Write the key to the memory (it's already on the data stack)
        generator.write_to_memory(builder, key_offset, 0, &key_ty)?;

        // Push the key offset and size to the data stack
        builder.local_get(key_offset).local_get(*key_size);

        // Call the host interface function, `map_delete`
        builder.call(generator.func_by_name("stdlib.map_delete"));

        let entry_status = generator.borrow_local(ValType::I32);
        builder.local_set(*entry_status);

        let block_ty = InstrSeqType::new(&mut generator.module.types, &[], &[]);
        let error_block_id = {
            let mut error_block = builder.dangling_instr_seq(block_ty);
            if generator.contract_analysis.epoch > StacksEpochId::Epoch2_05 {
                self.charge(generator, &mut error_block, *key_size)?;
            }

            error_block
                .i32_const(ErrorMap::ExternError as i32)
                .call(generator.func_by_name("stdlib.runtime-error"));

            error_block.id()
        };

        let success_block_id = {
            let mut success_block = builder.dangling_instr_seq(block_ty);

            if generator.contract_analysis.epoch < StacksEpochId::Epoch2_05 {
                self.charge(generator, &mut success_block, *key_size)?;
            } else {
                let entry_existed_block_id = {
                    let mut entry_existed_block = success_block.dangling_instr_seq(block_ty);
                    let cost = generator.borrow_local(ValType::I32);
                    //Size of None is 1
                    entry_existed_block
                        .local_get(*serialize_size)
                        .i32_const(1)
                        .binop(BinaryOp::I32Add)
                        .local_set(*cost);
                    self.charge(generator, &mut entry_existed_block, *cost)?;
                    entry_existed_block.id()
                };

                let entry_did_not_exist_block_id = {
                    let mut entry_did_not_exist_block = success_block.dangling_instr_seq(block_ty);
                    self.charge(generator, &mut entry_did_not_exist_block, *serialize_size)?;
                    entry_did_not_exist_block.id()
                };

                success_block.local_get(*entry_status).instr(IfElse {
                    consequent: entry_existed_block_id,
                    alternative: entry_did_not_exist_block_id,
                });
            }
            success_block.id()
        };

        builder.local_get(*entry_status);
        builder
            .i32_const(-1i32)
            .binop(BinaryOp::I32Ne)
            .instr(IfElse {
                consequent: success_block_id,
                alternative: error_block_id,
            });

        builder.local_get(*entry_status);

        Ok(())
    }
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
