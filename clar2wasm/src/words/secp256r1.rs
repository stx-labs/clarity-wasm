use clarity_types::ClarityName;
use walrus::ir::{BinaryOp, Block};
use walrus::ValType;

use crate::check_args;
use crate::error_mapping::ErrorMap;
use crate::wasm_generator::GeneratorError;
use crate::wasm_utils::get_global;
use crate::words::{ComplexWord, Word};

#[derive(Debug)]
pub struct Verify;

impl Word for Verify {
    fn name(&self) -> clarity_types::ClarityName {
        ClarityName::from_literal("secp256r1-verify")
    }
}

impl ComplexWord for Verify {
    fn traverse(
        &self,
        generator: &mut crate::wasm_generator::WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &clarity::vm::SymbolicExpression,
        args: &[clarity::vm::SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(
            generator,
            builder,
            3,
            args.len(),
            crate::wasm_utils::ArgumentCountCheck::Exact
        );

        let [message_hash, signature, public_key] = args else {
            unreachable!()
        };

        let verify_function = generator.func_by_name(
            if generator
                .contract_analysis
                .clarity_version
                .uses_secp256r1_double_hashing()
            {
                "stdlib.secp256r1_verify_double_hash"
            } else {
                "stdlib.secp256r1_verify_simple_hash"
            },
        );

        let outer_block_id = {
            let mut outer_block = builder.dangling_instr_seq(ValType::I32);
            let outer_block_id = outer_block.id();

            let expected_buffer_size = generator.borrow_local(ValType::I32);
            let actual_buffer_offset = generator.borrow_local(ValType::I32);
            let actual_buffer_size = generator.borrow_local(ValType::I32);

            let inner_block_id = {
                let mut inner_block = outer_block.dangling_instr_seq(None);
                let inner_block_id = inner_block.id();

                // handling message hash
                generator.traverse_expr(&mut inner_block, message_hash)?;
                inner_block
                    .local_set(*actual_buffer_size)
                    .local_set(*actual_buffer_offset);
                inner_block.i32_const(32).local_set(*expected_buffer_size);
                inner_block
                    .local_get(*expected_buffer_size)
                    .local_get(*actual_buffer_size)
                    .binop(BinaryOp::I32Ne)
                    .br_if(inner_block_id);
                inner_block
                    .local_get(*actual_buffer_offset)
                    .local_get(*actual_buffer_size);

                // handling signature
                generator.traverse_expr(&mut inner_block, signature)?;
                inner_block
                    .local_set(*actual_buffer_size)
                    .local_set(*actual_buffer_offset);
                inner_block.i32_const(64).local_set(*expected_buffer_size);
                inner_block
                    .local_get(*expected_buffer_size)
                    .local_get(*actual_buffer_size)
                    .binop(BinaryOp::I32LtU)
                    .br_if(inner_block_id);
                // if signature size is different from 64, it's an automatic false result
                inner_block
                    .local_get(*expected_buffer_size)
                    .local_get(*actual_buffer_size)
                    .binop(BinaryOp::I32Ne)
                    .if_else(
                        None,
                        |then| {
                            // we push a false
                            then.i32_const(0);
                            // we branch to the end of the computation: branching
                            // to the (i32-typed) outer block keeps the false we
                            // just pushed and unwinds the message hash offset and
                            // size still sitting on the stack.
                            then.br(outer_block_id);
                        },
                        |_else| {},
                    );
                inner_block
                    .local_get(*actual_buffer_offset)
                    .local_get(*actual_buffer_size);

                // handling public key
                generator.traverse_expr(&mut inner_block, public_key)?;
                inner_block
                    .local_set(*actual_buffer_size)
                    .local_set(*actual_buffer_offset);
                inner_block.i32_const(33).local_set(*expected_buffer_size);
                inner_block
                    .local_get(*expected_buffer_size)
                    .local_get(*actual_buffer_size)
                    .binop(BinaryOp::I32Ne)
                    .br_if(inner_block_id);
                inner_block
                    .local_get(*actual_buffer_offset)
                    .local_get(*actual_buffer_size);

                // calling the secp256r1 verify function
                inner_block.call(verify_function);

                // we can now go to the end of the computation
                inner_block.br(outer_block_id);

                inner_block_id
            };

            outer_block.instr(Block {
                seq: inner_block_id,
            });

            // if we arrive here, we have to throw a runtime error.
            outer_block
                .local_get(*expected_buffer_size)
                .global_set(get_global(&generator.module, "runtime-error-value-offset")?);
            outer_block
                .local_get(*actual_buffer_offset)
                .global_set(get_global(&generator.module, "runtime-error-arg-offset")?);
            outer_block
                .local_get(*actual_buffer_size)
                .global_set(get_global(&generator.module, "runtime-error-arg-len")?);
            outer_block
                .i32_const(ErrorMap::IncorrectBufferSize as i32)
                .call(generator.func_by_name("stdlib.runtime-error"));

            outer_block.unreachable();

            outer_block_id
        };

        builder.instr(Block {
            seq: outer_block_id,
        });

        Ok(())
    }
}
