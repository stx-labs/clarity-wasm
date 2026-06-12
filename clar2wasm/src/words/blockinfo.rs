use clarity::vm::{ClarityName, SymbolicExpression};
use walrus::ir::{Block, InstrSeqType};

use super::{ComplexWord, Word};
use crate::check_args;
use crate::cost::WordCharge;
use crate::wasm_generator::{clar2wasm_ty, ArgumentsExt, GeneratorError, WasmGenerator};
use crate::wasm_utils::ArgumentCountCheck;

#[derive(Debug)]
pub struct GetBlockInfo;

impl Word for GetBlockInfo {
    fn name(&self) -> ClarityName {
        ClarityName::from_literal("get-block-info?")
    }
}

impl ComplexWord for GetBlockInfo {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 2, args.len(), ArgumentCountCheck::Exact);

        self.charge(generator, builder, 0)?;

        let prop_name = args.get_name(0)?;
        let block = args.get_expr(1)?;

        // Push the block number onto the stack
        generator.traverse_expr(builder, block)?;

        // Reserve space on the stack for the return value
        let return_ty = generator
            .get_expr_type(expr)
            .ok_or_else(|| {
                GeneratorError::TypeError("get-block-info? expression must be typed".to_owned())
            })?
            .clone();

        let (return_offset, return_size) =
            generator.create_call_stack_local(builder, &return_ty, true, true);

        // Push the offset and size to the data stack
        builder.local_get(return_offset).i32_const(return_size);
        // Parse the property name at compile time
        match prop_name.as_str() {
            "time" => {
                builder.call(generator.func_by_name("stdlib.get_block_info_time_property"));
            }
            "header-hash" => {
                builder.call(generator.func_by_name("stdlib.get_block_info_header_hash_property"));
            }
            "burnchain-header-hash" => {
                builder.call(
                    generator.func_by_name("stdlib.get_block_info_burnchain_header_hash_property"),
                );
            }
            "id-header-hash" => {
                builder.call(
                    generator.func_by_name("stdlib.get_block_info_identity_header_hash_property"),
                );
            }
            "miner-address" => {
                builder
                    .call(generator.func_by_name("stdlib.get_block_info_miner_address_property"));
            }
            "block-reward" => {
                builder.call(generator.func_by_name("stdlib.get_block_info_block_reward_property"));
            }
            "miner-spend-total" => {
                builder.call(
                    generator.func_by_name("stdlib.get_block_info_miner_spend_total_property"),
                );
            }
            "miner-spend-winner" => {
                builder.call(
                    generator.func_by_name("stdlib.get_block_info_miner_spend_winner_property"),
                );
            }
            "vrf-seed" => {
                builder.call(generator.func_by_name("stdlib.get_block_info_vrf_seed_property"));
            }
            _ => {
                return Err(GeneratorError::InternalError(format!(
                    "{self:?} does not have a property of type {prop_name}"
                )))
            }
        };

        generator.read_from_memory(builder, return_offset, 0, &return_ty)?;

        Ok(())
    }
}

#[derive(Debug)]
pub struct GetBurnBlockInfo;

impl Word for GetBurnBlockInfo {
    fn name(&self) -> ClarityName {
        ClarityName::from_literal("get-burn-block-info?")
    }
}

impl ComplexWord for GetBurnBlockInfo {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 2, args.len(), ArgumentCountCheck::Exact);

        self.charge(generator, builder, 0)?;

        let prop_name = args.get_name(0)?;
        let block = args.get_expr(1)?;

        // Push the block number onto the stack
        generator.traverse_expr(builder, block)?;

        // Reserve space on the stack for the return value
        let return_ty = generator
            .get_expr_type(expr)
            .ok_or_else(|| {
                GeneratorError::TypeError(
                    "get-burn-block-info? expression must be typed".to_owned(),
                )
            })?
            .clone();

        let (return_offset, return_size) =
            generator.create_call_stack_local(builder, &return_ty, true, true);

        // Push the offset and size to the data stack
        builder.local_get(return_offset).i32_const(return_size);

        match prop_name.as_str() {
            "header-hash" => {
                builder.call(
                    generator.func_by_name("stdlib.get_burn_block_info_header_hash_property"),
                );
            }
            "pox-addrs" => {
                builder
                    .call(generator.func_by_name("stdlib.get_burn_block_info_pox_addrs_property"));
            }
            _ => {
                return Err(GeneratorError::InternalError(format!(
                    "{self:?} does not have a property of type {prop_name}"
                )))
            }
        };

        // Host interface fills the result into the specified memory. Read it
        // back out, and place the value on the data stack.
        generator.read_from_memory(builder, return_offset, 0, &return_ty)?;

        Ok(())
    }
}

#[derive(Debug)]
pub struct AtBlock;

impl Word for AtBlock {
    fn name(&self) -> ClarityName {
        ClarityName::from_literal("at-block")
    }
}

impl ComplexWord for AtBlock {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 2, args.len(), ArgumentCountCheck::Exact);

        let ty = generator.get_expr_type(expr).cloned().ok_or_else(|| {
            GeneratorError::TypeError("at-block expression should be typed".to_owned())
        })?;
        let wasm_ty = InstrSeqType::new(&mut generator.module.types, &[], &clar2wasm_ty(&ty));

        self.charge(generator, builder, 0)?;

        let block_hash = args.get_expr(0)?;
        let e = args.get_expr(1)?;
        generator.set_expr_type(e, ty)?;

        let e_block_id = {
            let mut e_block = builder.dangling_instr_seq(wasm_ty);
            let e_block_id = e_block.id();

            let fail_block_ty = match generator
                .get_current_function_return_type()
                .map(clar2wasm_ty)
            {
                Some(wasm_ty) => InstrSeqType::new(&mut generator.module.types, &[], &wasm_ty),
                None => None.into(),
            };
            let fail_block_id = {
                let mut fail_block = e_block.dangling_instr_seq(fail_block_ty);
                let fail_block_id = fail_block.id();

                let former_early_return = generator.early_return_block_id.replace(fail_block_id);

                // Traverse the block_hash, leaving it on the top of the stack
                generator.traverse_expr(&mut fail_block, block_hash)?;

                // Call the host interface function, `enter_at_block`
                fail_block.call(generator.func_by_name("stdlib.enter_at_block"));

                // Traverse the inner expression
                generator.traverse_expr(&mut fail_block, e)?;

                // we can restore the original early return block now
                generator.early_return_block_id = former_early_return;

                // Everytihing went well:
                // - Call the host interface function, `exit_at_block`
                // - Branch to the outer block
                fail_block.call(generator.func_by_name("stdlib.exit_at_block"));
                fail_block.br(e_block_id);

                fail_block_id
            };

            e_block.instr(Block { seq: fail_block_id });

            // If we are here, a shortcut was triggered, we need to cleanup then jump to the original shortcut.
            if let Some(early_return) = generator.early_return_block_id {
                e_block.call(generator.func_by_name("stdlib.exit_at_block"));
                e_block.br(early_return);
            } else {
                // if we are in top-level, this will never happen
                e_block.unreachable();
            }

            e_block_id
        };

        builder.instr(Block { seq: e_block_id });

        Ok(())
    }
}

#[derive(Debug)]
pub struct GetStacksBlockInfo;

impl Word for GetStacksBlockInfo {
    fn name(&self) -> ClarityName {
        ClarityName::from_literal("get-stacks-block-info?")
    }
}

impl ComplexWord for GetStacksBlockInfo {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 2, args.len(), ArgumentCountCheck::Exact);

        self.charge(generator, builder, 0)?;

        let prop_name = args.get_name(0)?;
        let block = args.get_expr(1)?;

        // Push the block number onto the stack
        generator.traverse_expr(builder, block)?;

        // Reserve space on the stack for the return value
        let return_ty = generator
            .get_expr_type(expr)
            .ok_or_else(|| {
                GeneratorError::TypeError(
                    "get-stacks-block-info? expression must be typed".to_owned(),
                )
            })?
            .clone();

        let (return_offset, return_size) =
            generator.create_call_stack_local(builder, &return_ty, true, true);

        // Push the offset and size to the data stack
        builder.local_get(return_offset).i32_const(return_size);
        // Parse the property name at compile time
        match prop_name.as_str() {
            "header-hash" => {
                builder.call(
                    generator.func_by_name("stdlib.get_stacks_block_info_header_hash_property"),
                );
            }
            "id-header-hash" => {
                builder
                    .call(generator.func_by_name(
                        "stdlib.get_stacks_block_info_identity_header_hash_property",
                    ));
            }
            "time" => {
                builder.call(generator.func_by_name("stdlib.get_stacks_block_info_time_property"));
            }
            _ => {
                return Err(GeneratorError::InternalError(format!(
                    "{self:?} does not have a property of type {prop_name}"
                )))
            }
        };

        generator.read_from_memory(builder, return_offset, 0, &return_ty)?;

        Ok(())
    }
}

#[derive(Debug)]
pub struct GetTenureInfo;

impl Word for GetTenureInfo {
    fn name(&self) -> ClarityName {
        ClarityName::from_literal("get-tenure-info?")
    }
}

impl ComplexWord for GetTenureInfo {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 2, args.len(), ArgumentCountCheck::Exact);

        self.charge(generator, builder, 0)?;

        let prop_name = args.get_name(0)?;
        let block = args.get_expr(1)?;

        // Push the block number onto the stack
        generator.traverse_expr(builder, block)?;

        // Reserve space on the stack for the return value
        let return_ty = generator
            .get_expr_type(expr)
            .ok_or_else(|| {
                GeneratorError::TypeError("get-tenure-info? expression must be typed".to_owned())
            })?
            .clone();

        let (return_offset, return_size) =
            generator.create_call_stack_local(builder, &return_ty, true, true);

        // Push the offset and size to the data stack
        builder.local_get(return_offset).i32_const(return_size);
        // Parse the property name at compile time
        match prop_name.as_str() {
            "time" => {
                builder.call(generator.func_by_name("stdlib.get_tenure_info_time_property"));
            }
            "vrf-seed" => {
                builder.call(generator.func_by_name("stdlib.get_tenure_info_vrf_seed_property"));
            }
            "burnchain-header-hash" => {
                builder.call(
                    generator.func_by_name("stdlib.get_tenure_info_burnchain_header_hash_property"),
                );
            }
            "miner-address" => {
                builder
                    .call(generator.func_by_name("stdlib.get_tenure_info_miner_address_property"));
            }
            "block-reward" => {
                builder
                    .call(generator.func_by_name("stdlib.get_tenure_info_block_reward_property"));
            }
            "miner-spend-total" => {
                builder.call(
                    generator.func_by_name("stdlib.get_tenure_info_miner_spend_total_property"),
                );
            }
            "miner-spend-winner" => {
                builder.call(
                    generator.func_by_name("stdlib.get_tenure_info_miner_spend_winner_property"),
                );
            }
            _ => {
                return Err(GeneratorError::InternalError(format!(
                    "{self:?} does not have a property of type {prop_name}"
                )))
            }
        };

        generator.read_from_memory(builder, return_offset, 0, &return_ty)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use clarity::types::StacksEpochId;
    use clarity::vm::errors::VmExecutionError;
    use clarity::vm::types::{OptionalData, PrincipalData, TupleData};
    use clarity::vm::{ClarityVersion, Value};
    use clarity_types::ClarityName;

    use crate::tools::{evaluate, TestEnvironment};

    #[cfg(any(
        feature = "test-clarity-v1",
        feature = "test-clarity-v2",
        feature = "test-clarity-v3"
    ))]
    #[cfg(test)]
    mod clarity_v1_v2_v3 {
        use clarity::vm::errors::EarlyReturnError::UnwrapFailed;
        use clarity::vm::errors::VmExecutionError::EarlyReturn;
        use clarity_types::types::ResponseData;
        use clarity_types::Value::{self, Response};

        use crate::tools::crosscheck;

        #[test]
        #[ignore = "test system needs to be improved relative to versioning and epochs"]
        fn at_block_needs_cleanup() {
            let snippet = "
                (define-private (foo)
                    (at-block 0x0000000000000000000000000000000000000000000000000000000000000000
                        (ok (try! (if false (ok true) (err u42))))
                    )
                )
                (foo)
            ";

            crosscheck(snippet, Ok(Some(Value::err_uint(42))));
        }

        #[test]
        #[ignore = "test system needs to be improved relative to versioning and epochs"]
        fn at_block_needs_cleanup_top_level() {
            let snippet = "
                (at-block 0x0000000000000000000000000000000000000000000000000000000000000000
                    (ok (try! (if false (ok true) (err u42))))
                )
            ";

            crosscheck(
                snippet,
                Err(EarlyReturn(UnwrapFailed(Box::new(Response(
                    ResponseData {
                        committed: false,
                        data: Box::new(clarity_types::Value::UInt(42)),
                    },
                ))))),
            );
        }
    }

    //
    // Module with tests that should only be executed
    // when running Clarity::V1 or Clarity::V2.
    //
    #[cfg(any(feature = "test-clarity-v1", feature = "test-clarity-v2"))]
    #[cfg(test)]
    mod clarity_v1_v2 {
        use clarity::types::StacksEpochId;
        use clarity::vm::ClarityVersion;

        use super::*;
        use crate::tools::crosscheck_with_epoch;

        #[test]
        fn get_block_info_non_existent() {
            crosscheck_with_epoch(
                "(get-block-info? time u9999999)",
                Ok(Some(Value::none())),
                StacksEpochId::Epoch25,
            );
        }

        #[test]
        fn test_block_height() {
            let snpt = "
                (define-public (block)
                (ok block-height))

                (define-public (burn-block)
                (ok burn-block-height))
            ";

            crosscheck_with_epoch(
                &format!("{snpt} (block)"),
                evaluate("(ok u0)"),
                StacksEpochId::Epoch24,
            );
            crosscheck_with_epoch(
                &format!("{snpt} (burn-block)"),
                evaluate("(ok u0)"),
                StacksEpochId::Epoch24,
            );
        }

        #[test]
        fn at_block() {
            crosscheck_with_epoch(
                "(at-block 0x0000000000000000000000000000000000000000000000000000000000000000 block-height)",
                Ok(Some(Value::UInt(0xFFFFFFFF))),
                StacksEpochId::Epoch24,
            )
        }

        #[test]
        fn get_block_info_less_than_two_args() {
            let epoch = if cfg!(feature = "test-clarity-v1") {
                StacksEpochId::Epoch2_05
            } else {
                StacksEpochId::Epoch25
            };

            let mut env = TestEnvironment::new(epoch, ClarityVersion::default_for_epoch(epoch));

            env.advance_chain_tip(1);
            let result = env.evaluate("(get-block-info? id-header-hash)");
            assert!(result.is_err());
            assert!(result
                .unwrap_err()
                .to_string()
                .contains("expecting >= 2 arguments, got 1"));
        }

        #[test]
        fn get_block_info_more_than_two_args() {
            // TODO: see issue #488
            // The inconsistency in function arguments should have been caught by the typechecker.
            // The runtime error below is being used as a workaround for a typechecker issue
            // where certain errors are not properly handled.
            // This test should be re-worked once the typechecker is fixed
            // and can correctly detect all argument inconsistencies.
            let snippet = "(get-block-info? burnchain-header-hash u0 miner-address)";
            let expected = Err(VmExecutionError::RuntimeCheck(
                clarity::vm::errors::RuntimeCheckErrorKind::IncorrectArgumentCount(2, 3),
            ));
            crosscheck_with_epoch(snippet, expected, StacksEpochId::Epoch24);
        }
    }

    //
    // Module with tests that should only be executed
    // when running Clarity::V3.
    //
    #[cfg(feature = "test-clarity-v3")]
    mod clarity_v3 {
        use clarity::types::StacksEpochId;
        use clarity::vm::ClarityVersion;

        use super::*;
        use crate::tools::{crosscheck_with_env, crosscheck_with_epoch};

        //- At Block
        #[test]
        fn at_block_with_stacks_block_height() {
            crosscheck_with_epoch("(at-block 0x0000000000000000000000000000000000000000000000000000000000000000 stacks-block-height)",
                Ok(Some(Value::UInt(0xFFFFFFFF))),
                StacksEpochId::Epoch30,
            )
        }

        #[test]
        fn get_stacks_block_info_less_than_two_args() {
            let result = evaluate("(get-stacks-block-info? id-header-hash)");
            assert!(result.is_err());
            assert!(result
                .unwrap_err()
                .to_string()
                .contains("expecting 2 arguments, got 1"));
        }

        #[test]
        fn get_stacks_block_info_more_than_two_args() {
            let result = evaluate("(get-stacks-block-info? id-header-hash u0 u0)");
            assert!(result.is_err());
            assert!(result
                .unwrap_err()
                .to_string()
                .contains("expecting 2 arguments, got 3"));
        }

        #[test]
        fn get_tenure_info_less_than_two_args() {
            let result = evaluate("(get-tenure-info? id-header-hash)");
            assert!(result.is_err());
            assert!(result
                .unwrap_err()
                .to_string()
                .contains("expecting 2 arguments, got 1"));
        }

        #[test]
        fn get_tenure_info_more_than_two_args() {
            let result = evaluate("(get-tenure-info? id-header-hash u0 u0)");
            assert!(result.is_err());
            assert!(result
                .unwrap_err()
                .to_string()
                .contains("expecting 2 arguments, got 3"));
        }

        #[test]
        fn get_stacks_block_info_id_header_hash() {
            let mut env = TestEnvironment::new(StacksEpochId::Epoch30, ClarityVersion::Clarity3);
            env.advance_chain_tip(1);
            let mut expected = [0u8; 32];
            // The hash here is taken from an older test for get-block-info?.
            // Because the logic behind get-stacks-block-info? id-header-hash
            // and get-block-info? id-header-hash are the same and both use the
            // get_index_block_header_hash function the return value should be
            // the same.
            hex::decode_to_slice(
                "b5e076ab7609c7f8c763b5c571d07aea80b06b41452231b1437370f4964ed66e",
                &mut expected,
            )
            .unwrap();
            crosscheck_with_env(
                "(get-stacks-block-info? id-header-hash u0)",
                Ok(Some(
                    Value::some(Value::buff_from(expected.to_vec()).unwrap()).unwrap(),
                )),
                env,
            );
        }

        #[test]
        fn get_stacks_block_info_time() {
            let mut env = TestEnvironment::new(StacksEpochId::Epoch30, ClarityVersion::Clarity3);
            env.advance_chain_tip(1);
            let expected = chrono::Utc::now().timestamp() as u128;
            crosscheck_with_env(
                "(get-stacks-block-info? time u0)",
                Ok(Some(Value::some(Value::UInt(expected)).unwrap())),
                env,
            );
        }

        #[test]
        fn get_stacks_block_info_header_hash() {
            let mut env = TestEnvironment::new(StacksEpochId::Epoch30, ClarityVersion::Clarity3);
            env.advance_chain_tip(1);
            let expected = Ok(Some(
                Value::some(Value::buff_from([0; 32].to_vec()).unwrap()).unwrap(),
            ));
            crosscheck_with_env("(get-stacks-block-info? header-hash u0)", expected, env);
        }

        #[test]
        fn get_tenure_info_time() {
            let mut env = TestEnvironment::new(StacksEpochId::Epoch30, ClarityVersion::Clarity3);
            env.advance_chain_tip(1);
            let expected = chrono::Utc::now().timestamp() as u128;
            crosscheck_with_env(
                "(get-tenure-info? time u0)",
                Ok(Some(Value::some(Value::UInt(expected)).unwrap())),
                env,
            );
        }

        #[test]
        fn get_tenure_info_header_hash() {
            let mut env = TestEnvironment::new(StacksEpochId::Epoch30, ClarityVersion::Clarity3);
            env.advance_chain_tip(1);
            let expected = Ok(Some(
                Value::some(Value::buff_from([0; 32].to_vec()).unwrap()).unwrap(),
            ));
            crosscheck_with_env("(get-tenure-info? burnchain-header-hash u0)", expected, env);
        }

        #[test]
        fn get_tenure_info_miner_address() {
            let mut env = TestEnvironment::new(StacksEpochId::Epoch30, ClarityVersion::Clarity3);
            env.advance_chain_tip(1);
            // The principal here is taken from an older test for
            // get-block-info?.
            // Because the logic behind get-tenure-info? id-header-hash and
            // get-block-info? id-header-hash are the same and both use the
            // get_miner_address function the return value should be the same.
            let expected = Ok(Some(
                Value::some(Value::Principal(
                    PrincipalData::parse("ST000000000000000000002AMW42H").unwrap(),
                ))
                .unwrap(),
            ));
            crosscheck_with_env("(get-tenure-info? miner-address u0)", expected, env);
        }

        #[test]
        #[ignore = "block-reward is not simulated in the test framework"]
        fn get_tenure_info_block_reward() {
            let mut env = TestEnvironment::new(StacksEpochId::Epoch30, ClarityVersion::Clarity3);
            env.advance_chain_tip(1);
            let expected = Ok(Some(Value::some(Value::UInt(0)).unwrap()));
            crosscheck_with_env("(get-tenure-info? block-reward u0)", expected, env);
        }

        #[test]
        fn get_tenure_info_miner_spend_total() {
            let mut env = TestEnvironment::new(StacksEpochId::Epoch30, ClarityVersion::Clarity3);
            env.advance_chain_tip(1);
            let expected = Ok(Some(Value::some(Value::UInt(0)).unwrap()));
            crosscheck_with_env("(get-tenure-info? miner-spend-total u0)", expected, env);
        }

        #[test]
        fn get_tenure_info_miner_spend_winner() {
            let mut env = TestEnvironment::new(StacksEpochId::Epoch30, ClarityVersion::Clarity3);
            env.advance_chain_tip(1);
            let expected = Ok(Some(Value::some(Value::UInt(0)).unwrap()));
            crosscheck_with_env("(get-tenure-info? miner-spend-winner u0)", expected, env);
        }

        #[test]
        fn get_tenure_info_vrf_seed() {
            let mut env = TestEnvironment::new(StacksEpochId::Epoch30, ClarityVersion::Clarity3);
            env.advance_chain_tip(1);
            let expected = Ok(Some(
                Value::some(Value::buff_from([0; 32].to_vec()).unwrap()).unwrap(),
            ));
            crosscheck_with_env("(get-tenure-info? vrf-seed u0)", expected, env);
        }
    }

    #[cfg(not(any(
        feature = "test-clarity-v1",
        feature = "test-clarity-v2",
        feature = "test-clarity-v3"
    )))]
    mod clarity_v4 {
        use clarity::types::StacksEpochId;
        use clarity::vm::ClarityVersion;

        use super::*;
        use crate::tools::crosscheck_with_env;

        #[test]
        fn stacks_block_time_crosscheck() {
            let env = TestEnvironment::new(StacksEpochId::Epoch33, ClarityVersion::Clarity4);
            crosscheck_with_env("stacks-block-time", Ok(Some(Value::UInt(1))), env);
        }
    }

    //- Block Info

    #[test]
    fn get_block_info_burnchain_header_hash() {
        let epoch = if cfg!(feature = "test-clarity-v1") {
            StacksEpochId::Epoch2_05
        } else {
            StacksEpochId::Epoch25
        };

        let mut env = TestEnvironment::new(epoch, ClarityVersion::default_for_epoch(epoch));
        env.advance_chain_tip(1);
        let result = env
            .evaluate("(get-block-info? burnchain-header-hash u0)")
            .expect("Failed to init contract.");
        assert_eq!(
            result,
            Some(Value::some(Value::buff_from([0; 32].to_vec()).unwrap()).unwrap())
        );
    }

    #[test]
    fn get_block_info_id_header_hash() {
        let epoch = if cfg!(feature = "test-clarity-v1") {
            StacksEpochId::Epoch2_05
        } else {
            StacksEpochId::Epoch25
        };

        let mut env = TestEnvironment::new(epoch, ClarityVersion::default_for_epoch(epoch));

        env.advance_chain_tip(1);
        let result = env
            .evaluate("(get-block-info? id-header-hash u0)")
            .expect("Failed to init contract.");
        let mut expected = [0u8; 32];
        hex::decode_to_slice(
            "b5e076ab7609c7f8c763b5c571d07aea80b06b41452231b1437370f4964ed66e",
            &mut expected,
        )
        .unwrap();
        assert_eq!(
            result,
            Some(Value::some(Value::buff_from(expected.to_vec()).unwrap()).unwrap())
        );
    }

    #[test]
    fn get_block_info_header_hash() {
        let epoch = if cfg!(feature = "test-clarity-v1") {
            StacksEpochId::Epoch2_05
        } else {
            StacksEpochId::Epoch25
        };

        let mut env = TestEnvironment::new(epoch, ClarityVersion::default_for_epoch(epoch));

        env.advance_chain_tip(1);
        let result = env
            .evaluate("(get-block-info? header-hash u0)")
            .expect("Failed to init contract.");
        assert_eq!(
            result,
            Some(Value::some(Value::buff_from([0; 32].to_vec()).unwrap()).unwrap())
        );
    }

    #[test]
    fn get_block_info_miner_address() {
        let epoch = if cfg!(feature = "test-clarity-v1") {
            StacksEpochId::Epoch2_05
        } else {
            StacksEpochId::Epoch25
        };

        let mut env = TestEnvironment::new(epoch, ClarityVersion::default_for_epoch(epoch));

        env.advance_chain_tip(1);
        let result = env
            .evaluate("(get-block-info? miner-address u0)")
            .expect("Failed to init contract.");
        assert_eq!(
            result,
            Some(
                Value::some(Value::Principal(
                    PrincipalData::parse("ST000000000000000000002AMW42H").unwrap()
                ))
                .unwrap()
            )
        )
    }

    #[test]
    fn get_block_info_time() {
        let epoch = if cfg!(feature = "test-clarity-v1") {
            StacksEpochId::Epoch2_05
        } else {
            StacksEpochId::Epoch25
        };

        let mut env = TestEnvironment::new(epoch, ClarityVersion::default_for_epoch(epoch));

        env.advance_chain_tip(1);
        let result = env
            .evaluate("(get-block-info? time u0)")
            .expect("Failed to init contract.");
        let block_time_val = match result {
            Some(Value::Optional(OptionalData { data: Some(data) })) => *data,
            _ => panic!("expected value"),
        };
        let block_time = match block_time_val {
            Value::UInt(val) => val,
            _ => panic!("expected uint"),
        };
        let now = chrono::Utc::now().timestamp() as u128;

        // The block time should be close to the current time, so let's give it
        // a 10 second window, to be safe.
        assert!(block_time >= now - 10);
    }

    #[test]
    #[ignore = "block-reward is not simulated in the test framework"]
    fn get_block_info_block_reward() {
        let mut env = TestEnvironment::default();
        env.advance_chain_tip(1);
        let result = env
            .evaluate("(get-block-info? block-reward u0)")
            .expect("Failed to init contract.");
        assert_eq!(result, Some(Value::some(Value::UInt(0)).unwrap()));
    }

    #[test]
    fn get_block_info_miner_spend_total() {
        let mut env = TestEnvironment::new(
            clarity::types::StacksEpochId::Epoch25,
            clarity::vm::ClarityVersion::Clarity2,
        );

        env.advance_chain_tip(1);
        let result = env
            .evaluate("(get-block-info? miner-spend-total u0)")
            .expect("Failed to init contract.");
        assert_eq!(result, Some(Value::some(Value::UInt(0)).unwrap()));
    }

    #[test]
    fn get_block_info_miner_spend_winner() {
        let mut env = TestEnvironment::new(
            clarity::types::StacksEpochId::Epoch25,
            clarity::vm::ClarityVersion::Clarity2,
        );

        env.advance_chain_tip(1);
        let result = env
            .evaluate("(get-block-info? miner-spend-winner u0)")
            .expect("Failed to init contract.");
        assert_eq!(result, Some(Value::some(Value::UInt(0)).unwrap()));
    }

    #[test]
    fn get_block_info_vrf_seed() {
        let mut env = TestEnvironment::new(
            clarity::types::StacksEpochId::Epoch25,
            clarity::vm::ClarityVersion::Clarity2,
        );
        env.advance_chain_tip(1);
        let result = env
            .evaluate("(get-block-info? vrf-seed u0)")
            .expect("Failed to init contract.");
        assert_eq!(
            result,
            Some(Value::some(Value::buff_from([0; 32].to_vec()).unwrap()).unwrap())
        );
    }

    #[test]
    fn get_burn_block_info_less_than_two_args() {
        let result = evaluate("(get-burn-block-info? id-header-hash)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 1"));
    }

    #[test]
    fn get_burn_block_info_more_than_two_args() {
        let result = evaluate("(get-burn-block-info? id-header-hash u0 u0)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 3"));
    }

    #[test]
    fn get_burn_block_info_pox_addrs() {
        let mut env = TestEnvironment::default();
        env.advance_chain_tip(1);
        let result = env
            .evaluate("(get-burn-block-info? pox-addrs u0)")
            .expect("Failed to init contract.");
        assert_eq!(
            result,
            Some(
                Value::some(
                    TupleData::from_data(vec![
                        (
                            ClarityName::from_literal("addrs"),
                            Value::cons_list_unsanitized(vec![TupleData::from_data(vec![
                                (
                                    ClarityName::from_literal("hashbytes"),
                                    Value::buff_from([0; 32].to_vec()).unwrap()
                                ),
                                (
                                    ClarityName::from_literal("version"),
                                    Value::buff_from_byte(0)
                                )
                            ])
                            .unwrap()
                            .into()])
                            .unwrap()
                        ),
                        (ClarityName::from_literal("payout"), Value::UInt(0))
                    ])
                    .unwrap()
                    .into()
                )
                .unwrap()
            )
        );
    }

    #[test]
    #[ignore = "test system needs to be improved relative to versioning and epochs"]
    fn at_block_less_than_two_args() {
        let result = evaluate(
            "(at-block 0xb5e076ab7609c7f8c763b5c571d07aea80b06b41452231b1437370f4964ed66e)",
        );
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 1"));
    }

    #[test]
    #[ignore = "test system needs to be improved relative to versioning and epochs"]
    fn at_block_more_than_two_args() {
        let result = evaluate(
            "(at-block 0xb5e076ab7609c7f8c763b5c571d07aea80b06b41452231b1437370f4964ed66e u0 u0)",
        );
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 3"));
    }

    #[test]
    #[ignore = "test system needs to be improved relative to versioning and epochs"]
    fn at_block_var() {
        let e = evaluate(
                "
(define-data-var data int 1)
(at-block 0xb5e076ab7609c7f8c763b5c571d07aea80b06b41452231b1437370f4964ed66e (var-get data)) ;; block 0
",
            )
            .unwrap_err();
        assert_eq!(
            e,
            VmExecutionError::Wasm(clarity::vm::errors::WasmError::DefineFunctionCalledInRunMode,),
        );
    }

    //
    // Module with tests that should only be executed
    // when running Clarity::V2 or Clarity::v3.
    //
    #[cfg(not(feature = "test-clarity-v1"))]
    #[cfg(test)]
    mod clarity_v2_v3 {
        use super::*;
        use crate::tools::crosscheck;

        #[test]
        fn get_burn_block_info_non_existent() {
            crosscheck(
                "(get-burn-block-info? header-hash u9999999)",
                Ok(Some(
                    Value::some(Value::buff_from([0; 32].to_vec()).unwrap()).unwrap(),
                )),
            )
        }

        #[test]
        fn get_burn_block_info_header_hash() {
            crosscheck(
                "(get-burn-block-info? header-hash u0)",
                Ok(Some(
                    Value::some(Value::buff_from([0; 32].to_vec()).unwrap()).unwrap(),
                )),
            )
        }

        #[test]
        fn test_chain_id() {
            crosscheck(
                "
(define-public (get-chain-id)
  (ok chain-id))

(get-chain-id)
",
                evaluate("(ok u2147483648)"),
            );
        }
    }
}
