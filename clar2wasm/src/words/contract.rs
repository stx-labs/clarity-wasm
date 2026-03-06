use clarity::vm::clarity_wasm::get_type_size;
use clarity::vm::types::signatures::CallableSubtype;
use clarity::vm::types::{PrincipalData, TypeSignature};
use clarity::vm::{ClarityName, SymbolicExpression, SymbolicExpressionType, Value};
use walrus::ir::BinaryOp;
use walrus::ValType;

use super::{ComplexWord, Word};
use crate::check_args;
use crate::cost::WordCharge;
use crate::wasm_generator::{clar2wasm_ty, ArgumentsExt, GeneratorError, WasmGenerator};
use crate::wasm_utils::ArgumentCountCheck;
use crate::words::SimpleWord;

#[derive(Debug)]
pub enum AsContract {
    Original,
    New,
}

impl Word for AsContract {
    fn name(&self) -> ClarityName {
        match self {
            AsContract::Original => ClarityName::from_literal("as-contract"),
            AsContract::New => ClarityName::from_literal("as-contract?"),
        }
    }
}

impl ComplexWord for AsContract {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        // The two implementations need to be seperated as the linker functions return return different results
        match self {
            Self::Original => {
                check_args!(generator, builder, 1, args.len(), ArgumentCountCheck::Exact);

                self.charge(generator, builder, 0)?;

                let inner = args.get_expr(0)?;

                // Call the host interface function, `enter_as_contract_original`
                builder.call(generator.func_by_name("stdlib.enter_as_contract_original"));

                // Traverse the inner expression
                generator.traverse_expr(builder, inner)?;

                // Call the host interface function, `exit_as_contract_original`
                builder.call(generator.func_by_name("stdlib.exit_as_contract_original"));
            }
            Self::New => {
                check_args!(generator, builder, 2, args.len(), ArgumentCountCheck::Exact);

                // TODO: add cost tracking #783
                let allowances = args.get_list(0)?;
                let inner = args.get_expr(1)?;

                // `as-contract?` returns a response type: (response <inner_type> uint).
                // In WASM, this is represented as [i32_indicator, ok_wasm_vals..., err_wasm_vals...].
                // For example, (response bool uint) = [i32, i32, i64, i64].
                //   - On success: [1, inner_result, 0, 0]
                //   - On failure: [0, 0, violation_lo, violation_hi]
                let inner_ty = generator
                    .get_expr_type(inner)
                    .ok_or_else(|| {
                        GeneratorError::TypeError(
                            "as-contract? inner expression must be typed".to_owned(),
                        )
                    })?
                    .clone();

                let return_ty = generator
                    .get_expr_type(expr)
                    .ok_or_else(|| {
                        GeneratorError::TypeError(
                            "as-contract? expression must be typed".to_owned(),
                        )
                    })?
                    .clone();

                // Enter the as-contract context (pushes sender/caller, begins transaction)
                builder.call(generator.func_by_name("stdlib.enter_as_contract_new"));

                // Traverse each allowance expression in the list.
                // Each one registers its allowance in the asset context.
                for allowance in allowances {
                    generator.traverse_expr(builder, allowance)?;
                }

                // Traverse the inner expression — its result is pushed onto the WASM stack
                generator.traverse_expr(builder, inner)?;

                // Save the inner result to locals so we can use it later.
                // We need to get it off the stack before calling exit, which
                // pushes its own return values.
                let inner_locals = generator.save_to_locals(builder, &inner_ty, true);

                // Call exit
                // Returns (indicator: i32, padding: i32, err_lo: i64, err_hi: i64).
                // The host function can't access the inner result on the WASM stack,
                // so the ok slot (padding) is always 0 — we splice in the real inner
                // result below.
                builder.call(generator.func_by_name("stdlib.exit_as_contract_new"));

                // Save the 4 exit return values to locals (popped in reverse order)
                let hi_local = generator.module.locals.add(ValType::I64);
                let lo_local = generator.module.locals.add(ValType::I64);
                let _padding_local = generator.module.locals.add(ValType::I32);
                let indicator_local = generator.module.locals.add(ValType::I32);
                builder.local_set(hi_local);
                builder.local_set(lo_local);
                builder.local_set(_padding_local);
                builder.local_set(indicator_local);

                // Allocate locals for the full response result
                let result_wasm_types = clar2wasm_ty(&return_ty);
                let result_locals: Vec<_> = result_wasm_types
                    .iter()
                    .map(|t| generator.module.locals.add(*t))
                    .collect();

                // Set the response indicator (1 = ok, 0 = err)
                builder
                    .local_get(indicator_local)
                    .local_set(result_locals[0]);

                let inner_wasm_len = clar2wasm_ty(&inner_ty).len();

                // Conditionally populate the ok or err slots of the response.
                // Locals default to zero, so we only need to set the relevant slots.
                builder.local_get(indicator_local).if_else(
                    None,
                    |then| {
                        // Success: copy the saved inner result into the ok slots.
                        // The err slots remain at their default zero values.
                        for (i, local) in inner_locals.iter().enumerate() {
                            then.local_get(*local).local_set(result_locals[1 + i]);
                        }
                    },
                    |else_| {
                        // Failure: the ok slots remain at their default zero values.
                        // Copy the violation index (u128) into the err slots.
                        let err_offset = 1 + inner_wasm_len;
                        else_
                            .local_get(lo_local)
                            .local_set(result_locals[err_offset]);
                        else_
                            .local_get(hi_local)
                            .local_set(result_locals[err_offset + 1]);
                    },
                );

                // Push the full response type onto the WASM stack
                for local in &result_locals {
                    builder.local_get(*local);
                }
            }
        }
        Ok(())
    }
}

#[derive(Debug)]
pub struct WithAllAssetsUnsafe;

impl Word for WithAllAssetsUnsafe {
    fn name(&self) -> ClarityName {
        ClarityName::from_literal("with-all-assets-unsafe")
    }
}

impl ComplexWord for WithAllAssetsUnsafe {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 0, args.len(), ArgumentCountCheck::Exact);

        self.charge(generator, builder, 0)?;

        // Call the host interface function, `with_all_assets_unsafe`
        builder.call(generator.func_by_name("stdlib.with_all_assets_unsafe"));

        Ok(())
    }
}

#[derive(Debug)]
pub struct WithFt;

impl Word for WithFt {
    fn name(&self) -> ClarityName {
        ClarityName::from_literal("with-ft")
    }
}

impl ComplexWord for WithFt {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 3, args.len(), ArgumentCountCheck::Exact);

        self.charge(generator, builder, 0)?;

        let token_contract = args.get_expr(0)?;
        let token_name = args.get_expr(1)?;
        let allowance = args.get_expr(2)?;

        // Traverse the contract principal
        generator.traverse_expr(builder, token_contract)?;

        // Traverse the token name
        generator.traverse_expr(builder, token_name)?;

        // Traverse the allowance amount (uint)
        generator.traverse_expr(builder, allowance)?;

        // Call the host interface function, `with_ft`
        builder.call(generator.func_by_name("stdlib.with_ft"));

        Ok(())
    }
}

#[derive(Debug)]
pub struct WithNft;

impl Word for WithNft {
    fn name(&self) -> ClarityName {
        ClarityName::from_literal("with-nft")
    }
}

impl ComplexWord for WithNft {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 3, args.len(), ArgumentCountCheck::Exact);

        self.charge(generator, builder, 0)?;

        let token_contract = args.get_expr(0)?;
        let token_name = args.get_expr(1)?;
        let allowance = args.get_expr(2)?;

        // Traverse the contract principal
        generator.traverse_expr(builder, token_contract)?;

        // Traverse the token name
        generator.traverse_expr(builder, token_name)?;

        // Traverse the allowances list
        generator.traverse_expr(builder, allowance)?;

        // Call the host interface function, `with_nft`
        builder.call(generator.func_by_name("stdlib.with_nft"));

        Ok(())
    }
}

#[derive(Debug)]
pub struct WithStacking;

impl Word for WithStacking {
    fn name(&self) -> ClarityName {
        ClarityName::from_literal("with-stacking")
    }
}

impl ComplexWord for WithStacking {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 1, args.len(), ArgumentCountCheck::Exact);

        self.charge(generator, builder, 0)?;

        let allowance = args.get_expr(0)?;

        // Traverse the allowance amount (uint)
        generator.traverse_expr(builder, allowance)?;

        // Call the host interface function, `with_stacking`
        builder.call(generator.func_by_name("stdlib.with_stacking"));

        Ok(())
    }
}

#[derive(Debug)]
pub struct WithStx;

impl Word for WithStx {
    fn name(&self) -> ClarityName {
        ClarityName::from_literal("with-stx")
    }
}

impl ComplexWord for WithStx {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 1, args.len(), ArgumentCountCheck::Exact);

        self.charge(generator, builder, 0)?;

        let allowance = args.get_expr(0)?;

        // Traverse the allowance amount (uint)
        generator.traverse_expr(builder, allowance)?;

        // Call the host interface function, `with_stx`
        builder.call(generator.func_by_name("stdlib.with_stx"));

        Ok(())
    }
}

#[derive(Debug)]
pub struct ContractCall;

impl Word for ContractCall {
    fn name(&self) -> ClarityName {
        ClarityName::from_literal("contract-call?")
    }
}

impl ComplexWord for ContractCall {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(
            generator,
            builder,
            2,
            args.len(),
            ArgumentCountCheck::AtLeast
        );

        self.charge(generator, builder, 0)?;

        let function_name = args.get_name(1)?;
        let contract_expr = args.get_expr(0)?;
        if let SymbolicExpressionType::LiteralValue(Value::Principal(PrincipalData::Contract(
            ref contract_identifier,
        ))) = contract_expr.expr
        {
            // This is a static contract call.
            // Push an empty trait name first
            builder.i32_const(0).i32_const(0);
            // Push the contract identifier onto the stack
            // TODO(#111): These should be tracked for reuse, similar to the string literals
            let (id_offset, id_length) =
                generator.add_literal(&contract_identifier.clone().into())?;
            builder
                .i32_const(id_offset as i32)
                .i32_const(id_length as i32);
        } else {
            // This is a dynamic contract call (via a trait).
            // Push the trait name on the stack
            let dynamic_arg = contract_expr.match_atom().ok_or_else(|| {
                GeneratorError::TypeError(
                    "Dynamic contract-call? argument should be a name".to_owned(),
                )
            })?;
            // Check if the name is in local bindings first, then in current function arguments.
            let trait_id = generator
                .bindings
                .get_trait_identifier(dynamic_arg)
                .or_else(|| {
                    generator
                        .get_current_function_arg_type(dynamic_arg)
                        .and_then(|ty| match ty {
                            TypeSignature::CallableType(CallableSubtype::Trait(trait_id)) => {
                                Some(trait_id)
                            }
                            TypeSignature::TraitReferenceType(trait_id) => Some(trait_id),
                            _ => None,
                        })
                })
                .ok_or_else(|| {
                    GeneratorError::TypeError(
                        "Dynamic argument of contract-call? should be a trait".to_owned(),
                    )
                })?;

            let (offset, len) = generator.used_traits.get(trait_id).ok_or_else(|| {
                GeneratorError::TypeError(format!(
                    "Usage of an unimported trait: {}",
                    trait_id.name
                ))
            })?;
            builder.i32_const(*offset as i32).i32_const(*len as i32);
            // Traversing the expression should load the contract identifier
            // onto the stack.
            generator.traverse_expr(builder, contract_expr)?;
        }

        // shadow args
        let args = if args.len() >= 2 { &args[2..] } else { &[] };
        let args_ty: Vec<_> = args
            .iter()
            .map(|arg| {
                generator
                    .get_expr_type(arg)
                    .ok_or_else(|| {
                        GeneratorError::TypeError(
                            "contract-call? argument must be typed".to_owned(),
                        )
                    })
                    .cloned()
            })
            .collect::<Result<_, _>>()?;

        // Push the function name onto the stack
        let (fn_offset, fn_length) = generator.add_string_literal(function_name)?;
        builder
            .i32_const(fn_offset as i32)
            .i32_const(fn_length as i32);

        // Write the arguments to the call stack, to be read by the host
        let arg_offset = generator.module.locals.add(ValType::I32);
        let total_args_size = args_ty.iter().map(get_type_size).sum();
        builder
            .global_get(generator.stack_pointer)
            .local_tee(arg_offset)
            .i32_const(total_args_size)
            .binop(BinaryOp::I32Add)
            .global_set(generator.stack_pointer);

        let mut arg_length = 0;
        for (arg, arg_ty) in args.iter().zip(args_ty) {
            // Traverse the argument, pushing it onto the stack
            generator.traverse_expr(builder, arg)?;

            arg_length += generator.write_to_memory(builder, arg_offset, arg_length, &arg_ty)?;
        }

        // Push the arguments offset and length onto the data stack
        builder.local_get(arg_offset).i32_const(arg_length as i32);

        // Reserve space for the return value
        let return_ty = generator
            .get_expr_type(expr)
            .ok_or_else(|| {
                GeneratorError::TypeError("contract-call? expression must be typed".to_owned())
            })?
            .clone();
        let (return_offset, return_size) =
            generator.create_call_stack_local(builder, &return_ty, true, true);

        // Push the return offset and size to the data stack
        builder.local_get(return_offset).i32_const(return_size);

        // Call the host interface function, `contract_call`
        builder.call(generator.func_by_name("stdlib.contract_call"));

        // Host interface fills the result into the specified memory. Read it
        // back out, and place the value on the data stack.
        generator.read_from_memory(builder, return_offset, 0, &return_ty)?;

        Ok(())
    }
}

#[derive(Debug)]
pub struct ContractHash;

impl Word for ContractHash {
    fn name(&self) -> ClarityName {
        ClarityName::from_literal("contract-hash?")
    }
}

impl SimpleWord for ContractHash {
    fn visit(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        arg_types: &[TypeSignature],
        return_type: &TypeSignature,
    ) -> Result<(), GeneratorError> {
        check_args!(
            generator,
            builder,
            1,
            arg_types.len(),
            ArgumentCountCheck::Exact
        );

        // TODO: add cost tests after the costs are implemented (see issue #783)
        // self.charge(generator, builder, 0)?;

        // Reserve space for the return value (response (buff 32) uint)
        let (return_offset, return_size) =
            generator.create_call_stack_local(builder, return_type, true, true);

        // Push the return offset and size to the data stack
        builder.local_get(return_offset).i32_const(return_size);

        // Call the host interface function, `contract_hash`
        builder.call(generator.func_by_name("stdlib.contract_hash"));

        // Host interface fills the result into the specified memory. Read it
        // back out, and place the value on the data stack.
        generator.read_from_memory(builder, return_offset, 0, return_type)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use clarity::vm::Value;
    use clarity_types::ContractName;

    use crate::tools::{
        crosscheck_multi_contract, crosscheck_multi_contract_with_env, TestEnvironment,
    };

    #[cfg(not(feature = "test-clarity-v4"))]
    mod clarity_v1_v2_v3 {
        use clarity::types::StacksEpochId;
        use clarity::vm::ClarityVersion;

        use crate::tools::evaluate_at;

        #[test]
        fn as_contract_less_than_one_arg() {
            let result = evaluate_at(
                "(as-contract)",
                StacksEpochId::Epoch32,
                ClarityVersion::Clarity3,
            );
            assert!(result.is_err());
            assert!(result
                .unwrap_err()
                .to_string()
                .contains("expecting 1 arguments, got 0"));
        }

        #[test]
        fn as_contract_more_than_one_arg() {
            let result = evaluate_at(
                "(as-contract 1 2)",
                StacksEpochId::Epoch32,
                ClarityVersion::Clarity3,
            );
            assert!(result.is_err());
            assert!(result
                .unwrap_err()
                .to_string()
                .contains("expecting 1 arguments, got 2"));
        }
    }

    #[test]
    fn contract_call_less_than_two_args() {
        let mut env = TestEnvironment::default();
        env.init_contract_with_snippet(
            "contract-callee",
            r#"
(define-public (no-args)
    (ok u42)
)
            "#,
        )
        .expect("Failed to init contract.");
        let result =
            env.init_contract_with_snippet("contract-caller", "(contract-call? .contract-callee)");

        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting >= 2 arguments, got 1"));
    }

    #[test]
    fn static_no_args() {
        let mut env = TestEnvironment::default();
        env.init_contract_with_snippet(
            "contract-callee",
            r#"
(define-public (no-args)
    (ok u42)
)
            "#,
        )
        .expect("Failed to init contract.");
        let val = env
            .init_contract_with_snippet(
                "contract-caller",
                "(contract-call? .contract-callee no-args)",
            )
            .expect("Failed to init contract.");

        assert_eq!(val.unwrap(), Value::okay(Value::UInt(42)).unwrap());
    }

    #[test]
    fn static_one_simple_arg() {
        let mut env = TestEnvironment::default();
        env.init_contract_with_snippet(
            "contract-callee",
            r#"
(define-public (one-simple-arg (x int))
    (ok x)
)
            "#,
        )
        .expect("Failed to init contract.");
        let val = env
            .init_contract_with_snippet(
                "contract-caller",
                "(contract-call? .contract-callee one-simple-arg 42)",
            )
            .expect("Failed to init contract.");

        assert_eq!(val.unwrap(), Value::okay(Value::Int(42)).unwrap());
    }

    #[test]
    fn static_one_arg() {
        let mut env = TestEnvironment::default();
        env.init_contract_with_snippet(
            "contract-callee",
            r#"
(define-public (one-arg (x (string-ascii 16)))
    (ok x)
)
            "#,
        )
        .expect("Failed to init contract.");
        let val = env
            .init_contract_with_snippet(
                "contract-caller",
                r#"(contract-call? .contract-callee one-arg "hello")"#,
            )
            .expect("Failed to init contract.");

        assert_eq!(
            val.unwrap(),
            Value::okay(Value::string_ascii_from_bytes("hello".to_string().into_bytes()).unwrap())
                .unwrap()
        );
    }

    #[test]
    fn static_two_simple_args() {
        let mut env = TestEnvironment::default();
        env.init_contract_with_snippet(
            "contract-callee",
            r#"
(define-public (two-simple-args (x int) (y int))
    (ok (+ x y))
)
            "#,
        )
        .expect("Failed to init contract.");
        let val = env
            .init_contract_with_snippet(
                "contract-caller",
                r#"(contract-call? .contract-callee two-simple-args 17 42)"#,
            )
            .expect("Failed to init contract.");

        assert_eq!(val.unwrap(), Value::okay(Value::Int(17 + 42)).unwrap());
    }

    #[test]
    fn static_two_args() {
        let mut env = TestEnvironment::default();
        env.init_contract_with_snippet(
            "contract-callee",
            r#"
(define-public (two-args (x (string-ascii 16)) (y (string-ascii 16)))
    (ok (concat x y))
)
            "#,
        )
        .expect("Failed to init contract.");
        let val = env
            .init_contract_with_snippet(
                "contract-caller",
                r#"(contract-call? .contract-callee two-args "hello " "world")"#,
            )
            .expect("Failed to init contract.");

        assert_eq!(
            val.unwrap(),
            Value::okay(
                Value::string_ascii_from_bytes("hello world".to_string().into_bytes()).unwrap()
            )
            .unwrap()
        );
    }

    #[test]
    fn dynamic_no_args() {
        let mut env = TestEnvironment::default();
        env.init_contract_with_snippet(
            "contract-callee",
            r#"
(define-trait test-trait ((no-args () (response uint uint))))
(define-public (no-args)
    (ok u42)
)
            "#,
        )
        .expect("Failed to init contract.");
        let val = env
            .init_contract_with_snippet(
                "contract-caller",
                r#"
(use-trait test-trait .contract-callee.test-trait)
(define-private (call-it (t <test-trait>))
    (contract-call? t no-args)
)
(call-it .contract-callee)
            "#,
            )
            .expect("Failed to init contract.");

        assert_eq!(val.unwrap(), Value::okay(Value::UInt(42)).unwrap());
    }

    #[test]
    fn dynamic_one_simple_arg() {
        let mut env = TestEnvironment::default();
        env.init_contract_with_snippet(
            "contract-callee",
            r#"
(define-trait test-trait ((one-simple-arg (int) (response int uint))))
(define-public (one-simple-arg (x int))
    (ok x)
)
            "#,
        )
        .expect("Failed to init contract.");
        let val = env
            .init_contract_with_snippet(
                "contract-caller",
                r#"
(use-trait test-trait .contract-callee.test-trait)
(define-private (call-it (t <test-trait>) (x int))
    (contract-call? t one-simple-arg x)
)
(call-it .contract-callee 42)
            "#,
            )
            .expect("Failed to init contract.");

        assert_eq!(val.unwrap(), Value::okay(Value::Int(42)).unwrap());
    }

    #[test]
    fn dynamic_one_arg() {
        let mut env = TestEnvironment::default();
        env.init_contract_with_snippet(
            "contract-callee",
            r#"
(define-trait test-trait ((one-arg ((string-ascii 16)) (response (string-ascii 16) uint))))
(define-public (one-arg (x (string-ascii 16)))
    (ok x)
)
            "#,
        )
        .expect("Failed to init contract.");
        let val = env
            .init_contract_with_snippet(
                "contract-caller",
                r#"
(use-trait test-trait .contract-callee.test-trait)
(define-private (call-it (t <test-trait>) (x (string-ascii 16)))
    (contract-call? t one-arg x)
)
(call-it .contract-callee "hello")
            "#,
            )
            .expect("Failed to init contract.");

        assert_eq!(
            val.unwrap(),
            Value::okay(Value::string_ascii_from_bytes("hello".to_string().into_bytes()).unwrap())
                .unwrap()
        );
    }

    #[test]
    fn dynamic_two_simple_args() {
        let mut env = TestEnvironment::default();
        env.init_contract_with_snippet(
            "contract-callee",
            r#"
(define-trait test-trait ((two-simple-args (int int) (response int uint))))
(define-public (two-simple-args (x int) (y int))
    (ok (+ x y))
)
            "#,
        )
        .expect("Failed to init contract.");
        let val = env
            .init_contract_with_snippet(
                "contract-caller",
                r#"
(use-trait test-trait .contract-callee.test-trait)
(define-private (call-it (t <test-trait>) (x int) (y int))
    (contract-call? t two-simple-args x y)
)
(call-it .contract-callee 17 42)
            "#,
            )
            .expect("Failed to init contract.");

        assert_eq!(val.unwrap(), Value::okay(Value::Int(17 + 42)).unwrap());
    }

    #[test]
    fn dynamic_two_args() {
        let mut env = TestEnvironment::default();
        env.init_contract_with_snippet(
            "contract-callee",
            r#"
(define-trait test-trait ((two-args ((string-ascii 16) (string-ascii 16)) (response (string-ascii 32) uint))))
(define-public (two-args (x (string-ascii 16)) (y (string-ascii 16)))
    (ok (concat x y))
)
            "#,
        ).expect("Failed to init contract.");
        let val = env
            .init_contract_with_snippet(
                "contract-caller",
                r#"
(use-trait test-trait .contract-callee.test-trait)
(define-private (call-it (t <test-trait>) (x (string-ascii 16)) (y (string-ascii 16)))
    (contract-call? t two-args x y)
)
(call-it .contract-callee "hello " "world")
            "#,
            )
            .expect("Failed to init contract.");

        assert_eq!(
            val.unwrap(),
            Value::okay(
                Value::string_ascii_from_bytes("hello world".to_string().into_bytes()).unwrap()
            )
            .unwrap()
        );
    }

    #[test]
    /// Call the erroring function directly and verify that the changes are
    /// rolled back.
    fn err_rollback_direct() {
        let mut env = TestEnvironment::default();
        env.init_contract_with_snippet(
            "contract-callee",
            r#"
(define-data-var my-val int 111)
(define-public (set-err (val int))
    (begin
        (var-set my-val val)
        (err u1)
    )
)
(define-read-only (get-val)
    (var-get my-val)
)
            "#,
        )
        .expect("Failed to init contract.");

        // Expect this call to return an error
        let res = env
            .init_contract_with_snippet(
                "contract-caller",
                "(contract-call? .contract-callee set-err -42)",
            )
            .expect("Failed to init contract.");
        assert_eq!(res.unwrap(), Value::err_uint(1));

        // Expect the data-var to be unchanged
        let val = env
            .init_contract_with_snippet("check-value", "(contract-call? .contract-callee get-val)")
            .expect("Failed to init contract.");
        assert_eq!(val.unwrap(), Value::Int(111));
    }

    #[test]
    /// Call the erroring function indirectly, through another contract's
    /// function which also fails, and verify that the changes are rolled back.
    fn err_rollback() {
        let mut env = TestEnvironment::default();
        env.init_contract_with_snippet(
            "contract-callee",
            r#"
(define-data-var my-val int 111)
(define-public (set-err (val int))
    (begin
        (var-set my-val val)
        (err u1)
    )
)
(define-read-only (get-val)
    (var-get my-val)
)
            "#,
        )
        .expect("Failed to init contract.");

        env.init_contract_with_snippet(
            "contract-caller",
            r#"
(define-public (call-set-err)
    (contract-call? .contract-callee set-err -42)
)
              "#,
        )
        .expect("Failed to init contract.");

        // Expect this call to return an err
        let res = env
            .init_contract_with_snippet("call-it", "(contract-call? .contract-caller call-set-err)")
            .expect("Failed to init contract.");
        assert_eq!(res.unwrap(), Value::err_uint(1));

        // Expect the data-var to be unchanged
        let val = env
            .init_contract_with_snippet("check-value", "(contract-call? .contract-callee get-val)")
            .expect("Failed to init contract.");
        assert_eq!(val.unwrap(), Value::Int(111));
    }

    #[test]
    /// Call the erroring function indirectly, through another contract's
    /// function which returns ok, but verify that the erroring functions'
    /// changes are still rolled back.
    fn err_rollback_ok() {
        let mut env = TestEnvironment::default();
        env.init_contract_with_snippet(
            "contract-callee",
            r#"
(define-data-var my-val int 111)
(define-public (set-err (val int))
    (begin
        (var-set my-val val)
        (err u1)
    )
)
(define-read-only (get-val)
    (var-get my-val)
)
            "#,
        )
        .expect("Failed to init contract.");

        env.init_contract_with_snippet(
            "contract-caller",
            r#"
(define-public (call-set-err-ok)
    (ok (unwrap-err-panic (contract-call? .contract-callee set-err -42)))
)
              "#,
        )
        .expect("Failed to init contract.");

        // Expect this call to return an okay.
        let res = env
            .init_contract_with_snippet(
                "call-it",
                "(contract-call? .contract-caller call-set-err-ok)",
            )
            .expect("Failed to init contract.");
        assert_eq!(res.unwrap(), Value::okay(Value::UInt(1)).unwrap());

        // Expect the data-var to be unchanged
        let val = env
            .init_contract_with_snippet("check-value", "(contract-call? .contract-callee get-val)")
            .expect("Failed to init contract.");
        assert_eq!(val.unwrap(), Value::Int(111));
    }

    #[test]
    /// Call the erroring function indirectly, through another contract's
    /// function which returns ok, but verify that the erroring functions'
    /// changes are still rolled back, while the ok function's changes are
    /// preserved.
    fn err_rollback_ok_preserve_changes() {
        let mut env = TestEnvironment::default();
        env.init_contract_with_snippet(
            "contract-callee",
            r#"
(define-data-var my-val int 111)
(define-public (set-err (val int))
    (begin
        (var-set my-val val)
        (err u1)
    )
)
(define-read-only (get-val)
    (var-get my-val)
)
            "#,
        )
        .expect("Failed to init contract.");

        env.init_contract_with_snippet(
            "contract-caller",
            r#"
(define-data-var my-val int 3)
(define-public (call-set-err-ok)
    (begin
        (var-set my-val 123)
        (ok (unwrap-err-panic (contract-call? .contract-callee set-err -42)))
    )
)
(define-read-only (get-val)
    (var-get my-val)
)
              "#,
        )
        .expect("Failed to init contract.");

        // Expect this call to return an okay.
        let res = env
            .init_contract_with_snippet(
                "call-it",
                "(contract-call? .contract-caller call-set-err-ok)",
            )
            .expect("Failed to init contract.");
        assert_eq!(res.unwrap(), Value::okay(Value::UInt(1)).unwrap());

        // Expect the callee data-var to be unchanged
        let val = env
            .init_contract_with_snippet("check-value", "(contract-call? .contract-callee get-val)")
            .expect("Failed to init contract.");
        assert_eq!(val.unwrap(), Value::Int(111));

        // Expect the caller data-var to be changed.
        let val = env
            .init_contract_with_snippet(
                "check-value-2",
                "(contract-call? .contract-caller get-val)",
            )
            .expect("Failed to init contract.");
        assert_eq!(val.unwrap(), Value::Int(123));
    }

    #[test]
    /// Call the erroring function via an intra-contract function call (not
    /// using `contract-call?`), and verify that the changes are rolled back.
    fn err_rollback_intra_contract_call() {
        let mut env = TestEnvironment::default();
        env.init_contract_with_snippet(
            "contract-callee",
            r#"
(define-data-var my-val int 111)
(define-public (set-err (val int))
    (begin
        (var-set my-val val)
        (err u1)
    )
)
(define-public (set-it)
    (ok (unwrap-err-panic (set-err -123)))
)
(define-read-only (get-val)
    (var-get my-val)
)
            "#,
        )
        .expect("Failed to init contract.");

        // Expect this call to return an okay.
        let res = env
            .init_contract_with_snippet(
                "contract-caller",
                "(contract-call? .contract-callee set-it)",
            )
            .expect("Failed to init contract.");
        assert_eq!(res.unwrap(), Value::okay(Value::UInt(1)).unwrap());

        // Expect the data-var to be unchanged
        let val = env
            .init_contract_with_snippet("check-value", "(contract-call? .contract-callee get-val)")
            .expect("Failed to init contract.");
        assert_eq!(val.unwrap(), Value::Int(111));
    }

    #[test]
    /// Call the erroring function via an intra-contract function call (not
    /// using `contract-call?`), and verify that the changes are rolled back
    /// because the erroring function is private.
    fn err_no_rollback_intra_contract_call() {
        let mut env = TestEnvironment::default();
        env.init_contract_with_snippet(
            "contract-callee",
            r#"
(define-data-var my-val int 111)
(define-private (set-err (val int))
    (begin
        (var-set my-val val)
        (err u1)
    )
)
(define-public (set-it)
    (ok (unwrap-err-panic (set-err -123)))
)
(define-read-only (get-val)
    (var-get my-val)
)
            "#,
        )
        .expect("Failed to init contract.");

        // Expect this call to return an okay.
        let res = env
            .init_contract_with_snippet(
                "contract-caller",
                "(contract-call? .contract-callee set-it)",
            )
            .expect("Failed to init contract.");
        assert_eq!(res.unwrap(), Value::okay(Value::UInt(1)).unwrap());

        // Expect the data-var to be unchanged
        let val = env
            .init_contract_with_snippet("check-value", "(contract-call? .contract-callee get-val)")
            .expect("Failed to init contract.");
        assert_eq!(val.unwrap(), Value::Int(-123));
    }

    #[test]
    fn multi_dynamic_define_impl_call() {
        let foo_trait = "
            (define-trait foo
                (
                    (do-it () (response bool uint))
                )
            )
            ";

        let foo_impl = "
            (impl-trait .foo.foo)

            (define-public (do-it)
                (ok true)
            )
            ";

        let call_foo = "
            (use-trait foo .foo.foo)

            (define-public (call-do-it (opt-f (optional <foo>)))
                (match opt-f
                    f (contract-call? f do-it)
                    (ok false)
                )
            )

            (call-do-it (some .foo-impl))
            ";

        crosscheck_multi_contract(
            &[
                (ContractName::from_literal("foo"), foo_trait),
                (ContractName::from_literal("foo-impl"), foo_impl),
                (ContractName::from_literal("call-foo"), call_foo),
            ],
            Ok(Some(Value::okay_true())),
        );
    }

    /// This is the same test as [multi_dynamic_define_impl_call], but it checks that it still works
    /// when we deal with the linked functions defined in stacks-core (duplication issue).
    #[test]
    fn multi_dynamic_define_impl_call_duplication_issue() {
        let foo_trait = "
            (define-trait foo
                (
                    (do-it () (response bool uint))
                )
            )
            ";

        let foo_impl = "
            (impl-trait .foo.foo)

            (define-public (do-it)
                (ok true)
            )
            ";

        let call_foo = "
            (use-trait foo .foo.foo)

            (define-public (call-do-it (opt-f (optional <foo>)))
                (match opt-f
                    f (contract-call? f do-it)
                    (ok false)
                )
            )
            ";

        let bar = "(contract-call? .call-foo call-do-it (some .foo-impl))";

        crosscheck_multi_contract(
            &[
                (ContractName::from_literal("foo"), foo_trait),
                (ContractName::from_literal("foo-impl"), foo_impl),
                (ContractName::from_literal("call-foo"), call_foo),
                (ContractName::from_literal("bar"), bar),
            ],
            Ok(Some(Value::okay_true())),
        );
    }

    #[test]
    fn contract_call_dynamic_traitreferencetype() {
        let foo = "
        (define-trait t
            ((foo () (response bool uint)))
        )

        (define-public (foo) (ok true))
    ";

        let bar = r#"
        (use-trait foo-trait .foo.t)

        (define-private (call-it (tt <foo-trait>))
            (contract-call? tt foo)
        )

        (call-it .foo)
    "#;

        crosscheck_multi_contract_with_env(
            &[
                (ContractName::from_literal("foo"), foo),
                (ContractName::from_literal("bar"), bar),
            ],
            Ok(Some(Value::okay_true())),
            TestEnvironment::new(
                clarity::types::StacksEpochId::Epoch20,
                clarity::vm::ClarityVersion::Clarity1,
            ),
        );
    }

    #[cfg(not(any(
        feature = "test-clarity-v1",
        feature = "test-clarity-v2",
        feature = "test-clarity-v3"
    )))]

    mod clarity_v4 {
        use clarity::util::hash::Sha512Trunc256Sum;
        use clarity::vm::types::PrincipalData;
        use clarity_types::{types::StandardPrincipalData, ClarityName};

        use super::*;
        use crate::tools::{crosscheck, crosscheck_with_env, evaluate};

        #[test]
        fn contract_hash_ok_returns_buff32() {
            let callee = "
(define-read-only (something)
    (ok u1)
)";
            let caller = "(contract-hash? .callee)";

            let expected = Sha512Trunc256Sum::from_data(callee.as_bytes());

            crosscheck_multi_contract(
                &[
                    (ContractName::from_literal("callee"), callee),
                    (ContractName::from_literal("caller"), caller),
                ],
                Ok(Some(
                    Value::okay(Value::buff_from(expected.0.to_vec()).unwrap()).unwrap(),
                )),
            );
        }

        #[test]
        fn contract_hash_ok_returns_buff32_with_full_addr() {
            let callee = "
(define-read-only (something)
    (ok u1)
)";
            let callee_address = StandardPrincipalData::transient().to_address();
            let caller = &format!("(contract-hash? '{}.callee)", callee_address);

            let expected = Sha512Trunc256Sum::from_data(callee.as_bytes());

            crosscheck_multi_contract(
                &[
                    (ContractName::from_literal("callee"), callee),
                    (ContractName::from_literal("caller"), caller),
                ],
                Ok(Some(
                    Value::okay(Value::buff_from(expected.0.to_vec()).unwrap()).unwrap(),
                )),
            );
        }

        #[test]
        fn contract_hash_err_u1_if_not_contract_principal() {
            crosscheck(
                "(contract-hash? tx-sender)",
                Ok(Some(Value::error(Value::UInt(1)).unwrap())),
            );
        }

        #[test]
        fn contract_hash_err_u2_if_contract_missing() {
            crosscheck(
                "(contract-hash? .does-not-exist)",
                Ok(Some(Value::error(Value::UInt(2)).unwrap())),
            );
        }

        // ==================== argument count checks ====================

        #[test]
        fn with_all_assets_unsafe_too_many_args() {
            let result = evaluate("(as-contract? ((with-all-assets-unsafe u1)) (ok true))");
            assert!(result.is_err());
            assert!(result
                .unwrap_err()
                .to_string()
                .contains("expecting 0 arguments, got 1"));
        }

        #[test]
        fn with_stx_no_args() {
            let result = evaluate("(as-contract? ((with-stx)) (ok true))");
            assert!(result.is_err());
            assert!(result
                .unwrap_err()
                .to_string()
                .contains("expecting 1 arguments, got 0"));
        }

        #[test]
        fn with_stx_too_many_args() {
            let result = evaluate("(as-contract? ((with-stx u100 u200)) (ok true))");
            assert!(result.is_err());
            assert!(result
                .unwrap_err()
                .to_string()
                .contains("expecting 1 arguments, got 2"));
        }

        #[test]
        fn with_stacking_no_args() {
            let result = evaluate("(as-contract? ((with-stacking)) (ok true))");
            assert!(result.is_err());
            assert!(result
                .unwrap_err()
                .to_string()
                .contains("expecting 1 arguments, got 0"));
        }

        #[test]
        fn with_stacking_too_many_args() {
            let result = evaluate("(as-contract? ((with-stacking u100 u200)) (ok true))");
            assert!(result.is_err());
            assert!(result
                .unwrap_err()
                .to_string()
                .contains("expecting 1 arguments, got 2"));
        }

        #[test]
        fn with_ft_no_args() {
            let result = evaluate("(as-contract? ((with-ft)) (ok true))");
            assert!(result.is_err());
            assert!(result
                .unwrap_err()
                .to_string()
                .contains("expecting 3 arguments, got 0"));
        }

        #[test]
        fn with_ft_too_few_args() {
            let result = evaluate(r#"(as-contract? ((with-ft .contract "token")) (ok true))"#);
            assert!(result.is_err());
            assert!(result
                .unwrap_err()
                .to_string()
                .contains("expecting 3 arguments, got 2"));
        }

        #[test]
        fn with_ft_too_many_args() {
            let result =
                evaluate(r#"(as-contract? ((with-ft .contract "token" u100 u200)) (ok true))"#);
            assert!(result.is_err());
            assert!(result
                .unwrap_err()
                .to_string()
                .contains("expecting 3 arguments, got 4"));
        }

        #[test]
        fn with_nft_no_args() {
            let result = evaluate("(as-contract? ((with-nft)) (ok true))");
            assert!(result.is_err());
            assert!(result
                .unwrap_err()
                .to_string()
                .contains("expecting 3 arguments, got 0"));
        }

        #[test]
        fn with_nft_too_few_args() {
            let result = evaluate(r#"(as-contract? ((with-nft .contract "token")) (ok true))"#);
            assert!(result.is_err());
            assert!(result
                .unwrap_err()
                .to_string()
                .contains("expecting 3 arguments, got 2"));
        }

        #[test]
        fn with_nft_too_many_args() {
            let result = evaluate(
                r#"(as-contract? ((with-nft .contract "token" (list u1) u99)) (ok true))"#,
            );
            assert!(result.is_err());
            assert!(result
                .unwrap_err()
                .to_string()
                .contains("expecting 3 arguments, got 4"));
        }

        // ==================== with-all-assets-unsafe ====================

        #[test]
        fn as_contract_unsafe_nft_transfer() {
            let mut env = TestEnvironment::default();
            let contract = r#"
(define-non-fungible-token token uint)

(define-public (mint-nft (asset uint))
    (begin
        (try! (nft-mint? token asset current-contract))
        (ok true)
    )
)

(define-public (transfer-token (asset uint))
    (let ((recipient tx-sender))
        (try!
            (as-contract? ((with-all-assets-unsafe))
                (try! (nft-transfer? token asset current-contract recipient))
            )
        )
        (ok true)
    )
)
"#;
            env.init_contract_with_snippet("contract", contract)
                .expect("failed to init contract");
            crosscheck_with_env(
                "(contract-call? .contract mint-nft u1)
                (contract-call? .contract transfer-token u1)",
                Ok(Some(Value::okay_true())),
                env,
            );
        }

        #[test]
        fn as_contract_unsafe_stx_transfer() {
            let mut env = TestEnvironment::default();
            let contract = r#"
(define-public (send-stx (amount uint) (recipient principal))
    (begin
        (try!
            (as-contract? ((with-all-assets-unsafe))
                (try! (stx-transfer? amount current-contract recipient))
            )
        )
        (ok true)
    )
)
"#;
            env.init_contract_with_snippet("contract", contract)
                .expect("failed to init contract");
            crosscheck_with_env(
                "(stx-transfer? u500 tx-sender .contract)
                (contract-call? .contract send-stx u50 tx-sender)",
                Ok(Some(Value::okay_true())),
                env,
            );
        }

        // ==================== with-stx ====================

        #[test]
        fn as_contract_stx_ok() {
            let mut env = TestEnvironment::default();
            let contract = r#"
(define-public (send-stx (amount uint) (recipient principal))
    (begin
        (try!
            (as-contract? ((with-stx u100))
                (try! (stx-transfer? amount current-contract recipient))
            )
        )
        (ok true)
    )
)
"#;
            env.init_contract_with_snippet("contract", contract)
                .expect("failed to init contract");
            crosscheck_with_env(
                "(stx-transfer? u500 tx-sender .contract)
                (contract-call? .contract send-stx u100 tx-sender)",
                Ok(Some(Value::okay_true())),
                env,
            );
        }

        #[test]
        fn as_contract_stx_exceeds_allowance() {
            let mut env = TestEnvironment::default();
            let contract = r#"
(define-public (send-stx (amount uint) (recipient principal))
    (begin
        (try!
            (as-contract? ((with-stx u10))
                (try! (stx-transfer? amount current-contract recipient))
            )
        )
        (ok true)
    )
)
"#;
            env.init_contract_with_snippet("contract", contract)
                .expect("failed to init contract");
            crosscheck_with_env(
                "(stx-transfer? u500 tx-sender .contract)
                (let ((result (contract-call? .contract send-stx u50 tx-sender)))
                    {error-code: result, balance: (stx-get-balance .contract)}
                )",
                Ok(Some(Value::Tuple(
                    clarity::vm::types::TupleData::from_data(vec![
                        (ClarityName::from_literal("balance"), Value::UInt(500)),
                        (
                            ClarityName::from_literal("error-code"),
                            Value::error(Value::UInt(0)).unwrap(),
                        ),
                    ])
                    .unwrap(),
                ))),
                env,
            );
        }

        #[test]
        fn as_contract_stx_no_allowance() {
            let mut env = TestEnvironment::default();
            let contract = r#"
(define-public (send-stx (amount uint) (recipient principal))
    (begin
        (try!
            (as-contract? ()
                (try! (stx-transfer? amount current-contract recipient))
            )
        )
        (ok true)
    )
)
"#;
            env.init_contract_with_snippet("contract", contract)
                .expect("failed to init contract");
            crosscheck_with_env(
                "(stx-transfer? u500 tx-sender .contract)
                (let ((result (contract-call? .contract send-stx u50 tx-sender)))
                    {error-code: result, balance: (stx-get-balance .contract)}
                )",
                Ok(Some(Value::Tuple(
                    clarity::vm::types::TupleData::from_data(vec![
                        (ClarityName::from_literal("balance"), Value::UInt(500)),
                        (
                            ClarityName::from_literal("error-code"),
                            Value::error(Value::UInt(128)).unwrap(),
                        ),
                    ])
                    .unwrap(),
                ))),
                env,
            );
        }

        // ==================== with-ft ====================

        #[test]
        fn as_contract_ft_ok() {
            let mut env = TestEnvironment::default();
            let contract = r#"
(define-fungible-token my-token)

(define-public (mint-ft (amount uint))
    (ft-mint? my-token amount current-contract)
)

(define-public (transfer-ft (amount uint) (recipient principal))
    (begin
        (try!
            (as-contract? ((with-ft .contract "my-token" u100))
                (try! (ft-transfer? my-token amount current-contract recipient))
            )
        )
        (ok true)
    )
)
"#;
            env.init_contract_with_snippet("contract", contract)
                .expect("failed to init contract");
            crosscheck_with_env(
                "(contract-call? .contract mint-ft u100)
                (contract-call? .contract transfer-ft u100 tx-sender)",
                Ok(Some(Value::okay_true())),
                env,
            );
        }

        #[test]
        fn as_contract_ft_exceeds_allowance() {
            let mut env = TestEnvironment::default();
            let contract = r#"
(define-fungible-token my-token)

(define-public (mint-ft (amount uint))
    (ft-mint? my-token amount current-contract)
)

(define-public (transfer-ft (amount uint) (recipient principal))
    (begin
        (try!
            (as-contract? ((with-ft .contract "my-token" u10))
                (try! (ft-transfer? my-token amount current-contract recipient))
            )
        )
        (ok true)
    )
)

(define-read-only (get-ft-balance)
    (ft-get-balance my-token current-contract)
)
"#;
            env.init_contract_with_snippet("contract", contract)
                .expect("failed to init contract");
            crosscheck_with_env(
                "(contract-call? .contract mint-ft u100)
                (let ((result (contract-call? .contract transfer-ft u50 tx-sender)))
                    {error-code: result, balance: (contract-call? .contract get-ft-balance)}
                )",
                Ok(Some(Value::Tuple(
                    clarity::vm::types::TupleData::from_data(vec![
                        (ClarityName::from_literal("balance"), Value::UInt(100)),
                        (
                            ClarityName::from_literal("error-code"),
                            Value::error(Value::UInt(0)).unwrap(),
                        ),
                    ])
                    .unwrap(),
                ))),
                env,
            );
        }

        #[test]
        fn as_contract_ft_no_allowance() {
            let mut env = TestEnvironment::default();
            let contract = r#"
(define-fungible-token my-token)

(define-public (mint-ft (amount uint))
    (ft-mint? my-token amount current-contract)
)

(define-public (transfer-ft (amount uint) (recipient principal))
    (begin
        (try!
            (as-contract? ()
                (try! (ft-transfer? my-token amount current-contract recipient))
            )
        )
        (ok true)
    )
)

(define-read-only (get-ft-balance)
    (ft-get-balance my-token current-contract)
)
"#;
            env.init_contract_with_snippet("contract", contract)
                .expect("failed to init contract");
            crosscheck_with_env(
                "(contract-call? .contract mint-ft u100)
                (let ((result (contract-call? .contract transfer-ft u50 tx-sender)))
                    {error-code: result, balance: (contract-call? .contract get-ft-balance)}
                )",
                Ok(Some(Value::Tuple(
                    clarity::vm::types::TupleData::from_data(vec![
                        (ClarityName::from_literal("balance"), Value::UInt(100)),
                        (
                            ClarityName::from_literal("error-code"),
                            Value::error(Value::UInt(128)).unwrap(),
                        ),
                    ])
                    .unwrap(),
                ))),
                env,
            );
        }

        // ==================== with-nft ====================

        #[test]
        fn as_contract_nft_ok() {
            let mut env = TestEnvironment::default();
            let contract = r#"
(define-non-fungible-token token uint)

(define-public (mint-nft (asset uint))
    (begin
        (try! (nft-mint? token asset current-contract))
        (ok true)
    )
)

(define-public (transfer-token (asset uint))
    (let ((recipient tx-sender))
        (try!
            (as-contract? ((with-nft .contract "token" (list u1)))
                (try! (nft-transfer? token asset current-contract recipient))
            )
        )
        (ok true)
    )
)
"#;
            env.init_contract_with_snippet("contract", contract)
                .expect("failed to init contract");
            crosscheck_with_env(
                "(contract-call? .contract mint-nft u1)
                (contract-call? .contract transfer-token u1)",
                Ok(Some(Value::okay_true())),
                env,
            );
        }

        #[test]
        fn as_contract_nft_wrong_id() {
            let mut env = TestEnvironment::default();
            let contract = r#"
(define-non-fungible-token token uint)

(define-public (mint-nft (asset uint))
    (begin
        (try! (nft-mint? token asset current-contract))
        (ok true)
    )
)

(define-public (transfer-token (asset uint))
    (let ((recipient tx-sender))
        (try!
            (as-contract? ((with-nft .contract "token" (list u999)))
                (try! (nft-transfer? token asset current-contract recipient))
            )
        )
        (ok true)
    )
)

(define-read-only (get-nft-owner (asset uint))
    (nft-get-owner? token asset)
)
"#;
            env.init_contract_with_snippet("contract", contract)
                .expect("failed to init contract");
            let contract_principal = Value::Principal(PrincipalData::Contract(
                clarity::vm::types::QualifiedContractIdentifier::new(
                    StandardPrincipalData::transient(),
                    ContractName::from_literal("contract"),
                ),
            ));
            crosscheck_with_env(
                "(contract-call? .contract mint-nft u1)
                (let ((result (contract-call? .contract transfer-token u1)))
                    {error-code: result, owner: (contract-call? .contract get-nft-owner u1)}
                )",
                Ok(Some(Value::Tuple(
                    clarity::vm::types::TupleData::from_data(vec![
                        (
                            ClarityName::from_literal("error-code"),
                            Value::error(Value::UInt(0)).unwrap(),
                        ),
                        (
                            ClarityName::from_literal("owner"),
                            Value::some(contract_principal).unwrap(),
                        ),
                    ])
                    .unwrap(),
                ))),
                env,
            );
        }

        #[test]
        fn as_contract_nft_no_allowance() {
            let mut env = TestEnvironment::default();
            let contract = r#"
(define-non-fungible-token token uint)

(define-public (mint-nft (asset uint))
    (begin
        (try! (nft-mint? token asset current-contract))
        (ok true)
    )
)

(define-public (transfer-token (asset uint))
    (let ((recipient tx-sender))
        (try!
            (as-contract? ()
                (try! (nft-transfer? token asset current-contract recipient))
            )
        )
        (ok true)
    )
)

(define-read-only (get-nft-owner (asset uint))
    (nft-get-owner? token asset)
)
"#;
            env.init_contract_with_snippet("contract", contract)
                .expect("failed to init contract");
            let contract_principal = Value::Principal(PrincipalData::Contract(
                clarity::vm::types::QualifiedContractIdentifier::new(
                    StandardPrincipalData::transient(),
                    ContractName::from_literal("contract"),
                ),
            ));
            crosscheck_with_env(
                "(contract-call? .contract mint-nft u1)
                (let ((result (contract-call? .contract transfer-token u1)))
                    {error-code: result, owner: (contract-call? .contract get-nft-owner u1)}
                )",
                Ok(Some(Value::Tuple(
                    clarity::vm::types::TupleData::from_data(vec![
                        (
                            ClarityName::from_literal("error-code"),
                            Value::error(Value::UInt(128)).unwrap(),
                        ),
                        (
                            ClarityName::from_literal("owner"),
                            Value::some(contract_principal).unwrap(),
                        ),
                    ])
                    .unwrap(),
                ))),
                env,
            );
        }

        // ==================== with-stacking ====================

        #[test]
        fn as_contract_stacking_ok() {
            let mut env = TestEnvironment::default();
            let pox4_code = include_str!("../../tests/contracts/boot-contracts/pox-4.clar");
            env.init_contract_with_snippet("pox-4", pox4_code)
                .expect("failed to init pox-4 contract");

            let wrapper = r#"
(define-public (do-delegate (amount uint) (delegate-to principal))
    (begin
        (try!
            (as-contract? ((with-stacking u1000000))
                (unwrap-panic (contract-call? .pox-4 delegate-stx
                    amount delegate-to none none))
            )
        )
        (ok true)
    )
)
"#;
            env.init_contract_with_snippet("wrapper", wrapper)
                .expect("failed to init wrapper contract");
            crosscheck_with_env(
                "(contract-call? .wrapper do-delegate u1000 tx-sender)",
                Ok(Some(Value::okay_true())),
                env,
            );
        }

        #[test]
        fn as_contract_stacking_pox_indirect() {
            let mut env = TestEnvironment::default();
            let pox4_code = include_str!("../../tests/contracts/boot-contracts/pox-4.clar");
            env.init_contract_with_snippet("pox-4", pox4_code)
                .expect("failed to init pox-4 contract");

            let intermediary = r#"
(define-public (do-delegate (amount uint) (delegate-to principal))
    (contract-call? .pox-4 delegate-stx amount delegate-to none none)
)
"#;
            env.init_contract_with_snippet("intermediary", intermediary)
                .expect("failed to init intermediary contract");

            // setup-allowance grants the intermediary permission to call pox-4
            // on behalf of the wrapper (as-contract? changes tx-sender to wrapper)
            let wrapper = r#"
(define-public (setup-allowance)
    (begin
        (try!
            (as-contract? ((with-all-assets-unsafe))
                (unwrap-panic (contract-call? .pox-4 allow-contract-caller .intermediary none))
            )
        )
        (ok true)
    )
)

(define-public (delegate-via-intermediary (amount uint) (delegate-to principal))
    (begin
        (try!
            (as-contract? ((with-stacking u1000000))
                (unwrap-panic (contract-call? .intermediary do-delegate
                    amount delegate-to))
            )
        )
        (ok true)
    )
)
"#;
            env.init_contract_with_snippet("wrapper", wrapper)
                .expect("failed to init wrapper contract");
            crosscheck_with_env(
                "(contract-call? .wrapper setup-allowance)
                (contract-call? .wrapper delegate-via-intermediary u1000 tx-sender)",
                Ok(Some(Value::okay_true())),
                env,
            );
        }

        #[test]
        fn as_contract_stacking_and_stx_pox() {
            let mut env = TestEnvironment::default();
            let pox4_code = include_str!("../../tests/contracts/boot-contracts/pox-4.clar");
            env.init_contract_with_snippet("pox-4", pox4_code)
                .expect("failed to init pox-4 contract");

            let wrapper = r#"
(define-public (delegate-and-send-stx (delegate-amount uint) (stx-amount uint) (recipient principal))
    (begin
        (try!
            (as-contract? ((with-stacking u1000000) (with-stx u500))
                (begin
                    (unwrap-panic (contract-call? .pox-4 delegate-stx
                        delegate-amount recipient none none))
                    (try! (stx-transfer? stx-amount current-contract recipient))
                )
            )
        )
        (ok true)
    )
)
"#;
            env.init_contract_with_snippet("wrapper", wrapper)
                .expect("failed to init wrapper contract");

            crosscheck_with_env(
                "(stx-transfer? u1000 tx-sender .wrapper)
                (contract-call? .wrapper delegate-and-send-stx u5000 u200 tx-sender)",
                Ok(Some(Value::okay_true())),
                env,
            );
        }

        // ==================== mixed / multiple allowances ====================

        #[test]
        fn as_contract_wrong_allowance_type() {
            let mut env = TestEnvironment::default();
            let contract = r#"
(define-fungible-token my-token)

(define-public (send-stx (amount uint) (recipient principal))
    (begin
        (try!
            (as-contract? ((with-ft .contract "my-token" u100))
                (try! (stx-transfer? amount current-contract recipient))
            )
        )
        (ok true)
    )
)
"#;
            env.init_contract_with_snippet("contract", contract)
                .expect("failed to init contract");
            crosscheck_with_env(
                "(stx-transfer? u500 tx-sender .contract)
                (let ((result (contract-call? .contract send-stx u50 tx-sender)))
                    {error-code: result, balance: (stx-get-balance .contract)}
                )",
                Ok(Some(Value::Tuple(
                    clarity::vm::types::TupleData::from_data(vec![
                        (ClarityName::from_literal("balance"), Value::UInt(500)),
                        (
                            ClarityName::from_literal("error-code"),
                            Value::error(Value::UInt(128)).unwrap(),
                        ),
                    ])
                    .unwrap(),
                ))),
                env,
            );
        }

        #[test]
        fn as_contract_multiple_stx_second_violation() {
            let mut env = TestEnvironment::default();
            let contract = r#"
(define-public (send-stx (amount uint) (recipient principal))
    (begin
        (try!
            (as-contract? ((with-stx u100) (with-stx u20))
                (try! (stx-transfer? amount current-contract recipient))
            )
        )
        (ok true)
    )
)
"#;
            env.init_contract_with_snippet("contract", contract)
                .expect("failed to init contract");
            crosscheck_with_env(
                "(stx-transfer? u500 tx-sender .contract)
                (let ((result (contract-call? .contract send-stx u40 tx-sender)))
                    {error-code: result, balance: (stx-get-balance .contract)}
                )",
                Ok(Some(Value::Tuple(
                    clarity::vm::types::TupleData::from_data(vec![
                        (ClarityName::from_literal("balance"), Value::UInt(500)),
                        (
                            ClarityName::from_literal("error-code"),
                            Value::error(Value::UInt(1)).unwrap(),
                        ),
                    ])
                    .unwrap(),
                ))),
                env,
            );
        }

        #[test]
        fn as_contract_mixed_stx_ft_nft() {
            let mut env = TestEnvironment::default();
            let contract = r#"
(define-fungible-token my-token)
(define-non-fungible-token my-nft uint)

(define-public (mint-ft (amount uint))
    (ft-mint? my-token amount current-contract)
)

(define-public (mint-nft (asset uint))
    (begin
        (try! (nft-mint? my-nft asset current-contract))
        (ok true)
    )
)

(define-public (transfer-all (ft-amount uint) (nft-id uint) (stx-amount uint))
    (let ((recipient tx-sender))
        (try!
            (as-contract?
                ((with-stx u500)
                 (with-ft .contract "my-token" u200)
                 (with-nft .contract "my-nft" (list u1 u2)))
                (begin
                    (try! (stx-transfer? stx-amount current-contract recipient))
                    (try! (ft-transfer? my-token ft-amount current-contract recipient))
                    (try! (nft-transfer? my-nft nft-id current-contract recipient))
                )
            )
        )
        (ok true)
    )
)
"#;
            env.init_contract_with_snippet("contract", contract)
                .expect("failed to init contract");
            crosscheck_with_env(
                "(stx-transfer? u1000 tx-sender .contract)
                (contract-call? .contract mint-ft u500)
                (contract-call? .contract mint-nft u1)
                (contract-call? .contract transfer-all u100 u1 u200)",
                Ok(Some(Value::okay_true())),
                env,
            );
        }

        // ==================== nested as-contract? ====================

        #[test]
        fn as_contract_nested_unsafe_outer_nft_inner() {
            let mut env = TestEnvironment::default();
            let contract = r#"
(define-non-fungible-token token uint)

(define-public (mint-nft (asset uint))
    (begin
        (try! (nft-mint? token asset current-contract))
        (ok true)
    )
)

(define-public (transfer-token (asset uint))
    (let ((recipient tx-sender))
        (try!
            (as-contract? ((with-all-assets-unsafe))
                (try!
                    (as-contract? ((with-nft .contract "token" (list u1)))
                        (try! (nft-transfer? token asset current-contract recipient))
                    )
                )
            )
        )
        (ok true)
    )
)
"#;
            env.init_contract_with_snippet("contract", contract)
                .expect("failed to init contract");
            crosscheck_with_env(
                "(contract-call? .contract mint-nft u1)
                (contract-call? .contract transfer-token u1)",
                Ok(Some(Value::okay_true())),
                env,
            );
        }

        #[test]
        fn as_contract_nested_inner_nft_violation() {
            let mut env = TestEnvironment::default();
            let contract = r#"
(define-non-fungible-token token uint)

(define-public (mint-nft (asset uint))
    (begin
        (try! (nft-mint? token asset current-contract))
        (ok true)
    )
)

(define-public (transfer-token (asset uint))
    (let ((recipient tx-sender))
        (try!
            (as-contract? ((with-all-assets-unsafe))
                (try!
                    (as-contract? ((with-nft .contract "token" (list u999)))
                        (try! (nft-transfer? token asset current-contract recipient))
                    )
                )
            )
        )
        (ok true)
    )
)
"#;
            env.init_contract_with_snippet("contract", contract)
                .expect("failed to init contract");
            crosscheck_with_env(
                "(contract-call? .contract mint-nft u1)
                (contract-call? .contract transfer-token u1)",
                Ok(Some(Value::error(Value::UInt(0)).unwrap())),
                env,
            );
        }

        #[test]
        fn as_contract_nested_cross_contract() {
            let mut env = TestEnvironment::default();
            let callee = r#"
(define-non-fungible-token token uint)

(define-public (mint-nft (asset uint))
    (begin
        (try! (nft-mint? token asset current-contract))
        (ok true)
    )
)

(define-public (transfer-nft (asset uint) (recipient principal))
    (begin
        (try! (nft-transfer? token asset current-contract recipient))
        (ok true)
    )
)
"#;
            let caller = r#"
(define-public (do-transfer (asset uint))
    (let ((recipient tx-sender))
        (try!
            (as-contract? ((with-all-assets-unsafe))
                (try! (contract-call? .callee transfer-nft asset recipient))
            )
        )
        (ok true)
    )
)
"#;
            env.init_contract_with_snippet("callee", callee)
                .expect("failed to init callee");
            env.init_contract_with_snippet("caller", caller)
                .expect("failed to init caller");
            crosscheck_with_env(
                "(contract-call? .callee mint-nft u1)
                (contract-call? .caller do-transfer u1)",
                Ok(Some(Value::okay_true())),
                env,
            );
        }

        #[test]
        fn as_contract_nested_stx_outer_ft_inner() {
            let mut env = TestEnvironment::default();
            let contract = r#"
(define-fungible-token my-token)

(define-public (mint-ft (amount uint))
    (ft-mint? my-token amount current-contract)
)

(define-public (transfer-both (stx-amount uint) (ft-amount uint) (recipient principal))
    (begin
        (try!
            (as-contract? ((with-stx u200) (with-ft .contract "my-token" u100))
                (begin
                    (try! (stx-transfer? stx-amount current-contract recipient))
                    (try!
                        (as-contract? ((with-ft .contract "my-token" u100))
                            (try! (ft-transfer? my-token ft-amount current-contract recipient))
                        )
                    )
                )
            )
        )
        (ok true)
    )
)

(define-read-only (get-ft-balance)
    (ft-get-balance my-token current-contract)
)
"#;
            env.init_contract_with_snippet("contract", contract)
                .expect("failed to init contract");
            crosscheck_with_env(
                "(stx-transfer? u500 tx-sender .contract)
                (contract-call? .contract mint-ft u200)
                (let ((result (contract-call? .contract transfer-both u100 u50 tx-sender)))
                    {result: result,
                     stx-balance: (stx-get-balance .contract),
                     ft-balance: (contract-call? .contract get-ft-balance)})",
                Ok(Some(Value::Tuple(
                    clarity::vm::types::TupleData::from_data(vec![
                        (ClarityName::from_literal("ft-balance"), Value::UInt(150)),
                        (ClarityName::from_literal("result"), Value::okay_true()),
                        (ClarityName::from_literal("stx-balance"), Value::UInt(400)),
                    ])
                    .unwrap(),
                ))),
                env,
            );
        }

        #[test]
        fn as_contract_nested_inner_ft_violation_rollback() {
            let mut env = TestEnvironment::default();
            let contract = r#"
(define-fungible-token my-token)

(define-public (mint-ft (amount uint))
    (ft-mint? my-token amount current-contract)
)

(define-public (transfer-both (stx-amount uint) (ft-amount uint) (recipient principal))
    (begin
        (try!
            (as-contract? ((with-stx u200))
                (begin
                    (try! (stx-transfer? stx-amount current-contract recipient))
                    (try!
                        (as-contract? ((with-ft .contract "my-token" u10))
                            (try! (ft-transfer? my-token ft-amount current-contract recipient))
                        )
                    )
                )
            )
        )
        (ok true)
    )
)

(define-read-only (get-ft-balance)
    (ft-get-balance my-token current-contract)
)
"#;
            env.init_contract_with_snippet("contract", contract)
                .expect("failed to init contract");
            // Inner FT allowance u10 is too low for u50 transfer.
            // The inner violation (err u0) propagates via try!, causing full rollback.
            crosscheck_with_env(
                "(stx-transfer? u500 tx-sender .contract)
                (contract-call? .contract mint-ft u200)
                (let ((result (contract-call? .contract transfer-both u100 u50 tx-sender)))
                    {error-code: result,
                     stx-balance: (stx-get-balance .contract),
                     ft-balance: (contract-call? .contract get-ft-balance)}
                )",
                Ok(Some(Value::Tuple(
                    clarity::vm::types::TupleData::from_data(vec![
                        (
                            ClarityName::from_literal("error-code"),
                            Value::error(Value::UInt(0)).unwrap(),
                        ),
                        (ClarityName::from_literal("ft-balance"), Value::UInt(200)),
                        (ClarityName::from_literal("stx-balance"), Value::UInt(500)),
                    ])
                    .unwrap(),
                ))),
                env,
            );
        }

        #[test]
        fn as_contract_nested_nft_outer_stx_inner() {
            let mut env = TestEnvironment::default();
            let contract = r#"
(define-non-fungible-token token uint)

(define-public (mint-nft (asset uint))
    (begin
        (try! (nft-mint? token asset current-contract))
        (ok true)
    )
)

(define-public (transfer-nft-and-stx (asset uint) (stx-amount uint))
    (let ((recipient tx-sender))
        (try!
            (as-contract? ((with-nft .contract "token" (list u1)) (with-stx u200))
                (begin
                    (try! (nft-transfer? token asset current-contract recipient))
                    (try!
                        (as-contract? ((with-stx u200))
                            (try! (stx-transfer? stx-amount current-contract recipient))
                        )
                    )
                )
            )
        )
        (ok true)
    )
)
"#;
            env.init_contract_with_snippet("contract", contract)
                .expect("failed to init contract");
            crosscheck_with_env(
                "(stx-transfer? u500 tx-sender .contract)
                (contract-call? .contract mint-nft u1)
                (contract-call? .contract transfer-nft-and-stx u1 u100)",
                Ok(Some(Value::okay_true())),
                env,
            );
        }
    }
}
