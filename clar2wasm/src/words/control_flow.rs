use clarity::vm::types::TypeSignature;
use clarity::vm::{ClarityName, SymbolicExpression};
use walrus::ir::{IfElse, UnaryOp};

use super::{ComplexWord, Word};
use crate::check_args;
use crate::cost::WordCharge;
use crate::error_mapping::ErrorMap;
use crate::wasm_generator::{drop_value, ArgumentsExt, GeneratorError, WasmGenerator};
use crate::wasm_utils::ArgumentCountCheck;

#[derive(Debug)]
pub struct Begin;

impl Word for Begin {
    fn name(&self) -> ClarityName {
        ClarityName::from_literal("begin")
    }
}

impl ComplexWord for Begin {
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
            1,
            args.len(),
            ArgumentCountCheck::AtLeast
        );

        self.charge(generator, builder, 0)?;

        generator.set_expr_type(
            args.last().ok_or_else(|| {
                GeneratorError::TypeError("begin must have at least one arg".to_string())
            })?,
            generator
                .get_expr_type(expr)
                .ok_or_else(|| GeneratorError::TypeError("begin must be typed".to_owned()))?
                .clone(),
        )?;
        generator.traverse_statement_list(builder, args)
    }
}

#[derive(Debug)]
pub struct UnwrapPanic;

impl Word for UnwrapPanic {
    fn name(&self) -> ClarityName {
        ClarityName::from_literal("unwrap-panic")
    }
}

impl ComplexWord for UnwrapPanic {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 1, args.len(), ArgumentCountCheck::Exact);

        self.charge(generator, builder, 0)?;

        let input = args.get_expr(0)?;
        generator.traverse_expr(builder, input)?;
        // There must be either an `optional` or a `response` on the top of the
        // stack. Both use an i32 indicator, where 0 means `none` or `err`. In
        // both cases, if this indicator is a 0, then we need to panic.

        // Get the type of the input expression
        let input_ty = generator
            .get_expr_type(input)
            .ok_or_else(|| {
                GeneratorError::TypeError("'unwrap-err' input expression must be typed".to_owned())
            })?
            .clone();

        match &input_ty {
            TypeSignature::OptionalType(val_ty) => {
                // For the optional case, e.g. `(unwrap-panic (some 1))`, the stack
                // will look like:
                // 1 -- some value
                // 1 -- indicator
                // We need to get to the indicator, so we can pop the some value and
                // store it in a local, then check the indicator. If it's 0, we need to
                // trigger a runtime error. If it's a 1, we just push the some value
                // back onto the stack and continue execution.

                // Save the value in locals
                let val_locals = generator.save_to_locals(builder, val_ty, true);

                // If the indicator is 0, throw a runtime error
                let if_id = {
                    let mut if_case = builder.dangling_instr_seq(None);
                    if_case.i32_const(ErrorMap::Panic as i32).call(
                        generator
                            .module
                            .funcs
                            .by_name("stdlib.runtime-error")
                            .ok_or_else(|| {
                                GeneratorError::InternalError(
                                    "stdlib.runtime-error not found".to_owned(),
                                )
                            })?,
                    );
                    if_case.id()
                };

                let else_id = {
                    let else_case = builder.dangling_instr_seq(None);
                    else_case.id()
                };

                builder.unop(UnaryOp::I32Eqz).instr(IfElse {
                    consequent: if_id,
                    alternative: else_id,
                });

                // Otherwise, push the value back onto the stack
                for val_local in val_locals {
                    builder.local_get(val_local);
                }

                Ok(())
            }
            TypeSignature::ResponseType(inner_types) => {
                // Ex. `(unwrap-panic (ok 1))`, where the value type is
                // `(response uint uint)`, the stack will look like:
                // 0 -- err value
                // 1 -- ok value
                // 1 -- indicator
                // We need to get to the indicator, so we can drop the err value, since
                // that is not needed, then we can pop the ok value and store them in a
                // local. Now we can check the indicator. If it's 0, we need to trigger
                // a runtime error. If it's a 1, we just push the ok value back onto
                // the stack and continue execution.

                let (ok_ty, err_ty) = &**inner_types;

                // Drop the err value
                drop_value(builder, err_ty);

                // Save the ok value in locals
                let ok_val_locals = generator.save_to_locals(builder, ok_ty, true);

                // If the indicator is 0, throw a runtime error
                let if_id = {
                    let mut if_case = builder.dangling_instr_seq(None);
                    if_case.i32_const(ErrorMap::Panic as i32).call(
                        generator
                            .module
                            .funcs
                            .by_name("stdlib.runtime-error")
                            .ok_or_else(|| {
                                GeneratorError::InternalError(
                                    "stdlib.runtime-error not found".to_owned(),
                                )
                            })?,
                    );
                    if_case.id()
                };

                let else_id = {
                    let else_case = builder.dangling_instr_seq(None);
                    else_case.id()
                };

                builder.unop(UnaryOp::I32Eqz).instr(IfElse {
                    consequent: if_id,
                    alternative: else_id,
                });

                // Otherwise, push the value back onto the stack
                for val_local in ok_val_locals {
                    builder.local_get(val_local);
                }

                Ok(())
            }
            _ => Err(GeneratorError::NotImplemented),
        }
    }
}

#[derive(Debug)]
pub struct UnwrapErrPanic;

impl Word for UnwrapErrPanic {
    fn name(&self) -> ClarityName {
        ClarityName::from_literal("unwrap-err-panic")
    }
}

impl ComplexWord for UnwrapErrPanic {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 1, args.len(), ArgumentCountCheck::Exact);

        self.charge(generator, builder, 0)?;

        let input = args.get_expr(0)?;
        generator.traverse_expr(builder, input)?;
        // The input must be a `response` type. It uses an i32 indicator, where
        // 0 means `err`. If this indicator is a 1, then we need to panic.

        // Get the type of the input expression
        let input_ty = generator
            .get_expr_type(input)
            .ok_or_else(|| {
                GeneratorError::TypeError(
                    "'unwrap-err-panic' input expression must be typed".to_owned(),
                )
            })?
            .clone();

        match &input_ty {
            TypeSignature::ResponseType(inner_types) => {
                // Ex. `(unwrap-err-panic (err 1))`, where the value type is
                // `(response uint uint)`, the stack will look like:
                // 1 -- err value
                // 0 -- ok value
                // 0 -- indicator
                // We need to get to the indicator, so we can save the err
                // value in a local, then drop the ok value, since this is not
                // needed. After that, we can check the indicator. If it's a 1,
                // we need to trigger a runtime error. If it's a 0, we just
                // push the err value back onto the stack and continue
                // execution.

                let (ok_ty, err_ty) = &**inner_types;

                // Save the err value in locals
                let err_val_locals = generator.save_to_locals(builder, err_ty, true);

                // Drop the err value
                drop_value(builder, ok_ty);

                // If the indicator is 0, throw a runtime error
                let if_id = {
                    let if_case = builder.dangling_instr_seq(None);
                    if_case.id()
                };

                let else_id = {
                    let mut else_case = builder.dangling_instr_seq(None);
                    else_case.i32_const(ErrorMap::Panic as i32).call(
                        generator
                            .module
                            .funcs
                            .by_name("stdlib.runtime-error")
                            .ok_or_else(|| {
                                GeneratorError::InternalError(
                                    "stdlib.runtime-error not found".to_owned(),
                                )
                            })?,
                    );
                    else_case.id()
                };

                builder.unop(UnaryOp::I32Eqz).instr(IfElse {
                    consequent: if_id,
                    alternative: else_id,
                });

                // Otherwise, push the value back onto the stack
                for val_local in err_val_locals {
                    builder.local_get(val_local);
                }

                Ok(())
            }
            _ => Err(GeneratorError::NotImplemented),
        }
    }
}

#[cfg(test)]
mod tests {
    use clarity::vm::errors::{RuntimeError, VmExecutionError};
    use clarity::vm::Value;

    use crate::tools::{crosscheck, crosscheck_expect_failure, evaluate};

    #[test]
    fn begin_less_than_one_arg() {
        let result = evaluate("(begin)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting >= 1 arguments, got 0"));
    }

    #[test]
    fn unwrap_panic_less_than_one_arg() {
        let result = evaluate("(unwrap-panic)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 1 arguments, got 0"));
    }

    #[test]
    fn unwrap_panic_more_than_one_arg() {
        let result = evaluate("(unwrap-panic (some 1) 2)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 1 arguments, got 2"));
    }

    #[test]
    fn unwrap_err_panic_less_than_one_arg() {
        let result = evaluate("(unwrap-err-panic)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 1 arguments, got 0"));
    }

    #[test]
    fn unwrap_err_panic_more_than_one_arg() {
        let result = evaluate("(unwrap-err-panic (some x) 2)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 1 arguments, got 2"));
    }

    #[test]
    fn test_unwrap_panic_some() {
        crosscheck("(unwrap-panic (some u1))", Ok(Some(Value::UInt(1))))
    }

    #[test]
    fn test_unwrap_panic_none() {
        let snippet = r#"
(define-private (unwrap-opt (x (optional uint)))
    (unwrap-panic x)
)
(unwrap-opt none)
        "#;

        crosscheck(
            snippet,
            Err(VmExecutionError::Runtime(
                RuntimeError::UnwrapFailure,
                Some(Vec::new()),
            )),
        )
    }

    #[test]
    fn test_unwrap_panic_ok() {
        crosscheck("(unwrap-panic (ok u2))", Ok(Some(Value::UInt(2))));
    }

    #[test]
    fn test_unwrap_panic_err() {
        let snippet = r#"
(define-private (unwrap-opt (x (response uint uint)))
    (unwrap-panic x)
)
(unwrap-opt (err u42))"#;

        crosscheck(
            snippet,
            Err(VmExecutionError::Runtime(
                RuntimeError::UnwrapFailure,
                Some(Vec::new()),
            )),
        )
    }

    #[test]
    fn test_unwrap_err_panic_err() {
        crosscheck("(unwrap-err-panic (err u1))", Ok(Some(Value::UInt(1))))
    }

    #[test]
    fn test_unwrap_err_panic_ok() {
        let snippet = r#"
(define-private (unwrap-opt (x (response uint uint)))
    (unwrap-err-panic x)
)
(unwrap-opt (ok u42))"#;

        crosscheck(
            snippet,
            Err(VmExecutionError::Runtime(
                RuntimeError::UnwrapFailure,
                Some(Vec::new()),
            )),
        )
    }

    /// Verify that the full response type is set correctly for the last
    /// expression in a `begin` block.
    #[test]
    fn begin_response_type_bug() -> Result<(), VmExecutionError> {
        evaluate(
            r#"
(define-private (foo)
    (err u1)
)
(define-read-only (get-count-at-block (block uint))
    (begin
        (unwrap-err! (foo) (err u100))
        (ok u100)
    )
)
            "#,
        )?;
        Ok(())
    }

    #[test]
    fn unwrap_none() {
        crosscheck_expect_failure(
            r#"
              (define-public (unwrap-none)
                (ok (try-opt none)))
              (unwrap-none)
            "#,
        );
    }

    #[test]
    fn unwrap_error() {
        crosscheck_expect_failure(
            r#"
              (define-public (unwrap-error)
                (ok (try-res (err u1))))
              (unwrap-error)
            "#,
        );
    }

    #[test]
    fn unwrap_some() {
        crosscheck(
            "
    (define-private (try-opt (x (optional uint)))
      (unwrap-panic x))

    (define-public (unwrap-some)
      (ok (try-opt (some u1))))

    (unwrap-some)
    ",
            evaluate("(ok u1)"),
        )
    }

    #[test]
    fn unwrap_ok() {
        crosscheck(
            "
    (define-private (try-res (x (response uint uint)))
      (unwrap-panic x))

    (define-public (unwrap-ok)
      (ok (try-res (ok u1))))

    (unwrap-ok)
    ",
            evaluate("(ok u1)"),
        );
    }

    #[test]
    fn begin() {
        crosscheck(
            "
 (define-public (simple)
   (ok
     (begin
       (+ 1 2)
       (+ 3 4))))

(simple)
",
            evaluate("(ok 7)"),
        )
    }
}
