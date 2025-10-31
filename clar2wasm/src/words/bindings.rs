use clarity::vm::{ClarityName, SymbolicExpression};

use crate::check_args;
use crate::cost::WordCharge;
use crate::wasm_generator::{ArgumentsExt, GeneratorError, WasmGenerator};
use crate::wasm_utils::{check_argument_count, ArgumentCountCheck};
use crate::words::{ComplexWord, Word};

#[derive(Debug)]
pub struct Let;

impl Word for Let {
    fn name(&self) -> ClarityName {
        "let".into()
    }
}

impl ComplexWord for Let {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        let args_len = args.len();

        check_args!(generator, builder, 2, args_len, ArgumentCountCheck::AtLeast);

        self.charge(generator, builder, args_len as u32)?;

        let bindings = args.get_list(0)?;

        // Save the current named locals
        let saved_locals = generator.bindings.clone();

        // Traverse the bindings
        for i in 0..bindings.len() {
            let pair = bindings.get_list(i)?;
            let name = pair.get_name(0)?;
            let value = pair.get_expr(1)?;
            // make sure name does not collide with builtin symbols
            if generator.is_reserved_name(name) {
                return Err(GeneratorError::InternalError(format!(
                    "Name already used {name:?}"
                )));
            }

            // Traverse the value
            generator.traverse_expr(builder, value)?;

            // Store store the value in locals, and save to the var map
            let ty = generator
                .get_expr_type(value)
                .ok_or_else(|| {
                    GeneratorError::TypeError("let value expression must be typed".to_owned())
                })?
                .clone();
            let locals = generator.save_to_locals(builder, &ty, true);

            // Add these named locals to the map
            generator.bindings.insert(name.clone(), ty, locals);
        }

        // WORKAROUND: need to set the last statement type to the type of the let expression
        let expr_ty = generator
            .get_expr_type(_expr)
            .ok_or_else(|| GeneratorError::TypeError("let expression should be typed".to_owned()))?
            .clone();

        generator.set_expr_type(
            args.last().ok_or_else(|| {
                GeneratorError::TypeError(
                    "let expression should have at least one statement".to_owned(),
                )
            })?,
            expr_ty,
        )?;

        // Traverse the body
        generator.traverse_statement_list(builder, &args[1..])?;

        // Restore the named locals.
        generator.bindings = saved_locals;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use clarity::vm::errors::{Error, ShortReturnType};
    use clarity::vm::Value;

    use crate::tools::{crosscheck, crosscheck_compare_only, crosscheck_expect_failure, evaluate};

    #[cfg(feature = "test-clarity-v1")]
    mod clarity_v1 {
        use clarity::types::StacksEpochId;

        use super::*;
        use crate::tools::crosscheck_with_epoch;

        #[test]
        fn validate_let_epoch() {
            // Epoch20
            crosscheck_with_epoch(
                "(let ((index-of? 2)) (+ index-of? index-of?))",
                Ok(Some(Value::Int(4))),
                StacksEpochId::Epoch20,
            );
        }
    }

    #[test]
    fn let_less_than_two_args() {
        let result = evaluate("(let ((current-count (count u1))))");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting >= 2 arguments, got 1"));
    }

    #[test]
    fn clar_let_disallow_builtin_names() {
        // It's not allowed to use names of user-defined functions as bindings
        const ERR: &str = "
(define-private (test)
 (let ((+ u3))
   +))";

        crosscheck_expect_failure(&format!("{ERR} (test)"));
    }

    #[test]
    fn clar_let_disallow_user_defined_names() {
        // It's not allowed to use names of user-defined functions as bindings
        const ERR: &str = "
(define-private (test)
 (let ((test u3))
    test))";

        crosscheck_expect_failure(&format!("{ERR} (test)"));
    }

    #[test]
    fn let_with_multiple_statements() {
        crosscheck_compare_only(
            r#"
                (define-data-var count uint u0)

                (define-public (decrement)
                    (let ((current-count (var-get count)))
                        (asserts! (> current-count u0) (err u1))
                        (ok (var-set count (- current-count u1)))
                    )
                )
            "#,
        )
    }

    #[test]
    fn validate_let() {
        // Reserved keyword
        crosscheck_expect_failure("(let ((map 2)) (+ map map))");

        // Custom variable name
        crosscheck("(let ((a 2)) (+ a a))", Ok(Some(Value::Int(4))));

        // Custom variable name duplicate
        crosscheck_expect_failure("(let ((a 2) (a 3)) (+ a a))");
    }

    #[test]
    fn let_with_try_ok() {
        let snippet = r#"
            (let
                ( (ok-val true) (err-no u42) )
                (try! (if true (ok ok-val) (err err-no)))
                "result"
            )
        "#;

        crosscheck(
            snippet,
            Ok(Some(
                Value::string_ascii_from_bytes(b"result".to_vec()).unwrap(),
            )),
        );
    }

    #[test]
    fn let_with_try_err() {
        let snippet = r#"
            (let
                ( (ok-val true) (err-no u42) )
                (try! (if false (ok ok-val) (err err-no)))
                "result"
            )
        "#;

        crosscheck(
            snippet,
            Err(Error::ShortReturn(ShortReturnType::ExpectedValue(
                Box::new(Value::err_uint(42)),
            ))),
        );
    }

    #[test]
    fn let_with_try_in_function_ok() {
        let snippet = r#"
            (define-private (foo)
                (let
                    ( (ok-val true) (err-no u42) )
                    (try! (if true (ok ok-val) (err err-no)))
                    (ok "result")
                )
            )
            (foo)
        "#;

        crosscheck(
            snippet,
            Ok(Some(
                Value::okay(Value::string_ascii_from_bytes(b"result".to_vec()).unwrap()).unwrap(),
            )),
        );
    }

    #[test]
    fn let_with_try_in_function_err() {
        let snippet = r#"
            (define-private (foo)
                (let
                    ( (ok-val true) (err-no u42) )
                    (try! (if false (ok ok-val) (err err-no)))
                    (ok "result")
                )
            )
            (foo)
        "#;

        crosscheck(snippet, Ok(Some(Value::err_uint(42))));
    }
}
