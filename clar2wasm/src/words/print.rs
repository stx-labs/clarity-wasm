use clarity::vm::types::{ASCIIData, CharType};
use clarity::vm::{ClarityName, SymbolicExpression};

use super::{ComplexWord, Word};
use crate::check_args;
use crate::cost::WordCharge;
use crate::wasm_generator::{ArgumentsExt, GeneratorError, WasmGenerator};
use crate::wasm_utils::{signature_from_string, ArgumentCountCheck};

#[derive(Debug)]
pub struct Print;

impl Word for Print {
    fn name(&self) -> ClarityName {
        ClarityName::from_literal("print")
    }
}

impl ComplexWord for Print {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 1, args.len(), ArgumentCountCheck::Exact);

        let value = args.get_expr(0)?;

        // Traverse the value, leaving it on the data stack
        generator.traverse_expr(builder, value)?;

        // Save the value to locals
        let ty = generator
            .get_expr_type(value)
            .ok_or_else(|| {
                GeneratorError::TypeError("print value expression must be typed".to_owned())
            })?
            .clone();
        let val_locals = generator.save_to_locals(builder, &ty, true);

        let ty_for_serde = generator.type_for_serialization(&ty);
        let serialized_ty = ty_for_serde.to_string();
        // Ensure (at compile time) type can be reconstructed
        signature_from_string(
            &serialized_ty,
            generator.contract_analysis.clarity_version,
            generator.contract_analysis.epoch,
        )
        .map_err(|e| {
            GeneratorError::TypeError(format!("serialized type cannot be deserialized: {e:?}"))
        })?;
        let serialized_ty = serialized_ty.bytes().collect();

        let (serialized_ty_offset, serialized_ty_len) =
            generator.add_clarity_string_literal(&CharType::ASCII(ASCIIData {
                data: serialized_ty,
            }))?;

        self.charge(generator, builder, serialized_ty_len)?;

        // Push the value back onto the data stack
        for val_local in &val_locals {
            builder.local_get(*val_local);
        }
        // Storing expr to memory to pass a reference to `print`
        let (value_offset, value_length) =
            generator.create_call_stack_local(builder, &ty, false, true);
        generator.write_to_memory(builder, value_offset, 0, &ty)?;
        // Then load the offset and length onto the stack
        builder.local_get(value_offset).i32_const(value_length);

        // Push type offset and length onto the stack
        builder
            .i32_const(serialized_ty_offset as i32)
            .i32_const(serialized_ty_len as i32);

        // Call the host interface function, `print`
        builder.call(generator.func_by_name("stdlib.print"));

        // Print always returns its input, so read the input value back from
        // the locals.
        for val_local in val_locals {
            builder.local_get(val_local);
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use clarity::types::StacksEpochId;
    use clarity::vm::types::{
        ASCIIData, CharType, ListTypeData, SequenceData, TupleData, UTF8Data,
    };
    use clarity::vm::{ClarityName, ContractName, Value};

    use crate::tools::{crosscheck, evaluate};

    #[test]
    fn print_no_args() {
        let result = evaluate("(print)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 1 arguments, got 0"));
    }

    #[test]
    fn print_more_than_one_arg() {
        let result = evaluate("(print 21 21)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 1 arguments, got 2"));
    }

    #[test]
    fn test_simple() {
        crosscheck("(print 42)", Ok(Some(Value::Int(42))));
    }

    #[test]
    fn test_contract_call() {
        let first_contract_name = ContractName::from_literal("callee");
        let first_snippet = r#"
(define-public (foo (a int))
  (ok (print a))
)
            "#;

        let second_contract_name = ContractName::from_literal("caller");
        let second_snippet = "(unwrap-panic (contract-call? .callee foo 42))";

        crate::tools::crosscheck_multi_contract(
            &[
                (first_contract_name, first_snippet),
                (second_contract_name, second_snippet),
            ],
            Ok(Some(Value::Int(42))),
        );
    }

    #[test]
    fn test_empty_list() {
        crosscheck(
            "(print (list))",
            Ok(Some(
                Value::list_with_type(
                    &StacksEpochId::latest(),
                    vec![],
                    ListTypeData::new_list(clarity::vm::types::TypeSignature::NoType, 0).unwrap(),
                )
                .unwrap(),
            )),
        );
    }

    #[test]
    fn test_complex_notype() {
        let notype_list = Value::list_with_type(
            &StacksEpochId::latest(),
            vec![],
            ListTypeData::new_list(clarity::vm::types::TypeSignature::NoType, 0).unwrap(),
        )
        .unwrap();
        let none_list = Value::cons_list(vec![Value::none()], &StacksEpochId::latest()).unwrap();
        let err = Value::err_uint(1);
        crosscheck(
            "(print { a: (list), b: (list none), c: (err u1) })",
            Ok(Some(Value::Tuple(
                TupleData::from_data(vec![
                    (ClarityName::from_literal("a"), notype_list),
                    (ClarityName::from_literal("b"), none_list),
                    (ClarityName::from_literal("c"), err),
                ])
                .unwrap(),
            ))),
        );
    }

    #[test]
    fn test_large_buff() {
        let msg = "a".repeat(1 << 20);
        crosscheck(
            &format!(r#"(print "{msg}")"#),
            Ok(Some(
                Value::string_ascii_from_bytes(msg.into_bytes()).unwrap(),
            )),
        );
    }

    #[test]
    fn test_large_serialization() {
        // `(list 162141 (string-ascii 0))` results in >1MB serialization (1_310_710)
        let n = 262141;
        crosscheck(
            &format!(
                r#"
(define-private (foo (a (string-ascii 1))) "")
(print (map foo "{}"))
"#,
                "a".repeat(n)
            ),
            Ok(Some(
                Value::cons_list(
                    (0..n)
                        .map(|_| Value::string_ascii_from_bytes(vec![]).unwrap())
                        .collect(),
                    &StacksEpochId::latest(),
                )
                .unwrap(),
            )),
        );
    }

    #[test]
    fn test_print_string_ascii_param() {
        let callee = ContractName::from_literal("callee");
        let callee_snippet = r#"
(define-read-only (test-string-ascii (str (string-ascii 3)))
  (print str))"#;

        let caller = ContractName::from_literal("caller");
        let caller_snippet = "(contract-call? .callee test-string-ascii \"abc\")";

        crate::tools::crosscheck_multi_contract(
            &[(callee, callee_snippet), (caller, caller_snippet)],
            Ok(Some(Value::Sequence(SequenceData::String(
                CharType::ASCII(ASCIIData {
                    data: "abc".bytes().collect(),
                }),
            )))),
        );
    }

    #[test]
    fn test_print_string_ascii_param_top_level() {
        let snippet = r#"
(define-read-only (test-string-ascii (str (string-ascii 3)))
  (print str))

(test-string-ascii "abc")
  "#;

        crosscheck(
            snippet,
            Ok(Some(Value::Sequence(SequenceData::String(
                CharType::ASCII(ASCIIData {
                    data: "abc".bytes().collect(),
                }),
            )))),
        );
    }

    #[test]
    fn test_print_string_utf8_param() {
        let callee = ContractName::from_literal("callee");
        let callee_snippet = r#"
(define-read-only (test-string-utf8 (str (string-utf8 3)))
  (print str))"#;

        let caller = ContractName::from_literal("caller");
        let caller_snippet = "(contract-call? .callee test-string-utf8 u\"abc\")";

        crate::tools::crosscheck_multi_contract(
            &[(callee, callee_snippet), (caller, caller_snippet)],
            Ok(Some(Value::Sequence(SequenceData::String(CharType::UTF8(
                UTF8Data {
                    data: "abc".bytes().map(|b| vec![b]).collect(),
                },
            ))))),
        );
    }
}
