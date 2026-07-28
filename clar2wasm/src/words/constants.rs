use clarity::types::StacksEpochId;
use clarity::vm::types::PrincipalData;
use clarity::vm::{ClarityName, SymbolicExpression, SymbolicExpressionType, Value};
use walrus::{ActiveData, DataKind, ValType};

use super::{ComplexWord, Word};
use crate::check_args;
use crate::wasm_generator::{ArgumentsExt, GeneratorError, WasmGenerator};
use crate::wasm_utils::{get_type_size, is_in_memory_type, ArgumentCountCheck};

#[derive(Debug)]
pub struct DefineConstant;

impl Word for DefineConstant {
    fn name(&self) -> ClarityName {
        ClarityName::from_literal("define-constant")
    }
}

impl ComplexWord for DefineConstant {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 2, args.len(), ArgumentCountCheck::Exact);

        // Constant name
        let name = args.get_name(0)?;

        // Making sure if name is not reserved
        if generator.is_reserved_name(name) {
            return Err(GeneratorError::InternalError(format!(
                "Name already used {name:?}"
            )));
        }

        // Constant value
        let value = args.get_expr(1)?;
        let value_ty = generator
            .get_expr_type(value)
            .ok_or_else(|| GeneratorError::TypeError("constant value must be typed".to_owned()))?
            .clone();

        let (offset, length) = if let SymbolicExpressionType::LiteralValue(value) = &value.expr {
            // If the constant value is a literal value (i.e: 42, u13, ...)
            // it can be, directly, added to the literal memory.
            let (mut value_offset, value_length) = generator.add_literal(value)?;

            // Literals of in-memory types should write (offset, len) to memory,
            // so that their representation is consistent with in-memory non-literals.
            if is_in_memory_type(&value_ty) {
                let ref_offset = generator.literal_memory_end;
                generator.literal_memory_end += 8; // offset + len bytes

                let memory = generator.get_memory()?;
                generator.module.data.add(
                    DataKind::Active(ActiveData {
                        memory,
                        location: walrus::ActiveDataLocation::Absolute(ref_offset),
                    }),
                    value_offset
                        .to_le_bytes()
                        .into_iter()
                        .chain(value_length.to_le_bytes())
                        .collect(),
                );

                // update offset to point to reference
                value_offset = ref_offset;
            }

            (value_offset, value_length)
        } else {
            // The constant expression is evaluated,
            // and the result is stored in a reserved memory location.

            // Evaluate the expression and push the result onto the stack.
            generator.traverse_expr(builder, value)?;

            // Prepare space in memory for the expression's result.
            let offset = generator.literal_memory_end;
            let offset_local = generator.module.locals.add(ValType::I32);
            builder.i32_const(offset as i32).local_set(offset_local);
            let value_ty_len = get_type_size(&value_ty) as u32;
            generator.literal_memory_end += value_ty_len;

            // Write the evaluated expression value, present on top of the stack, to the memory.
            let value_length = generator.write_to_memory(builder, offset_local, 0, &value_ty)?;

            (offset, value_length)
        };

        // Add constant name to the memory.
        let (name_offset, name_length) = generator.add_string_literal(name)?;

        // Push constant name attributes to the data stack.
        builder
            .i32_const(name_offset as i32)
            .i32_const(name_length as i32);

        // Push constant value attributes to the data stack.
        builder.i32_const(offset as i32).i32_const(length as i32);

        // Call a host interface function to add the constant name
        // and evaluated value to a persistent data structure.
        builder.call(generator.func_by_name("stdlib.save_constant"));

        generator.constants.insert(name.to_string(), value_ty);
        if generator.contract_analysis.epoch >= StacksEpochId::Epoch34 {
            // If the constant is bound to a contract principal, remember its
            // contract identifier so that `contract-call?` targeting this constant
            // can be lowered as a static dispatch. This covers both a direct
            // principal literal (`(define-constant a .contract)`) and a constant
            // aliasing another such constant (`(define-constant b a)`), which is
            // already recorded because constants are processed in source order.
            match &value.expr {
                SymbolicExpressionType::LiteralValue(Value::Principal(
                    PrincipalData::Contract(contract_identifier),
                )) => {
                    generator
                        .constant_contract_principals
                        .insert(name.to_string(), contract_identifier.clone());
                }
                SymbolicExpressionType::Atom(other) => {
                    if let Some(contract_identifier) = generator
                        .constant_contract_principals
                        .get(other.as_str())
                        .cloned()
                    {
                        generator
                            .constant_contract_principals
                            .insert(name.to_string(), contract_identifier);
                    }
                }
                _ => {}
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use clarity::types::StacksEpochId;
    use clarity::vm::types::{
        ASCIIData, CharType, ListData, ListTypeData, PrincipalData, SequenceData, TupleData,
    };
    use clarity::vm::Value;
    use clarity_types::ClarityName;

    use crate::tools::{crosscheck, crosscheck_expect_failure, evaluate, TestEnvironment};

    //
    // Module with tests that should only be executed
    // when running Clarity::V1.
    //
    #[cfg(feature = "test-clarity-v1")]
    mod clarity_v1 {
        use super::*;
        use crate::tools::crosscheck_with_epoch;

        #[test]
        fn validate_define_const_epoch() {
            // Epoch20
            crosscheck_with_epoch(
                "(define-constant index-of? (+ 2 2))",
                Ok(None),
                StacksEpochId::Epoch20,
            );
        }
    }

    #[test]
    fn define_constant_less_than_two_args() {
        let result = evaluate("(define-constant one)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 1"));
    }

    #[test]
    fn define_constant_more_than_two_args() {
        let result = evaluate("(define-constant two 2 3)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 3"));
    }

    #[test]
    fn define_constant_const() {
        crosscheck(
            r#"(define-constant four 4) (define-private (go) (print four)) (go)"#,
            Ok(Some(Value::Int(4))),
        )
    }

    #[test]
    fn define_constant_function() {
        crosscheck(
            r#"(define-constant four (+ 2 2)) (define-private (go) (print four)) (go)"#,
            Ok(Some(Value::Int(4))),
        )
    }

    #[test]
    fn define_constant_list() {
        crosscheck(
            r#"(define-constant list-of-2-int (list 1 1)) (define-private (go) (print list-of-2-int)) (go)"#,
            Ok(Some(Value::Sequence(SequenceData::List(ListData {
                data: vec![Value::Int(1), Value::Int(1)],
                type_signature: ListTypeData::new_list(
                    clarity::vm::types::TypeSignature::IntType,
                    2,
                )
                .unwrap(),
            })))),
        )
    }

    #[test]
    fn test_int_constant() {
        crosscheck(
            "
(define-constant small-int 1)
(define-public (get-int-constant)
  (ok small-int))
(get-int-constant)",
            evaluate("(ok 1)"),
        );
    }

    #[test]
    fn test_large_uint_constant() {
        crosscheck(
            "
(define-constant large-uint u338770000845734292516042252062085074415)
(define-public (get-large-uint-constant)
  (ok large-uint))
(get-large-uint-constant)",
            evaluate("(ok u338770000845734292516042252062085074415)"),
        );
    }

    #[test]
    fn test_string_constant() {
        crosscheck(
            r#"
(define-constant string "hello world")
(define-public (get-string-constant)
  (ok string))
(get-string-constant)"#,
            evaluate(r#"(ok "hello world")"#),
        );
    }

    #[test]
    fn test_string_utf8_constant() {
        crosscheck(
            r#"
(define-constant string-utf8 u"hello world\u{1F98A}")
(define-public (get-string-utf8-constant)
  (ok string-utf8))
(get-string-utf8-constant)
"#,
            evaluate(r#"(ok u"hello world\u{1F98A}")"#),
        );
    }

    #[test]
    fn test_bytes_constant() {
        crosscheck(
            "
(define-constant bytes 0x12345678)
(define-public (get-bytes-constant)
  (ok bytes))
(get-bytes-constant)
",
            evaluate("(ok 0x12345678)"),
        );
    }

    #[test]
    fn validate_define_const() {
        // Reserved keyword
        crosscheck_expect_failure("(define-constant map (+ 2 2))");

        // Custom constant name
        crosscheck("(define-constant a (+ 2 2))", Ok(None));

        // Custom constant name duplicate
        crosscheck_expect_failure("(define-constant a (+ 2 2)) (define-constant a (+ 2 2))");
    }

    #[test]
    fn test_non_literal_string() {
        crosscheck(
            r#"(define-constant cst (concat "Hello," " World!")) cst"#,
            Ok(Some(Value::Sequence(SequenceData::String(
                CharType::ASCII(ASCIIData {
                    data: "Hello, World!".bytes().collect(),
                }),
            )))),
        )
    }

    #[test]
    fn test_large_buff() {
        let buff = "aa".repeat(1 << 20);
        crosscheck(
            &format!("(define-constant cst 0x{buff}) cst"),
            Ok(Some(Value::buff_from(hex::decode(buff).unwrap()).unwrap())),
        )
    }

    #[test]
    fn test_large_complex() {
        let a = "aa".repeat(1 << 18);
        let b = "bb".repeat(1 << 18);
        crosscheck(
            &format!("(define-constant cst (list 0x{a} 0x{b})) cst"),
            Ok(Some(
                Value::cons_list(
                    vec![
                        Value::buff_from(hex::decode(a).unwrap()).unwrap(),
                        Value::buff_from(hex::decode(b).unwrap()).unwrap(),
                    ],
                    &StacksEpochId::latest(),
                )
                .unwrap(),
            )),
        )
    }

    #[test]
    fn test_large_complex_via_contract_call() {
        let a = "aa".repeat(1 << 18);
        let b = "bb".repeat(1 << 18);

        let mut env = TestEnvironment::default();
        env.init_contract_with_snippet(
            "contract-callee",
            &format!(
                r#"
                (define-constant cst (list 0x{a} 0x{b}))
                (define-public (return-cst)
                    (ok cst)
                )
            "#
            ),
        )
        .expect("Failed to init contract.");
        let val = env
            .init_contract_with_snippet(
                "contract-caller",
                r#"(contract-call? .contract-callee return-cst)"#,
            )
            .expect("Failed to init contract.");

        assert_eq!(
            val.unwrap(),
            Value::okay(
                Value::cons_list(
                    vec![
                        Value::buff_from(hex::decode(a).unwrap()).unwrap(),
                        Value::buff_from(hex::decode(b).unwrap()).unwrap(),
                    ],
                    &StacksEpochId::latest(),
                )
                .unwrap()
            )
            .unwrap()
        );
    }

    #[test]
    fn test_concretize() {
        crosscheck(
            "(define-constant cst (list 'S1169T4T08XBQR7N8F69R4FE00ESXD8QTD8XEKZ67.A 'SH3Y7SXGEJD365K42XCJ21KSTSCB1Z4RA5XTJA2ZH.a)) cst",
            Ok(Some(
                Value::cons_list(
                    vec![Value::Principal(
                            PrincipalData::parse_qualified_contract_principal(
                                "S1169T4T08XBQR7N8F69R4FE00ESXD8QTD8XEKZ67.A",
                            )
                        .unwrap()),
                        Value::Principal(
                            PrincipalData::parse_qualified_contract_principal(
                                "SH3Y7SXGEJD365K42XCJ21KSTSCB1Z4RA5XTJA2ZH.a",
                            )
                        .unwrap())
                    ],
                    &StacksEpochId::latest(),
                )
                .unwrap()
            )),
        );
    }

    #[test]
    fn constants_need_ducktyping() {
        let snippet = "
            (define-constant cst (err u1))
            
            (define-private (foo)
                (if false (ok true) cst)
            )

            (define-private (bar)
                (if false (ok 42) cst)
            )

            {foo: (foo), bar: (bar)} 
        ";

        crosscheck(
            snippet,
            Ok(Some(
                TupleData::from_data(vec![
                    (ClarityName::from_literal("foo"), Value::err_uint(1)),
                    (ClarityName::from_literal("bar"), Value::err_uint(1)),
                ])
                .unwrap()
                .into(),
            )),
        );
    }
}
