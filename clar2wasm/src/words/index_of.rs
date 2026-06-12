use clarity::types::StacksEpochId;
use clarity::vm::types::{SequenceSubtype, TypeSignature};
use clarity::vm::{ClarityName, SymbolicExpression};
use walrus::ir::{BinaryOp, IfElse, InstrSeqType, Loop, UnaryOp};
use walrus::ValType;

use super::{ComplexWord, Word};
use crate::check_args;
use crate::cost::WordCharge;
use crate::wasm_generator::{ArgumentsExt, GeneratorError, SequenceElementType, WasmGenerator};
use crate::wasm_utils::{get_type_size, ArgumentCountCheck};
use crate::words::equal::wasm_equal;

#[derive(Debug)]
pub enum IndexOf {
    Original,
    Alias,
}

impl Word for IndexOf {
    fn name(&self) -> ClarityName {
        match self {
            IndexOf::Original => ClarityName::from_literal("index-of"),
            IndexOf::Alias => ClarityName::from_literal("index-of?"),
        }
    }
}

impl ComplexWord for IndexOf {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        let serialization_size = generator.module.locals.add(ValType::I32);
        check_args!(generator, builder, 2, args.len(), ArgumentCountCheck::Exact);

        if generator.contract_analysis.epoch < StacksEpochId::Epoch2_05 {
            self.charge(generator, builder, args.len() as u32)?;
        }

        // Traverse the sequence, leaving its offset and size on the stack.
        let seq = args.get_expr(0)?;
        let elem_expr = args.get_expr(1)?;
        // workaround to fix types in the case of elements that are themself Sequences
        if let TypeSignature::SequenceType(SequenceSubtype::ListType(ltd)) = generator
            .get_expr_type(seq)
            .ok_or(GeneratorError::TypeError(
                "index_of element must be typed".to_owned(),
            ))?
        {
            generator.set_expr_type(elem_expr, ltd.get_list_item_type().clone())?;
        }

        generator.traverse_expr(builder, elem_expr)?;
        // STACK: [item]

        // Get the type of the item expression
        let item_ty = generator
            .get_expr_type(elem_expr)
            .ok_or_else(|| {
                GeneratorError::TypeError("index_of item expression must be typed".to_owned())
            })?
            .clone();

        if generator.contract_analysis.epoch >= StacksEpochId::Epoch2_05 {
            generator.serialization_size(builder, &item_ty)?;
            // STACK: [item, item_serialization_size]

            builder.local_set(serialization_size);
            // STACK: [item]
        }

        // Store the item into a local.
        let item_locals = generator.save_to_locals(builder, &item_ty, true);
        // STACK: []

        // Traverse the sequence, leaving its offset and size on the stack.
        generator.traverse_expr(builder, seq)?;
        // STACK: [offset, size]

        // Get type of the Sequence element.
        let elem_ty = generator.get_sequence_element_type(seq)?;

        if generator.contract_analysis.epoch >= StacksEpochId::Epoch2_05 {
            let seq_type = generator
                .get_expr_type(seq)
                .ok_or_else(|| {
                    GeneratorError::TypeError(
                        "index_of sequence expression must be typed".to_owned(),
                    )
                })?
                .clone();

            generator.serialization_size(builder, &seq_type)?;
            builder
                .local_get(serialization_size)
                .binop(BinaryOp::I32Add)
                .local_set(serialization_size);
            self.charge(generator, builder, serialization_size)?;
        }

        // Locals declaration.
        let seq_size = generator.module.locals.add(ValType::I32);
        let offset = generator.module.locals.add(ValType::I32);
        let end_offset = generator.module.locals.add(ValType::I32);

        builder
            .local_set(seq_size)
            // STACK: [offset]
            .local_tee(offset)
            // STACK: [offset]
            .local_get(seq_size)
            // STACK: [offset, size]
            .binop(BinaryOp::I32Add)
            // STACK: [add_result]
            .local_set(end_offset);
        // STACK: []

        // compute the sequence size.
        // we put seq_size on the stack to retrieve it later,
        // and again on the stack for the cost computation for epoch <= 2.05.
        builder.local_get(seq_size).local_get(seq_size);
        match &elem_ty {
            SequenceElementType::Byte => {
                // nothing to change here
            }
            SequenceElementType::UnicodeScalar => {
                // number of bytes / 4
                builder.i32_const(2).binop(BinaryOp::I32ShrU);
            }
            SequenceElementType::Other(ty) => {
                // number of bytes / element size
                builder
                    .i32_const(get_type_size(ty))
                    .binop(BinaryOp::I32DivU);
            }
        }
        builder.local_set(seq_size);

        builder.local_tee(seq_size).unop(UnaryOp::I32Eqz);
        // STACK: [size]

        let ty = InstrSeqType::new(
            &mut generator.module.types,
            &[],
            &[ValType::I32, ValType::I64, ValType::I64],
        );

        let if_id = {
            let mut if_case = builder.dangling_instr_seq(ty);
            if_case.i32_const(0).i64_const(0).i64_const(0);
            if_case.id()
        };

        let else_id = {
            let else_case = &mut builder.dangling_instr_seq(ty);

            // STACK: []

            // Create and store an index into a local.
            let index = generator.module.locals.add(ValType::I64);
            else_case.i64_const(0);
            // STACK: [0]
            else_case.local_set(index);
            // STACK: []

            // Loop through the sequence.
            let loop_body_ty = InstrSeqType::new(
                &mut generator.module.types,
                &[],
                &[ValType::I32, ValType::I64, ValType::I64],
            );

            let loop_body = &mut else_case.dangling_instr_seq(loop_body_ty);
            let loop_body_id = {
                // Loop label.
                let loop_id = loop_body.id();

                // Load an element from the sequence, at offset position,
                // and push it onto the top of the stack.
                // Also store the current sequence element into a local.
                let (elem_size, elem_locals) = match &elem_ty {
                    SequenceElementType::Other(elem_ty) => {
                        (
                            generator.read_from_memory(loop_body, offset, 0, elem_ty)?,
                            // STACK: [element]
                            generator.save_to_locals(loop_body, elem_ty, true),
                            // STACK: []
                        )
                    }
                    SequenceElementType::Byte => {
                        // The element type is a byte, so we can just push the
                        // offset and size = 1 to the stack.
                        let size = 1;
                        loop_body.local_get(offset).i32_const(size);
                        // STACK: [offset, size]

                        (size, generator.save_to_locals(loop_body, &item_ty, true))
                        // STACK: []
                    }
                    SequenceElementType::UnicodeScalar => {
                        // The element type is a unicode scalar, so we can just push the
                        // offset and size = 4 to the stack.
                        let size = 4;
                        loop_body.local_get(offset).i32_const(size);
                        // STACK: [offset, size]

                        (size, generator.save_to_locals(loop_body, &item_ty, true))
                        // STACK: []
                    }
                };

                // Check item and element equality.
                // And push the result of the comparison onto the top of the stack.
                wasm_equal(&item_ty, generator, loop_body, &item_locals, &elem_locals)?;
                // STACK: [wasm_equal_result]

                loop_body.if_else(
                    InstrSeqType::new(
                        &mut generator.module.types,
                        &[],
                        &[ValType::I32, ValType::I64, ValType::I64],
                    ),
                    |then| {
                        then.i32_const(1).local_get(index).i64_const(0);
                        // STACK: [1, index_lo, index_hi]
                    },
                    |else_| {
                        // Increment the sequence offset by the size of the element
                        // and push it to the stack.
                        // Also push the offset limit onto the top of the stack.
                        else_
                            .local_get(offset)
                            .i32_const(elem_size)
                            .binop(BinaryOp::I32Add)
                            .local_tee(offset)
                            .local_get(end_offset);
                        // STACK: [offset, end_offset]

                        else_.binop(BinaryOp::I32GeU).if_else(
                            InstrSeqType::new(
                                &mut generator.module.types,
                                &[],
                                &[ValType::I32, ValType::I64, ValType::I64],
                            ),
                            |then| {
                                // Reached the end of the sequence
                                // and not found the element.
                                then.i32_const(0).local_get(index).i64_const(0);
                                // STACK: [0, index_lo, index_hi]
                            },
                            |else_| {
                                // Increment index by 1
                                // and continue loop.
                                else_
                                    .local_get(index)
                                    .i64_const(1)
                                    .binop(BinaryOp::I64Add)
                                    .local_set(index)
                                    .br(loop_id);
                            },
                        );
                    },
                );
                loop_body.id()
            };

            else_case.instr(Loop { seq: loop_body_id });

            else_case.id()
        };

        builder.instr(IfElse {
            consequent: if_id,
            alternative: else_id,
        });

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use clarity::vm::types::{ListData, ListTypeData, SequenceData};
    use clarity::vm::Value;

    use crate::tools::{crosscheck, evaluate, TestEnvironment};

    #[test]
    fn index_of_list_less_than_two_args() {
        let result = evaluate("(index-of (list 1 2 3))");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 1"));
    }

    #[test]
    fn index_of_list_more_than_two_args() {
        let result = evaluate("(index-of (list 1 2 3) 1 2)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 3"));
    }

    #[test]
    fn index_of_list_not_present() {
        crosscheck("(index-of (list 1 2 3 4 5 6 7) 9)", Ok(Some(Value::none())));
    }

    #[test]
    fn index_of_list_first() {
        crosscheck(
            "(index-of (list 1 2 3 4) 1)",
            Ok(Some(Value::some(Value::UInt(0)).unwrap())),
        );
    }

    #[test]
    fn index_of_list() {
        crosscheck(
            "(index-of (list 1 2 3 4 5 6 7) 3)",
            Ok(Some(Value::some(Value::UInt(2)).unwrap())),
        );
    }

    #[test]
    fn index_of_list_last() {
        crosscheck(
            "(index-of (list 1 2 3 4 5 6 7) 7)",
            Ok(Some(Value::some(Value::UInt(6)).unwrap())),
        );
    }

    #[test]
    fn index_of_list_called_by_v1_alias() {
        crosscheck(
            "(index-of (list 1 2 3 4 5 6 7) 100)",
            Ok(Some(Value::none())),
        );
    }

    #[test]
    fn index_of_list_of_lists() {
        crosscheck("(index-of (list (list 1 2) (list 2 3 4) (list 1 2 3 4 5) (list 1 2 3 4)) (list 1 2 3 4))",
            Ok(Some(Value::some(Value::UInt(3)).unwrap()))
        );
    }

    #[test]
    fn index_of_list_zero_len() {
        let mut env = TestEnvironment::default();
        let val = env.init_contract_with_snippet(
            "index_of",
            r#"
(define-private (find-it? (needle int) (haystack (list 10 int)))
  (index-of haystack needle))
(find-it? 6 (list))
"#,
        );

        assert_eq!(val.unwrap(), Some(Value::none()));
    }

    #[test]
    fn index_of_list_check_stack() {
        let mut env = TestEnvironment::default();
        let val = env.evaluate(
            r#"
(define-private (find-it? (needle int) (haystack (list 10 int)))
  (is-eq (index-of haystack needle) none))
(asserts! (find-it? 6 (list 1 2 3)) (err u1))
(list 4 5 6)
"#,
        );

        assert_eq!(
            val.unwrap(),
            Some(Value::Sequence(SequenceData::List(ListData {
                data: vec![Value::Int(4), Value::Int(5), Value::Int(6)],
                type_signature: ListTypeData::new_list(
                    clarity::vm::types::TypeSignature::IntType,
                    3
                )
                .unwrap()
            })))
        );
    }

    #[test]
    fn index_of_ascii() {
        crosscheck(
            "(index-of \"Stacks\" \"a\")",
            Ok(Some(Value::some(Value::UInt(2)).unwrap())),
        );
    }

    #[test]
    fn index_of_ascii_empty() {
        crosscheck("(index-of \"\" \"\")", Ok(Some(Value::none())));
    }

    #[test]
    fn index_of_ascii_empty_input() {
        crosscheck("(index-of \"\" \"a\")", Ok(Some(Value::none())));
    }

    #[test]
    fn index_of_ascii_empty_char() {
        crosscheck("(index-of \"Stacks\" \"\")", Ok(Some(Value::none())));
    }

    #[test]
    fn index_of_ascii_first_elem() {
        crosscheck(
            "(index-of \"Stacks\" \"S\")",
            Ok(Some(Value::some(Value::UInt(0)).unwrap())),
        );
    }

    #[test]
    fn index_of_ascii_last_elem() {
        crosscheck(
            "(index-of \"Stacks\" \"s\")",
            Ok(Some(Value::some(Value::UInt(5)).unwrap())),
        );
    }

    #[test]
    fn index_of_utf8() {
        crosscheck(
            "(index-of u\"Stacks\" u\"a\")",
            Ok(Some(Value::some(Value::UInt(2)).unwrap())),
        );
    }

    #[test]
    fn index_of_utf8_b() {
        crosscheck(
            "(index-of u\"St\\u{1F98A}cks\" u\"\\u{1F98A}\")",
            Ok(Some(Value::some(Value::UInt(2)).unwrap())),
        );
    }

    #[test]
    fn index_of_utf8_first_elem() {
        crosscheck(
            "(index-of u\"Stacks\\u{1F98A}\" u\"S\")",
            Ok(Some(Value::some(Value::UInt(0)).unwrap())),
        );
    }

    #[test]
    fn index_of_utf8_last_elem() {
        crosscheck(
            "(index-of u\"Stacks\\u{1F98A}\" u\"\\u{1F98A}\")",
            Ok(Some(Value::some(Value::UInt(6)).unwrap())),
        );
    }

    #[test]
    fn index_of_utf8_zero_len() {
        crosscheck("(index-of u\"Stacks\" u\"\")", Ok(Some(Value::none())));
    }

    #[test]
    fn index_of_buff_last_byte() {
        crosscheck(
            "(index-of 0xfb01 0x01)",
            Ok(Some(Value::some(Value::UInt(1)).unwrap())),
        );
    }

    #[test]
    fn index_of_buff_first_byte() {
        crosscheck(
            "(index-of 0xfb01 0xfb)",
            Ok(Some(Value::some(Value::UInt(0)).unwrap())),
        );
    }

    #[test]
    fn index_of_buff() {
        crosscheck(
            "(index-of 0xeeaadd 0xaa)",
            Ok(Some(Value::some(Value::UInt(1)).unwrap())),
        );
    }

    #[test]
    fn index_of_buff_not_present() {
        crosscheck("(index-of 0xeeaadd 0xcc)", Ok(Some(Value::none())));
    }

    #[test]
    fn index_of_first_optional_complex_type() {
        crosscheck(
            "(index-of (list (some 42) none none none (some 15)) (some 42))",
            Ok(Some(Value::some(Value::UInt(0)).unwrap())),
        );
    }

    #[test]
    fn index_of_last_optional_complex_type() {
        crosscheck(
            "(index-of (list (some 42) (some 3) (some 6) (some 15) none) none)",
            Ok(Some(Value::some(Value::UInt(4)).unwrap())),
        );
    }

    #[test]
    fn index_of_optional_complex_type() {
        crosscheck(
            "(index-of (list (some 1) none) none)",
            Ok(Some(Value::some(Value::UInt(1)).unwrap())),
        );
    }

    #[test]
    fn index_of_tuple_complex_type() {
        crosscheck("(index-of (list (tuple (id 42) (name \"Clarity\")) (tuple (id 133) (name \"Wasm\"))) (tuple (id 42) (name \"Wasm\")))",
            Ok(Some(Value::none()))
        );
    }

    #[test]
    fn index_of_complex_type() {
        crosscheck(
            "(index-of (list (list (ok 2) (err 5)) (list (ok 42)) (list (err 7))) (list (err 7)))",
            Ok(Some(Value::some(Value::UInt(2)).unwrap())),
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
        fn index_of_alias_list_zero_len() {
            let mut env = TestEnvironment::default();
            let val = env.init_contract_with_snippet(
                "index_of",
                r#"
    (define-private (find-it? (needle int) (haystack (list 10 int)))
      (index-of? haystack needle))
    (find-it? 6 (list))
    "#,
            );

            assert_eq!(val.unwrap(), Some(Value::none()));
        }

        #[test]
        fn index_of_alias_first_optional_complex_type() {
            crosscheck(
                "(index-of? (list (some 42) none none none (some 15)) (some 42))",
                Ok(Some(Value::some(Value::UInt(0)).unwrap())),
            );
        }
    }
}
