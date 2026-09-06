use std::collections::BTreeMap;

use clarity::types::StacksEpochId;
use clarity::vm::types::TupleTypeSignature;
use clarity::vm::types::TypeSignature;
use clarity::vm::{ClarityName, SymbolicExpression};
use walrus::ir::BinaryOp;
use walrus::ValType;

use super::{ComplexWord, Word};
use crate::check_args;
use crate::cost::WordCharge;
use crate::wasm_generator::{clar2wasm_ty, drop_value, GeneratorError, WasmGenerator};
use crate::wasm_utils::{check_argument_count, ArgumentCountCheck};

#[derive(Debug)]
pub struct TupleCons;

impl Word for TupleCons {
    fn name(&self) -> ClarityName {
        ClarityName::from_literal("tuple")
    }
}

impl ComplexWord for TupleCons {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        let args_len = args.len();

        check_argument_count(generator, builder, 1, args_len, ArgumentCountCheck::AtLeast)?;

        self.charge(generator, builder, args_len as u32)?;

        let ty = generator
            .get_expr_type(expr)
            .ok_or_else(|| GeneratorError::TypeError("tuple expression must be typed".to_string()))?
            .clone();

        let mut tuple_ty = match ty {
            TypeSignature::TupleType(ref tuple) => tuple.get_type_map().clone(),
            _ => return Err(GeneratorError::TypeError("expected tuple type".to_string())),
        };

        // The args for `tuple` should be pairs of values, with the first value
        // being the key and the second being the value.
        let mut values = Vec::with_capacity(args.len());
        for arg in args {
            let list = arg.match_list().ok_or_else(|| {
                GeneratorError::InternalError("expected key-value pairs in tuple".to_string())
            })?;
            if list.len() != 2 {
                return Err(GeneratorError::InternalError(
                    "expected key-value pairs in tuple".to_string(),
                ));
            }

            let key = list[0].match_atom().ok_or_else(|| {
                GeneratorError::InternalError("expected key-value pairs in tuple".to_string())
            })?;
            values.push((key, &list[1]));
        }

        // Since we have to evaluate the fields in the order of definition but the result will be
        // in the lexicographic order of the keys, we'll add locals to store all evaluated fields.
        let mut locals_map = BTreeMap::new();

        // Now we can iterate over the fields and evaluate them.
        for (key, value) in values {
            let value_ty = tuple_ty.remove(key).ok_or_else(|| {
                GeneratorError::TypeError("Tuples fields should be typed".to_owned())
            })?;

            // WORKAROUND: if you have a tuple like `(tuple (foo none))`, the `none` will have the type
            // NoType, even if it has a defined type in the tuple. This creates issues because the placeholder
            // does not have the same amount of values in the Wasm code than the correct type.
            // While we wait for a real fix in the typechecker, here is a workaround to make sure that the type
            // is correct.
            generator.set_expr_type(value, value_ty.clone())?;

            generator.traverse_expr(builder, value)?;
            locals_map.insert(key, generator.save_to_locals(builder, &value_ty, true));
        }

        // Make sure that all the tuples keys were defined
        if !tuple_ty.is_empty() {
            return Err(GeneratorError::TypeError(
                "Tuple should define each of its fields".to_owned(),
            ));
        }

        // Finally load the locals onto the stack
        for local in locals_map.into_values().flatten() {
            builder.local_get(local);
        }

        Ok(())
    }
}

#[derive(Debug)]
pub struct TupleGet;

impl Word for TupleGet {
    fn name(&self) -> ClarityName {
        ClarityName::from_literal("get")
    }
}

impl ComplexWord for TupleGet {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 2, args.len(), ArgumentCountCheck::Exact);

        let target_field_name = args[0]
            .match_atom()
            .ok_or_else(|| GeneratorError::InternalError("expected key name".into()))?;

        let tuple_ty = generator
            .get_expr_type(&args[1])
            .ok_or_else(|| GeneratorError::TypeError("tuple expression must be typed".to_string()))
            .and_then(|lhs_ty| match lhs_ty {
                TypeSignature::TupleType(tuple) => Ok(tuple),
                TypeSignature::OptionalType(boxed) => match **boxed {
                    TypeSignature::TupleType(ref tuple) => Ok(tuple),
                    _ => Err(GeneratorError::TypeError("expected tuple type".to_string())),
                },
                _ => Err(GeneratorError::TypeError("expected tuple type".to_string())),
            })?
            .clone();

        // Traverse the tuple argument, leaving it on top of the stack.
        generator.traverse_expr(builder, &args[1])?;

        // Determine the wasm types for each field of the tuple
        let field_types = tuple_ty.get_type_map();

        self.charge(generator, builder, field_types.iter().len() as u32)?;

        // Create locals for the target field
        let wasm_types = clar2wasm_ty(field_types.get(target_field_name).ok_or_else(|| {
            GeneratorError::InternalError(format!("missing field '{target_field_name}' in tuple"))
        })?);
        let mut val_locals = Vec::with_capacity(wasm_types.len());
        for local_ty in wasm_types.iter().rev() {
            let local = generator.module.locals.add(*local_ty);
            val_locals.push(local);
        }

        // Loop through the fields of the tuple, in reverse order. When we find
        // the target field, we'll store it in the locals we created above. All
        // other fields will be dropped.
        for (field_name, field_ty) in field_types.iter().rev() {
            // If this is the target field, store it in the locals we created
            // above.
            if field_name == target_field_name {
                for local in val_locals.iter() {
                    builder.local_set(*local);
                }
            } else {
                drop_value(builder, field_ty);
            }
        }

        // Load the target field from the locals we created above.
        for local in val_locals.iter().rev() {
            builder.local_get(*local);
        }

        Ok(())
    }
}

#[derive(Debug)]
pub struct TupleMerge;

impl Word for TupleMerge {
    fn name(&self) -> ClarityName {
        ClarityName::from_literal("merge")
    }
}

impl ComplexWord for TupleMerge {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 2, args.len(), ArgumentCountCheck::Exact);
        let serialization_size = generator.borrow_local(ValType::I32);

        if generator.contract_analysis.epoch < StacksEpochId::Epoch2_05 {
            self.charge(generator, builder, args.len() as u32)?;
        }
        let lhs_tuple_ty = generator
            .get_expr_type(&args[0])
            .ok_or_else(|| GeneratorError::TypeError("tuple expression must be typed".to_string()))
            .and_then(|lhs_ty| match lhs_ty {
                TypeSignature::TupleType(tuple) => Ok(tuple),
                _ => Err(GeneratorError::TypeError("expected tuple type".to_string())),
            })?
            .clone();

        let rhs_tuple_ty = generator
            .get_expr_type(&args[1])
            .ok_or_else(|| GeneratorError::TypeError("tuple expression must be typed".to_string()))
            .and_then(|lhs_ty| match lhs_ty {
                TypeSignature::TupleType(tuple) => Ok(tuple),
                _ => Err(GeneratorError::TypeError("expected tuple type".to_string())),
            })?
            .clone();

        let result_ty = generator
            .get_expr_type(expr)
            .ok_or_else(|| GeneratorError::TypeError("merge expression must be typed".to_owned()));

        let result_type_map = result_ty
            .and_then(|expr_ty| match expr_ty {
                TypeSignature::TupleType(tuple) => Ok(tuple),
                _ => Err(GeneratorError::TypeError("expected tuple type".to_string())),
            })
            .map(|tuple| tuple.get_type_map().clone())?;

        // Merge result types into the LHS and RHS tuple types.
        let rhs_tuple_ty = TupleTypeSignature::try_from(
            rhs_tuple_ty
                .get_type_map()
                .iter()
                .map(|(name, ty_)| {
                    (
                        name.clone(),
                        result_type_map
                            .get(name)
                            .cloned()
                            .unwrap_or_else(|| ty_.clone()),
                    )
                })
                .collect::<Vec<_>>(),
        )
        .map_err(|e| GeneratorError::TypeError(format!("merge: invalid RHS tuple type: {e}")))?;
        generator.set_expr_type(&args[1], TypeSignature::TupleType(rhs_tuple_ty.clone()))?;

        let lhs_tuple_ty = TupleTypeSignature::try_from(
            lhs_tuple_ty
                .get_type_map()
                .iter()
                .map(|(name, ty_)| {
                    // Fields overridden by the RHS are dropped, so their own type is kept.
                    let ty_ = if rhs_tuple_ty.get_type_map().contains_key(name) {
                        ty_.clone()
                    } else {
                        result_type_map
                            .get(name)
                            .cloned()
                            .unwrap_or_else(|| ty_.clone())
                    };
                    (name.clone(), ty_)
                })
                .collect::<Vec<_>>(),
        )
        .map_err(|e| GeneratorError::TypeError(format!("merge: invalid LHS tuple type: {e}")))?;
        generator.set_expr_type(&args[0], TypeSignature::TupleType(lhs_tuple_ty.clone()))?;

        // Those locals will contain the resulting tuple after the merge operation
        let result_locals: BTreeMap<_, Vec<_>> = result_type_map
            .into_iter()
            .map(|(name, ty_)| {
                (
                    name,
                    clar2wasm_ty(&ty_)
                        .into_iter()
                        .map(|local_ty| generator.module.locals.add(local_ty))
                        .collect(),
                )
            })
            .collect();

        // Traverse the LHS tuple argument, leaving it on top of the stack.
        generator.traverse_expr(builder, &args[0])?;

        if generator.contract_analysis.epoch >= StacksEpochId::Epoch2_05 {
            generator.serialization_size(builder, &lhs_tuple_ty.clone().into())?;
            // STACK: [LHS, item_serialization_size]

            builder.local_set(*serialization_size);
            // STACK: [LHS]
        }

        // We will copy the values from LHS into the result locals iff the key is not
        // present in RHS. Otherwise, we drop the values.
        for (name, ty_) in lhs_tuple_ty.get_type_map().iter().rev() {
            if !rhs_tuple_ty.get_type_map().contains_key(name) {
                result_locals
                    .get(name)
                    .ok_or_else(|| {
                        GeneratorError::InternalError(
                            "merge result tuple should contain all the keys of LHS".to_owned(),
                        )
                    })?
                    .iter()
                    .rev()
                    .for_each(|local| {
                        builder.local_set(*local);
                    });
            } else {
                drop_value(builder, ty_);
            }
        }

        // Traverse the RHS tuple argument, leaving it on top of the stack.
        generator.traverse_expr(builder, &args[1])?;

        if generator.contract_analysis.epoch >= StacksEpochId::Epoch2_05 {
            generator.serialization_size(builder, &rhs_tuple_ty.clone().into())?;
            // STACK: [RHS, item_serialization_size]

            builder
                .local_get(*serialization_size)
                .binop(BinaryOp::I32Add)
                .local_set(*serialization_size);

            // STACK: [RHS]
            self.charge(generator, builder, *serialization_size)?;
            // STACK: [RHS]
        }

        // We will copy all values of RHS into the result locals
        for (name, _) in rhs_tuple_ty.get_type_map().iter().rev() {
            result_locals
                .get(name)
                .ok_or_else(|| {
                    GeneratorError::InternalError(
                        "merge result tuple should contain all the keys of RHS".to_owned(),
                    )
                })?
                .iter()
                .rev()
                .for_each(|local| {
                    builder.local_set(*local);
                });
        }

        // Now we load the result locals onto the stack
        result_locals.into_values().flatten().for_each(|local| {
            builder.local_get(local);
        });

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use clarity::vm::types::TupleData;
    use clarity::vm::{ClarityName, Value};

    use crate::tools::{crosscheck, evaluate};

    #[test]
    fn test_get_optional() {
        let preamble = "
(define-read-only (get-optional-tuple (o (optional { a: int })))
  (get a o))";

        crosscheck(
            &format!("{preamble} (get-optional-tuple none)"),
            Ok(Some(Value::none())),
        );

        crosscheck(
            &format!("{preamble} (get-optional-tuple (some {{ a: 3 }} ))"),
            Ok(Some(Value::some(Value::Int(3)).unwrap())),
        );
    }

    #[test]
    fn merge_same_key_different_type() {
        let snippet = r#"(merge {a: 42} {a: "Hello, World!"})"#;

        let expected = Value::from(
            clarity::vm::types::TupleData::from_data(vec![(
                clarity::vm::ClarityName::from_literal("a"),
                Value::Sequence(clarity::vm::types::SequenceData::String(
                    clarity::vm::types::CharType::ASCII(clarity::vm::types::ASCIIData {
                        data: "Hello, World!".bytes().collect(),
                    }),
                )),
            )])
            .unwrap(),
        );

        crosscheck(snippet, Ok(Some(expected)));
    }

    #[test]
    fn merge_multiple_same_key_different_type() {
        let snippet =
            r#"(merge {a: 42, b: 0x24, c: 0xdeadbeef} {a: "Hello, World!", b: u789, d: 123})"#;

        let expected = Value::from(
            clarity::vm::types::TupleData::from_data(vec![
                (
                    clarity::vm::ClarityName::from_literal("a"),
                    Value::Sequence(clarity::vm::types::SequenceData::String(
                        clarity::vm::types::CharType::ASCII(clarity::vm::types::ASCIIData {
                            data: "Hello, World!".bytes().collect(),
                        }),
                    )),
                ),
                (
                    clarity::vm::ClarityName::from_literal("b"),
                    Value::UInt(789),
                ),
                (
                    clarity::vm::ClarityName::from_literal("c"),
                    Value::Sequence(clarity::vm::types::SequenceData::Buffer(
                        clarity::vm::types::BuffData {
                            data: vec![0xde, 0xad, 0xbe, 0xef],
                        },
                    )),
                ),
                (clarity::vm::ClarityName::from_literal("d"), Value::Int(123)),
            ])
            .unwrap(),
        );

        crosscheck(snippet, Ok(Some(expected)));
    }

    #[test]
    fn tuple_check_evaluation_order() {
        let snippet = r#"
        (define-data-var foo int 1)
        {
            b: (var-set foo 2),
            a: (var-get foo)
        }
    "#;

        let expected = Value::from(
            TupleData::from_data(vec![
                (ClarityName::from_literal("b"), Value::Bool(true)),
                (ClarityName::from_literal("a"), Value::Int(2)),
            ])
            .unwrap(),
        );

        crosscheck(snippet, Ok(Some(expected)));
    }

    /// Builds `{ a: <a>, b: <b> }` as a Clarity value.
    fn tuple_ab(a: Value, b: Value) -> Value {
        Value::from(
            TupleData::from_data(vec![
                (ClarityName::from_literal("a"), a),
                (ClarityName::from_literal("b"), b),
            ])
            .unwrap(),
        )
    }

    // The type of a `merge` expression is pushed down from its context (e.g. the declared
    // value type of a map), which may be wider than the types of the operands' fields: a
    // `none` literal is typed `(optional NoType)`. The following tests make sure that the
    // operands are generated with the result's field types in such cases.

    #[test]
    fn merge_rhs_none_field_widened_by_map_value_type() {
        let snippet = r#"
(define-map m uint { a: uint, b: (optional uint) })
(map-set m u1 (merge { a: u1 } { b: none }))
(map-get? m u1)
"#;

        crosscheck(
            snippet,
            Ok(Some(
                Value::some(tuple_ab(Value::UInt(1), Value::none())).unwrap(),
            )),
        );
    }

    #[test]
    fn merge_lhs_none_field_widened_by_map_value_type() {
        let snippet = r#"
(define-map m uint { a: (optional uint), b: uint })
(map-set m u1 (merge { a: none } { b: u2 }))
(map-get? m u1)
"#;

        crosscheck(
            snippet,
            Ok(Some(
                Value::some(tuple_ab(Value::none(), Value::UInt(2))).unwrap(),
            )),
        );
    }

    #[test]
    fn merge_lhs_none_field_overridden_by_rhs() {
        // The LHS field `a` is dropped from the result, so its own type must be kept
        // rather than being replaced by the result's type for `a`.
        let snippet = r#"
(define-map m uint { a: (optional uint), b: uint })
(map-set m u1 (merge { a: none, b: u1 } { a: (some u5) }))
(map-get? m u1)
"#;

        crosscheck(
            snippet,
            Ok(Some(
                Value::some(tuple_ab(
                    Value::some(Value::UInt(5)).unwrap(),
                    Value::UInt(1),
                ))
                .unwrap(),
            )),
        );
    }

    #[test]
    fn merge_both_sides_none_fields_widened() {
        let snippet = r#"
(define-map m uint { a: (optional uint), b: (optional int) })
(map-set m u1 (merge { a: none } { b: none }))
(map-get? m u1)
"#;

        crosscheck(
            snippet,
            Ok(Some(
                Value::some(tuple_ab(Value::none(), Value::none())).unwrap(),
            )),
        );
    }

    #[test]
    fn merge_rhs_nested_tuple_none_field_widened() {
        // The pushed-down type must propagate through the RHS `tuple` into its nested fields.
        let snippet = r#"
(define-map m uint { a: uint, b: { c: (optional uint), d: int } })
(map-set m u1 (merge { a: u1 } { b: { c: none, d: -1 } }))
(map-get? m u1)
"#;

        let nested = Value::from(
            TupleData::from_data(vec![
                (ClarityName::from_literal("c"), Value::none()),
                (ClarityName::from_literal("d"), Value::Int(-1)),
            ])
            .unwrap(),
        );

        crosscheck(
            snippet,
            Ok(Some(Value::some(tuple_ab(Value::UInt(1), nested)).unwrap())),
        );
    }

    #[test]
    fn merge_rhs_none_field_widened_by_data_var_type() {
        let snippet = r#"
(define-data-var v { a: uint, b: (optional uint) } { a: u0, b: (some u0) })
(var-set v (merge { a: u1 } { b: none }))
(var-get v)
"#;

        crosscheck(snippet, Ok(Some(tuple_ab(Value::UInt(1), Value::none()))));
    }

    #[test]
    fn merge_rhs_none_field_widened_by_map_insert_value_type() {
        let snippet = r#"
(define-map m uint { a: uint, b: (optional uint) })
(map-insert m u1 (merge { a: u1 } { b: none }))
(map-get? m u1)
"#;

        crosscheck(
            snippet,
            Ok(Some(
                Value::some(tuple_ab(Value::UInt(1), Value::none())).unwrap(),
            )),
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

        #[test]
        fn merge_real_example() {
            let snippet = r#"
    (define-read-only (read-buff-1 (cursor { bytes: (buff 8192), pos: uint }))
        (ok {
            value: (unwrap! (as-max-len? (unwrap! (slice? (get bytes cursor) (get pos cursor) (+ (get pos cursor) u1)) (err u1)) u1) (err u1)),
            next: { bytes: (get bytes cursor), pos: (+ (get pos cursor) u1) }
        }))

    (define-read-only (read-uint-8 (cursor { bytes: (buff 8192), pos: uint }))
        (let ((cursor-bytes (try! (read-buff-1 cursor))))
            (ok (merge cursor-bytes { value: (buff-to-uint-be (get value cursor-bytes)) }))))
                "#;

            crosscheck(snippet, Ok(None));
        }
    }

    #[test]
    fn tuple_less_than_one_arg() {
        let result = evaluate("(tuple)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting >= 1 arguments, got 0"));
    }

    #[test]
    fn get_less_than_two_args() {
        let result = evaluate("(get id)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 1"));
    }

    #[test]
    fn get_more_than_two_args() {
        let result = evaluate("(get id 2 3)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 3"));
    }

    #[test]
    fn merge_less_than_two_args() {
        let result = evaluate("(merge)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 0"));
    }

    #[test]
    fn merge_more_than_two_args() {
        let result = evaluate("(merge {a: 1} {b: 2} {c: 3})");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 3"));
    }
}
