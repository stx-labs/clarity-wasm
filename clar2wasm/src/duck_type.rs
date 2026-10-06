use std::collections::BTreeMap;

use clarity::vm::types::{SequenceSubtype, TupleTypeSignature, TypeSignature};
use clarity_types::types::StringSubtype;
use walrus::ir::{BinaryOp, Loop};
use walrus::{InstrSeqBuilder, LocalId, ValType};

use crate::wasm_generator::{
    add_placeholder_for_clarity_type, clar2wasm_ty, drop_value, GeneratorError, WasmGenerator,
};
use crate::wasm_utils::get_type_in_memory_size;

impl WasmGenerator {
    /// Converts the representation of a Value on top of the stack from a type to another type. The Value keeps the
    /// same value in the end, only its representation in locals and memory differs.
    /// This is a no-op if both types are identical.
    ///
    /// The original and target types should be "somewhat compatible" and validated by the typechecker
    /// for this function to succeed.
    ///
    /// We can pass the offset to a preallocated memory where the duck-typed value will be written.
    /// This can be necessary to avoid an overwriting of this value if any operation is done right after the duck-typing.
    /// If we ignore this argument, the duck-typed value will be written on top of the current call stack frame,
    /// and $stack-pointer will be moved past it. It is the caller's responsibility to reset $stack-pointer once
    /// the duck-typed value is not needed anymore.
    pub(crate) fn duck_type(
        &mut self,
        builder: &mut InstrSeqBuilder,
        og_ty: &TypeSignature,
        target_ty: &TypeSignature,
        preallocated_memory: Option<LocalId>,
    ) -> Result<(), GeneratorError> {
        // This is a no-op if both types are identical
        if !need_ducktyping(og_ty, target_ty) {
            return Ok(());
        }

        let memory_pointer = match preallocated_memory {
            Some(p) => p,
            None => {
                let (pointer, _) =
                    self.create_call_stack_bytes(builder, dt_needed_workspace(target_ty) as i32);
                pointer
            }
        };

        let locals = self.create_locals_for_ty(target_ty);
        self.duck_type_stack(builder, og_ty, target_ty, &locals, memory_pointer)?;
        for l in locals {
            builder.local_get(l);
        }

        Ok(())
    }

    fn duck_type_stack(
        &mut self,
        builder: &mut InstrSeqBuilder,
        og_ty: &TypeSignature,
        target_ty: &TypeSignature,
        locals: &[LocalId],
        allocated_mem_offset: LocalId,
    ) -> Result<(), GeneratorError> {
        match (og_ty, target_ty) {
            (TypeSignature::NoType, _) | (_, TypeSignature::NoType) => {
                // drop the useless original value from the stack
                drop_value(builder, og_ty);
                // set locals to zero values (needed for ducktying of list elements)
                add_placeholder_for_clarity_type(builder, target_ty);
                for &l in locals.iter().rev() {
                    builder.local_set(l);
                }
            }
            (TypeSignature::BoolType, TypeSignature::BoolType)
            | (TypeSignature::IntType, TypeSignature::IntType)
            | (TypeSignature::UIntType, TypeSignature::UIntType)
            | (
                TypeSignature::SequenceType(SequenceSubtype::BufferType(_)),
                TypeSignature::SequenceType(SequenceSubtype::BufferType(_)),
            )
            | (
                TypeSignature::SequenceType(SequenceSubtype::StringType(_)),
                TypeSignature::SequenceType(SequenceSubtype::StringType(_)),
            )
            | (TypeSignature::PrincipalType, TypeSignature::PrincipalType)
            | (TypeSignature::CallableType(_), TypeSignature::CallableType(_))
            | (TypeSignature::PrincipalType, TypeSignature::CallableType(_))
            | (TypeSignature::CallableType(_), TypeSignature::PrincipalType)
            | (TypeSignature::TraitReferenceType(_), TypeSignature::TraitReferenceType(_)) => {
                for &l in locals.iter().rev() {
                    builder.local_set(l);
                }
            }
            (TypeSignature::OptionalType(og_subty), TypeSignature::OptionalType(target_subty)) => {
                let (variant_local, sub_locals) = locals.split_first().ok_or_else(|| {
                    GeneratorError::InternalError(
                        "Not enough locals for duck-typing an optional".to_owned(),
                    )
                })?;
                self.duck_type_stack(
                    builder,
                    og_subty,
                    target_subty,
                    sub_locals,
                    allocated_mem_offset,
                )?;
                builder.local_set(*variant_local);
            }
            (TypeSignature::ResponseType(og_subty), TypeSignature::ResponseType(target_subty)) => {
                let (og_ok_ty, og_err_ty) = og_subty.as_ref();
                let (target_ok_ty, target_err_ty) = target_subty.as_ref();

                let (variant_local, inner_locals) = locals.split_first().ok_or_else(|| {
                    GeneratorError::InternalError(
                        "Not enough locals for duck-typing a response".to_owned(),
                    )
                })?;
                let (ok_locals, err_locals) = inner_locals
                    .split_at_checked(clar2wasm_ty(target_ok_ty).len())
                    .ok_or_else(|| {
                        GeneratorError::InternalError(
                            "Not enough locals for duck-typing a response".to_owned(),
                        )
                    })?;

                self.duck_type_stack(
                    builder,
                    og_err_ty,
                    target_err_ty,
                    err_locals,
                    allocated_mem_offset,
                )?;
                self.duck_type_stack(
                    builder,
                    og_ok_ty,
                    target_ok_ty,
                    ok_locals,
                    allocated_mem_offset,
                )?;
                builder.local_set(*variant_local);
            }
            (TypeSignature::TupleType(og_tup_ty), TypeSignature::TupleType(target_tup_ty)) => {
                // Fields are matched by name: the original tuple can have hidden fields that the target
                // doesn't list (see `with_hidden_tuple_fields`), and those are dropped.
                let target_map = target_tup_ty.get_type_map();

                let mut remaining_locals = locals;
                for (name, og_subty) in og_tup_ty.get_type_map().iter().rev() {
                    let Some(target_subty) = target_map.get(name) else {
                        drop_value(builder, og_subty);
                        continue;
                    };
                    let current_locals;
                    (remaining_locals, current_locals) = remaining_locals
                        .split_at_checked(remaining_locals.len() - clar2wasm_ty(target_subty).len())
                        .ok_or_else(|| {
                            GeneratorError::InternalError(
                                "Not enough locals for duck-typing a tuple".to_owned(),
                            )
                        })?;
                    self.duck_type_stack(
                        builder,
                        og_subty,
                        target_subty,
                        current_locals,
                        allocated_mem_offset,
                    )?;
                }
            }
            (
                TypeSignature::SequenceType(SequenceSubtype::ListType(og_ltd)),
                TypeSignature::SequenceType(SequenceSubtype::ListType(target_ltd)),
            ) => {
                let og_elem_ty = og_ltd.get_list_item_type();
                let target_elem_ty = target_ltd.get_list_item_type();

                // Set list length and offset to locals, and reserve some working space to store the target elements
                let [offset, length] = locals else {
                    return Err(GeneratorError::InternalError(
                        "List duck typing should use only two locals".to_owned(),
                    ));
                };

                let offset_target = self.module.locals.add(ValType::I32);
                let length_target = self.module.locals.add(ValType::I32);

                builder.local_set(*length);
                builder.local_set(*offset);

                // A list which can never hold an element is already in the representation of the
                // target list: its (offset, length) is on the stack, and there is no element to
                // convert. The element types don't even have to be compatible, since the
                // typechecker admits an empty list into any list type.
                if og_ltd.get_max_len() == 0 {
                    return Ok(());
                }

                // Create locals for the element target repr.
                let target_locs = self.create_locals_for_ty(target_elem_ty);

                // iterate through elements, convert them to target type and store them
                let loop_id = {
                    let mut loop_ = builder.dangling_instr_seq(None);
                    let loop_id = loop_.id();

                    let og_elem_size = self.read_from_memory(&mut loop_, *offset, 0, og_elem_ty)?;
                    self.duck_type_stack(
                        &mut loop_,
                        og_elem_ty,
                        target_elem_ty,
                        &target_locs,
                        allocated_mem_offset,
                    )?;
                    for l in target_locs.iter() {
                        loop_.local_get(*l);
                    }
                    let target_elem_size =
                        self.write_to_memory(&mut loop_, offset_target, 0, target_elem_ty)?;

                    loop_
                        .local_get(*offset)
                        .i32_const(og_elem_size)
                        .binop(BinaryOp::I32Add)
                        .local_set(*offset);
                    loop_
                        .local_get(offset_target)
                        .i32_const(target_elem_size as i32)
                        .binop(BinaryOp::I32Add)
                        .local_set(offset_target);
                    loop_
                        .local_get(length_target)
                        .i32_const(target_elem_size as i32)
                        .binop(BinaryOp::I32Add)
                        .local_set(length_target);
                    loop_
                        .local_get(*length)
                        .i32_const(og_elem_size)
                        .binop(BinaryOp::I32Sub)
                        .local_tee(*length)
                        .br_if(loop_id);

                    loop_id
                };

                // we will "duck-type-clone" if the length of the list is not empty
                builder.local_get(*length).if_else(
                    None,
                    |then| {
                        then.i32_const(0).local_set(length_target);
                        // we set the offset_target to copy at the free space of stack-pointer and we move this on further
                        then.local_get(allocated_mem_offset)
                            .local_tee(offset_target)
                            .i32_const(get_type_in_memory_size(target_ty, false))
                            .binop(BinaryOp::I32Add)
                            .local_set(allocated_mem_offset);

                        // we put the resulting offset/length on the stack
                        then.local_get(offset_target);

                        // the cloning loop
                        then.instr(Loop { seq: loop_id });

                        // we set the result back to the correct locals
                        then.local_set(*offset);
                        then.local_get(length_target).local_set(*length);
                    },
                    |_else| {},
                );
            }
            (TypeSignature::ListUnionType(_), TypeSignature::ListUnionType(_)) => {
                return Err(GeneratorError::InternalError(
                    "Unconcretized ListUnionType".to_owned(),
                ))
            }
            _ => {
                return Err(GeneratorError::TypeError(format!(
                    "Incompatible types for duck typing:\n\t{og_ty:?}\n\t{target_ty:?}"
                )))
            }
        }
        Ok(())
    }

    fn create_locals_for_ty(&mut self, ty: &TypeSignature) -> Vec<LocalId> {
        clar2wasm_ty(ty)
            .into_iter()
            .map(|vt| self.module.locals.add(vt))
            .collect()
    }
}

pub fn need_ducktyping(og_ty: &TypeSignature, tg_ty: &TypeSignature) -> bool {
    match og_ty {
        TypeSignature::NoType
        | TypeSignature::BoolType
        | TypeSignature::IntType
        | TypeSignature::UIntType => og_ty != tg_ty,
        TypeSignature::PrincipalType
        | TypeSignature::CallableType(_)
        | TypeSignature::TraitReferenceType(_) => !matches!(
            tg_ty,
            TypeSignature::PrincipalType
                | TypeSignature::CallableType(_)
                | TypeSignature::TraitReferenceType(_),
        ),
        TypeSignature::SequenceType(SequenceSubtype::BufferType(_)) => !matches!(
            tg_ty,
            TypeSignature::SequenceType(SequenceSubtype::BufferType(_))
        ),
        TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(_))) => {
            !matches!(
                tg_ty,
                TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(_)))
            )
        }
        TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(_))) => {
            !matches!(
                tg_ty,
                TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(_)))
            )
        }
        TypeSignature::SequenceType(SequenceSubtype::ListType(og_ltd)) => {
            if let TypeSignature::SequenceType(SequenceSubtype::ListType(tg_ltd)) = tg_ty {
                // a list which can never hold an element has nothing to convert
                og_ltd.get_max_len() > 0
                    && need_ducktyping(og_ltd.get_list_item_type(), tg_ltd.get_list_item_type())
            } else {
                false
            }
        }
        TypeSignature::TupleType(og_tup_ty) => {
            if let TypeSignature::TupleType(tg_tup_ty) = tg_ty {
                let og_map = og_tup_ty.get_type_map();
                let tg_map = tg_tup_ty.get_type_map();
                og_map.len() != tg_map.len()
                    || og_map.iter().zip(tg_map).any(
                        |((og_name, og_elem_ty), (tg_name, tg_elem_ty))| {
                            og_name != tg_name || need_ducktyping(og_elem_ty, tg_elem_ty)
                        },
                    )
            } else {
                false
            }
        }
        TypeSignature::OptionalType(og_opt_ty) => {
            if let TypeSignature::OptionalType(tg_opt_ty) = tg_ty {
                need_ducktyping(og_opt_ty, tg_opt_ty)
            } else {
                false
            }
        }
        TypeSignature::ResponseType(og_resp_ty) => {
            if let TypeSignature::ResponseType(tg_resp_ty) = tg_ty {
                need_ducktyping(&og_resp_ty.as_ref().0, &tg_resp_ty.as_ref().0)
                    || need_ducktyping(&og_resp_ty.as_ref().1, &tg_resp_ty.as_ref().1)
            } else {
                false
            }
        }
        TypeSignature::ListUnionType(_) => {
            unreachable!("ListUnionType should not exist at this point")
        }
    }
}

/// Returns `target`, plus the hidden tuple fields of `own`: the fields it has and `target` doesn't,
/// at any nesting level.
///
/// When the typechecker joins two types (`if` branches, list elements, ...), the resulting tuple types
/// only keep the fields of the first one. An expression with hidden fields still builds all of them, so it
/// has to be traversed with this type, and duck-typed to `target` afterwards (which drops the hidden fields).
///
/// The result is equal to `target` when `own` has no hidden fields.
pub(crate) fn with_hidden_tuple_fields(
    target: &TypeSignature,
    own: &TypeSignature,
) -> Result<TypeSignature, GeneratorError> {
    match (target, own) {
        (TypeSignature::TupleType(tg_tup_ty), TypeSignature::TupleType(own_tup_ty)) => {
            let tg_map = tg_tup_ty.get_type_map();
            let fields = own_tup_ty
                .get_type_map()
                .iter()
                .map(|(name, own_subty)| {
                    let subty = match tg_map.get(name) {
                        Some(tg_subty) => with_hidden_tuple_fields(tg_subty, own_subty)?,
                        None => own_subty.clone(),
                    };
                    Ok((name.clone(), subty))
                })
                .collect::<Result<BTreeMap<_, _>, GeneratorError>>()?;
            TupleTypeSignature::try_from(fields)
                .map(TypeSignature::from)
                .map_err(|e| GeneratorError::TypeError(format!("Invalid tuple type: {e}")))
        }
        (TypeSignature::OptionalType(tg_subty), TypeSignature::OptionalType(own_subty)) => Ok(
            TypeSignature::OptionalType(Box::new(with_hidden_tuple_fields(tg_subty, own_subty)?)),
        ),
        (TypeSignature::ResponseType(tg_subty), TypeSignature::ResponseType(own_subty)) => {
            let (tg_ok_ty, tg_err_ty) = tg_subty.as_ref();
            let (own_ok_ty, own_err_ty) = own_subty.as_ref();
            Ok(TypeSignature::ResponseType(Box::new((
                with_hidden_tuple_fields(tg_ok_ty, own_ok_ty)?,
                with_hidden_tuple_fields(tg_err_ty, own_err_ty)?,
            ))))
        }
        (
            TypeSignature::SequenceType(SequenceSubtype::ListType(tg_ltd)),
            TypeSignature::SequenceType(SequenceSubtype::ListType(own_ltd)),
        ) if own_ltd.get_max_len() > 0 => {
            let item_ty = with_hidden_tuple_fields(
                tg_ltd.get_list_item_type(),
                own_ltd.get_list_item_type(),
            )?;
            TypeSignature::list_of(item_ty, tg_ltd.get_max_len())
                .map_err(|e| GeneratorError::TypeError(format!("Invalid list type: {e}")))
        }
        _ => Ok(target.clone()),
    }
}

pub fn dt_needed_workspace(ty: &TypeSignature) -> u32 {
    match ty {
        TypeSignature::OptionalType(opt) => dt_needed_workspace(opt),
        TypeSignature::ResponseType(resp) => {
            dt_needed_workspace(&resp.0) + dt_needed_workspace(&resp.1)
        }
        TypeSignature::TupleType(tup) => tup.get_type_map().values().map(dt_needed_workspace).sum(),
        TypeSignature::SequenceType(SequenceSubtype::ListType(_)) => {
            // we need the full capacity for a list in memory except for its actual offset and length which will be on the stack
            get_type_in_memory_size(ty, true) as u32 - 8
        }
        _ => 0,
    }
}

#[cfg(test)]
mod tests {

    use clarity::vm::types::{
        ListTypeData, ResponseData, SequenceSubtype, TupleData, TupleTypeSignature, TypeSignature,
    };
    use clarity::vm::{ClarityName, Value};
    #[allow(unused_imports)]
    use clarity_types::ContractName;

    use super::{need_ducktyping, with_hidden_tuple_fields};
    #[allow(unused_imports)]
    use crate::tools::crosscheck_multi_contract;
    use crate::wasm_generator::WasmGenerator;

    fn duck_type_test(value: &Value, original_ty: &TypeSignature, target_ty: &TypeSignature) {
        duck_type_test_expecting(value, original_ty, target_ty, value);
    }

    fn duck_type_test_expecting(
        value: &Value,
        original_ty: &TypeSignature,
        target_ty: &TypeSignature,
        expected: &Value,
    ) {
        let mut gen = WasmGenerator::empty();
        gen.create_module(target_ty, |gen, builder| {
            gen.pass_value(builder, value, original_ty)
                .expect("failed to write instructions for original value");

            gen.duck_type(builder, original_ty, target_ty, None)
                .expect("failed to write duck type instructions");
        });
        let res = gen.execute_module(target_ty);

        assert_eq!(expected, &res);
    }

    fn tuple_ty(fields: Vec<(&'static str, TypeSignature)>) -> TypeSignature {
        TupleTypeSignature::try_from(
            fields
                .into_iter()
                .map(|(name, ty)| (ClarityName::from_literal(name), ty))
                .collect::<Vec<_>>(),
        )
        .unwrap()
        .into()
    }

    fn tuple_value(fields: Vec<(&'static str, Value)>) -> Value {
        TupleData::from_data(
            fields
                .into_iter()
                .map(|(name, value)| (ClarityName::from_literal(name), value))
                .collect(),
        )
        .unwrap()
        .into()
    }

    #[test]
    fn duck_type_optional_int() {
        let value = Value::none();
        let og_ty = TypeSignature::OptionalType(Box::new(TypeSignature::NoType));
        let target_ty = TypeSignature::OptionalType(Box::new(TypeSignature::IntType));

        duck_type_test(&value, &og_ty, &target_ty);
    }

    #[test]
    fn duck_type_optional_string() {
        let value = Value::none();
        let og_ty = TypeSignature::OptionalType(Box::new(TypeSignature::NoType));
        let target_ty = TypeSignature::OptionalType(Box::new(TypeSignature::SequenceType(
            clarity::vm::types::SequenceSubtype::StringType(
                clarity::vm::types::StringSubtype::ASCII(999u32.try_into().unwrap()),
            ),
        )));

        duck_type_test(&value, &og_ty, &target_ty);
    }

    #[test]
    fn duck_type_response_int_int_from_ok() {
        let value = Value::okay(Value::Int(42)).unwrap();
        let og_ty =
            TypeSignature::ResponseType(Box::new((TypeSignature::IntType, TypeSignature::NoType)));
        let target_ty =
            TypeSignature::ResponseType(Box::new((TypeSignature::IntType, TypeSignature::IntType)));

        duck_type_test(&value, &og_ty, &target_ty);
    }

    #[test]
    fn duck_type_response_int_int_from_err() {
        let value = Value::error(Value::Int(42)).unwrap();
        let og_ty =
            TypeSignature::ResponseType(Box::new((TypeSignature::NoType, TypeSignature::IntType)));
        let target_ty =
            TypeSignature::ResponseType(Box::new((TypeSignature::IntType, TypeSignature::IntType)));

        duck_type_test(&value, &og_ty, &target_ty);
    }

    #[test]
    fn duck_type_response_string_int_from_ok() {
        let value = Value::okay(Value::string_ascii_from_bytes("hello".bytes().collect()).unwrap())
            .unwrap();
        let og_ty = TypeSignature::ResponseType(Box::new((
            TypeSignature::SequenceType(clarity::vm::types::SequenceSubtype::StringType(
                clarity::vm::types::StringSubtype::ASCII(42u32.try_into().unwrap()),
            )),
            TypeSignature::NoType,
        )));
        let target_ty = TypeSignature::ResponseType(Box::new((
            TypeSignature::SequenceType(clarity::vm::types::SequenceSubtype::StringType(
                clarity::vm::types::StringSubtype::ASCII(42u32.try_into().unwrap()),
            )),
            TypeSignature::IntType,
        )));

        duck_type_test(&value, &og_ty, &target_ty);
    }

    #[test]
    fn duck_type_response_string_int_from_err() {
        let value = Value::error(Value::Int(42)).unwrap();
        let og_ty =
            TypeSignature::ResponseType(Box::new((TypeSignature::NoType, TypeSignature::IntType)));
        let target_ty = TypeSignature::ResponseType(Box::new((
            TypeSignature::SequenceType(clarity::vm::types::SequenceSubtype::StringType(
                clarity::vm::types::StringSubtype::ASCII(42u32.try_into().unwrap()),
            )),
            TypeSignature::IntType,
        )));

        duck_type_test(&value, &og_ty, &target_ty);
    }

    #[test]
    fn duck_type_tuple() {
        let value = Value::from(
            TupleData::from_data(vec![
                (ClarityName::from_literal("a"), Value::Int(42)),
                (ClarityName::from_literal("b"), Value::none()),
                (
                    ClarityName::from_literal("c"),
                    Value::buff_from(vec![1, 2, 3, 4, 5]).unwrap(),
                ),
                (
                    ClarityName::from_literal("d"),
                    Value::Response(ResponseData {
                        committed: true,
                        data: Box::new(Value::none()),
                    }),
                ),
            ])
            .unwrap(),
        );
        let og_ty = TypeSignature::TupleType(
            TupleTypeSignature::try_from(vec![
                (ClarityName::from_literal("a"), TypeSignature::IntType),
                (
                    ClarityName::from_literal("b"),
                    TypeSignature::OptionalType(Box::new(TypeSignature::NoType)),
                ),
                (
                    ClarityName::from_literal("c"),
                    TypeSignature::SequenceType(clarity::vm::types::SequenceSubtype::BufferType(
                        500u32.try_into().unwrap(),
                    )),
                ),
                (
                    ClarityName::from_literal("d"),
                    TypeSignature::ResponseType(Box::new((
                        TypeSignature::OptionalType(Box::new(TypeSignature::NoType)),
                        TypeSignature::NoType,
                    ))),
                ),
            ])
            .unwrap(),
        );
        let target_ty = TypeSignature::TupleType(
            TupleTypeSignature::try_from(vec![
                (ClarityName::from_literal("a"), TypeSignature::IntType),
                (
                    ClarityName::from_literal("b"),
                    TypeSignature::OptionalType(Box::new(TypeSignature::UIntType)),
                ),
                (
                    ClarityName::from_literal("c"),
                    TypeSignature::SequenceType(clarity::vm::types::SequenceSubtype::BufferType(
                        500u32.try_into().unwrap(),
                    )),
                ),
                (
                    ClarityName::from_literal("d"),
                    TypeSignature::ResponseType(Box::new((
                        TypeSignature::OptionalType(Box::new(TypeSignature::IntType)),
                        TypeSignature::BoolType,
                    ))),
                ),
            ])
            .unwrap(),
        );

        duck_type_test(&value, &og_ty, &target_ty);
    }

    #[test]
    fn duck_type_tuple_drops_hidden_fields() {
        let value = tuple_value(vec![
            ("a", Value::Int(42)),
            ("b", Value::buff_from(vec![1, 2, 3]).unwrap()),
            ("c", Value::some(Value::Bool(true)).unwrap()),
            ("d", Value::UInt(7)),
        ]);
        let og_ty = tuple_ty(vec![
            ("a", TypeSignature::IntType),
            (
                "b",
                TypeSignature::SequenceType(SequenceSubtype::BufferType(3u32.try_into().unwrap())),
            ),
            (
                "c",
                TypeSignature::OptionalType(Box::new(TypeSignature::BoolType)),
            ),
            ("d", TypeSignature::UIntType),
        ]);
        let target_ty = tuple_ty(vec![
            ("a", TypeSignature::IntType),
            (
                "c",
                TypeSignature::OptionalType(Box::new(TypeSignature::BoolType)),
            ),
        ]);
        let expected = tuple_value(vec![
            ("a", Value::Int(42)),
            ("c", Value::some(Value::Bool(true)).unwrap()),
        ]);

        duck_type_test_expecting(&value, &og_ty, &target_ty, &expected);
    }

    #[test]
    fn duck_type_list_drops_hidden_tuple_fields() {
        let value = Value::cons_list_unsanitized(vec![
            tuple_value(vec![("a", Value::UInt(1)), ("k", Value::Bool(true))]),
            tuple_value(vec![("a", Value::UInt(2)), ("k", Value::Bool(false))]),
        ])
        .unwrap();
        let og_ty = TypeSignature::list_of(
            tuple_ty(vec![
                ("a", TypeSignature::UIntType),
                ("k", TypeSignature::BoolType),
            ]),
            2,
        )
        .unwrap();
        let target_ty =
            TypeSignature::list_of(tuple_ty(vec![("a", TypeSignature::UIntType)]), 2).unwrap();
        let expected = Value::cons_list_unsanitized(vec![
            tuple_value(vec![("a", Value::UInt(1))]),
            tuple_value(vec![("a", Value::UInt(2))]),
        ])
        .unwrap();

        duck_type_test_expecting(&value, &og_ty, &target_ty, &expected);
    }

    #[test]
    fn hidden_tuple_fields_need_ducktyping() {
        let narrow_ty = tuple_ty(vec![("a", TypeSignature::UIntType)]);
        let hidden_ty = tuple_ty(vec![
            ("a", TypeSignature::UIntType),
            ("k", TypeSignature::BoolType),
        ]);
        // same number of fields, different names
        let renamed_ty = tuple_ty(vec![("b", TypeSignature::UIntType)]);

        assert!(!need_ducktyping(&narrow_ty, &narrow_ty));
        assert!(need_ducktyping(&hidden_ty, &narrow_ty));
        assert!(need_ducktyping(&renamed_ty, &narrow_ty));
    }

    #[test]
    fn with_hidden_tuple_fields_without_hidden_fields_is_target() {
        let target_ty = TypeSignature::ResponseType(Box::new((
            tuple_ty(vec![(
                "a",
                TypeSignature::OptionalType(Box::new(TypeSignature::IntType)),
            )]),
            TypeSignature::list_of(TypeSignature::IntType, 4).unwrap(),
        )));
        let own_ty = TypeSignature::ResponseType(Box::new((
            tuple_ty(vec![(
                "a",
                TypeSignature::OptionalType(Box::new(TypeSignature::NoType)),
            )]),
            TypeSignature::NoType,
        )));

        assert_eq!(
            with_hidden_tuple_fields(&target_ty, &own_ty).unwrap(),
            target_ty
        );
        assert_eq!(
            with_hidden_tuple_fields(&target_ty, &target_ty).unwrap(),
            target_ty
        );
    }

    #[test]
    fn with_hidden_tuple_fields_keeps_nested_hidden_fields() {
        let target_ty = TypeSignature::OptionalType(Box::new(tuple_ty(vec![
            (
                "a",
                TypeSignature::OptionalType(Box::new(TypeSignature::IntType)),
            ),
            (
                "l",
                TypeSignature::list_of(tuple_ty(vec![("x", TypeSignature::UIntType)]), 5).unwrap(),
            ),
        ])));
        let own_ty = TypeSignature::OptionalType(Box::new(tuple_ty(vec![
            (
                "a",
                TypeSignature::OptionalType(Box::new(TypeSignature::NoType)),
            ),
            ("k", TypeSignature::BoolType),
            (
                "l",
                TypeSignature::list_of(
                    tuple_ty(vec![
                        ("x", TypeSignature::UIntType),
                        ("y", TypeSignature::IntType),
                    ]),
                    2,
                )
                .unwrap(),
            ),
        ])));

        // shared fields and the list length come from the target, hidden fields from `own`
        let expected = TypeSignature::OptionalType(Box::new(tuple_ty(vec![
            (
                "a",
                TypeSignature::OptionalType(Box::new(TypeSignature::IntType)),
            ),
            ("k", TypeSignature::BoolType),
            (
                "l",
                TypeSignature::list_of(
                    tuple_ty(vec![
                        ("x", TypeSignature::UIntType),
                        ("y", TypeSignature::IntType),
                    ]),
                    5,
                )
                .unwrap(),
            ),
        ])));

        assert_eq!(
            with_hidden_tuple_fields(&target_ty, &own_ty).unwrap(),
            expected
        );
    }

    #[test]
    fn with_hidden_tuple_fields_ignores_empty_list() {
        let target_ty =
            TypeSignature::list_of(tuple_ty(vec![("a", TypeSignature::UIntType)]), 3).unwrap();
        let own_ty = TypeSignature::list_of(
            tuple_ty(vec![
                ("a", TypeSignature::UIntType),
                ("k", TypeSignature::BoolType),
            ]),
            0,
        )
        .unwrap();

        assert_eq!(
            with_hidden_tuple_fields(&target_ty, &own_ty).unwrap(),
            target_ty
        );
    }

    #[test]
    fn duck_type_list_response() {
        let value = Value::cons_list_unsanitized(vec![
            Value::okay(Value::Int(1)).unwrap(),
            Value::okay(Value::Int(2)).unwrap(),
            Value::okay(Value::Int(3)).unwrap(),
            Value::okay(Value::Int(4)).unwrap(),
        ])
        .unwrap();
        let og_ty = TypeSignature::SequenceType(SequenceSubtype::ListType(
            ListTypeData::new_list(
                TypeSignature::ResponseType(Box::new((
                    TypeSignature::IntType,
                    TypeSignature::NoType,
                ))),
                4,
            )
            .unwrap(),
        ));

        let target_ty = TypeSignature::SequenceType(SequenceSubtype::ListType(
            ListTypeData::new_list(
                TypeSignature::ResponseType(Box::new((
                    TypeSignature::IntType,
                    TypeSignature::PrincipalType,
                ))),
                4,
            )
            .unwrap(),
        ));

        duck_type_test(&value, &og_ty, &target_ty);
    }

    #[test]
    fn duck_type_list_list_response() {
        let list_okay_int_value = |int| {
            Value::cons_list_unsanitized(vec![Value::okay(Value::Int(int)).unwrap()]).unwrap()
        };
        let value = Value::cons_list_unsanitized(vec![
            list_okay_int_value(1),
            list_okay_int_value(2),
            list_okay_int_value(3),
            list_okay_int_value(4),
        ])
        .unwrap();
        let og_ty = TypeSignature::SequenceType(SequenceSubtype::ListType(
            ListTypeData::new_list(
                TypeSignature::SequenceType(SequenceSubtype::ListType(
                    ListTypeData::new_list(
                        TypeSignature::ResponseType(Box::new((
                            TypeSignature::IntType,
                            TypeSignature::NoType,
                        ))),
                        1,
                    )
                    .unwrap(),
                )),
                4,
            )
            .unwrap(),
        ));

        let target_ty = TypeSignature::SequenceType(SequenceSubtype::ListType(
            ListTypeData::new_list(
                TypeSignature::SequenceType(SequenceSubtype::ListType(
                    ListTypeData::new_list(
                        TypeSignature::ResponseType(Box::new((
                            TypeSignature::IntType,
                            TypeSignature::PrincipalType,
                        ))),
                        1,
                    )
                    .unwrap(),
                )),
                4,
            )
            .unwrap(),
        ));

        duck_type_test(&value, &og_ty, &target_ty);
    }

    #[test]
    fn empty_list_needs_no_ducktyping() {
        let target_ty = TypeSignature::list_of(TypeSignature::BUFFER_1, 8).unwrap();

        assert!(!need_ducktyping(
            &TypeSignature::list_of(TypeSignature::IntType, 0).unwrap(),
            &target_ty
        ));

        // the very same element types have to be converted as soon as the list can hold an element
        assert!(need_ducktyping(
            &TypeSignature::list_of(TypeSignature::IntType, 1).unwrap(),
            &target_ty
        ));
    }

    // The typechecker admits an empty list into any list type without ever looking at its element
    // type, so both of these duck-type a list whose elements could not be converted at all.
    #[test]
    fn duck_type_empty_list_with_incompatible_elements() {
        let value = Value::cons_list_unsanitized(vec![]).unwrap();
        let og_ty = TypeSignature::SequenceType(SequenceSubtype::ListType(
            ListTypeData::new_list(TypeSignature::IntType, 0).unwrap(),
        ));

        let target_ty = TypeSignature::SequenceType(SequenceSubtype::ListType(
            ListTypeData::new_list(TypeSignature::BUFFER_1, 8).unwrap(),
        ));

        duck_type_test(&value, &og_ty, &target_ty);
    }

    #[test]
    fn duck_type_response_with_empty_list_from_ok() {
        // the err type is what makes the response need duck-typing, so the empty list is reached
        // from the recursion, which doesn't check whether a conversion is needed.
        let value = Value::okay(Value::cons_list_unsanitized(vec![]).unwrap()).unwrap();
        let og_ty = TypeSignature::ResponseType(Box::new((
            TypeSignature::SequenceType(SequenceSubtype::ListType(
                ListTypeData::new_list(TypeSignature::IntType, 0).unwrap(),
            )),
            TypeSignature::NoType,
        )));

        let target_ty = TypeSignature::ResponseType(Box::new((
            TypeSignature::SequenceType(SequenceSubtype::ListType(
                ListTypeData::new_list(TypeSignature::BUFFER_1, 8).unwrap(),
            )),
            TypeSignature::PrincipalType,
        )));

        duck_type_test(&value, &og_ty, &target_ty);
    }

    // The redefinition of t with type foo-trait clashes with definition of the trait t in foo contract for clarity v1
    #[cfg(not(feature = "test-clarity-v1"))]
    #[test]
    fn duck_typing_principal_and_callable() {
        let foo = "
            (define-trait t
                ((foo () (response bool uint)))
            )

            (define-public (foo) (ok true))
        ";

        let bar = r#"
            (use-trait foo-trait .foo.t)

            (define-constant callee .foo)

            (define-private (call-it (t <foo-trait>))
                (contract-call? t foo)
            )

            (call-it callee)
        "#;

        crosscheck_multi_contract(
            &[
                (ContractName::from_literal("foo"), foo),
                (ContractName::from_literal("bar"), bar),
            ],
            Ok(Some(Value::okay_true())),
        );
    }
}
