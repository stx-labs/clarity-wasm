use clarity::vm::types::{SequenceSubtype, TypeSignature};
use walrus::ir::{BinaryOp, IfElse, Loop};
use walrus::{InstrSeqBuilder, LocalId};

use crate::wasm_generator::{clar2wasm_ty, has_in_memory_type, GeneratorError, WasmGenerator};

impl WasmGenerator {
    /// Copies a value in *locals* to *copy_offset* while taking care of the in-memory values
    /// , especilly inner in-memory values.
    pub fn copy_value(
        &mut self,
        builder: &mut InstrSeqBuilder,
        ty: &TypeSignature,
        locals: &[LocalId],
        copy_offset: LocalId,
    ) -> Result<(), GeneratorError> {
        match ty {
            TypeSignature::NoType
            | TypeSignature::IntType
            | TypeSignature::UIntType
            | TypeSignature::BoolType => Ok(()),
            TypeSignature::SequenceType(SequenceSubtype::ListType(ltd)) => {
                let [offset, len] = locals else {
                    return Err(GeneratorError::InternalError(
                        "Copy: a list type should be (offset, length)".to_owned(),
                    ));
                };
                let memory = self.get_memory()?;

                // we will copy the entire list as is to its destination first
                builder
                    .local_get(copy_offset)
                    .local_get(*offset)
                    .local_get(*len)
                    .memory_copy(memory, memory);

                // update the offset to copy_offset, then move copy_offset to point after the list
                builder.local_get(copy_offset).local_set(*offset);
                builder
                    .local_get(copy_offset)
                    .local_get(*len)
                    .binop(BinaryOp::I32Add)
                    .local_set(copy_offset);

                // now we will iterate through the list elements, copy the in-memory parts and update the pointers
                let copy_loop = {
                    let mut loop_ = builder.dangling_instr_seq(None);
                    let loop_id = loop_.id();

                    let elem_ty = ltd.get_list_item_type();

                    let size = self.read_from_memory(&mut loop_, *offset, 0, elem_ty)?;
                    let elem_locals = self.save_to_locals(&mut loop_, elem_ty, true);

                    self.copy_value(&mut loop_, elem_ty, &elem_locals, copy_offset)?;
                    for l in elem_locals {
                        loop_.local_get(l);
                    }
                    self.write_to_memory(&mut loop_, *offset, 0, elem_ty)?;

                    loop_
                        .local_get(*offset)
                        .i32_const(size)
                        .binop(BinaryOp::I32Add)
                        .local_set(*offset);
                    loop_
                        .local_get(*len)
                        .i32_const(size)
                        .binop(BinaryOp::I32Sub)
                        .local_tee(*len)
                        .br_if(loop_id);

                    loop_id
                };

                // if we have elements, we will store the (offset, len) on the stack, execute the copy loop, then get back the (offset, len)
                builder.local_get(*len).if_else(
                    None,
                    |then| {
                        then.local_get(*offset)
                            .local_get(*len)
                            .instr(Loop { seq: copy_loop })
                            .local_set(*len)
                            .local_set(*offset);
                    },
                    |_| {},
                );

                Ok(())
            }
            TypeSignature::SequenceType(_)
            | TypeSignature::PrincipalType
            | TypeSignature::CallableType(_)
            | TypeSignature::TraitReferenceType(_) => {
                let [offset, len] = locals else {
                    return Err(GeneratorError::InternalError(
                        "Copy: a simple in-memory type should be (offset, length)".to_owned(),
                    ));
                };

                let memory = self.get_memory()?;
                builder
                    .local_get(copy_offset)
                    .local_get(*offset)
                    .local_get(*len)
                    .memory_copy(memory, memory);
                // Set the new offset
                builder.local_get(copy_offset).local_set(*offset);
                // Increment the copy offset
                builder
                    .local_get(copy_offset)
                    .local_get(*len)
                    .binop(BinaryOp::I32Add)
                    .local_set(copy_offset);
                Ok(())
            }
            TypeSignature::OptionalType(opt) => {
                let some_id = {
                    let mut some = builder.dangling_instr_seq(None);
                    self.copy_value(&mut some, opt, &locals[1..], copy_offset)?;
                    some.id()
                };
                let none_id = builder.dangling_instr_seq(None).id();

                builder.local_get(locals[0]).instr(IfElse {
                    consequent: some_id,
                    alternative: none_id,
                });

                Ok(())
            }
            TypeSignature::ResponseType(resp) => {
                let (ok_ty, err_ty) = &**resp;
                let variant = locals[0];
                let (ok_locals, err_locals) = locals[1..].split_at(clar2wasm_ty(ok_ty).len());
                let ok_id = {
                    let mut ok = builder.dangling_instr_seq(None);
                    if has_in_memory_type(ok_ty) {
                        self.copy_value(&mut ok, ok_ty, ok_locals, copy_offset)?;
                    }
                    ok.id()
                };
                let err_id = {
                    let mut err = builder.dangling_instr_seq(None);
                    if has_in_memory_type(err_ty) {
                        self.copy_value(&mut err, err_ty, err_locals, copy_offset)?;
                    }
                    err.id()
                };
                builder.local_get(variant).instr(IfElse {
                    consequent: ok_id,
                    alternative: err_id,
                });
                Ok(())
            }
            TypeSignature::TupleType(tuple_type_signature) => {
                let inner_ty_and_locals = tuple_type_signature.get_type_map().values().scan(
                    locals,
                    |remaining_locals, ty| {
                        let current_locals;
                        (current_locals, *remaining_locals) =
                            remaining_locals.split_at(clar2wasm_ty(ty).len());
                        Some((ty, current_locals))
                    },
                );

                for (ty, locals) in inner_ty_and_locals {
                    if has_in_memory_type(ty) {
                        self.copy_value(builder, ty, locals, copy_offset)?;
                    }
                }
                Ok(())
            }
            TypeSignature::ListUnionType(_) => {
                unreachable!("ListUnionType is not a value type")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use clarity_types::types::{PrincipalData, TupleData, TypeSignature};
    use clarity_types::Value;

    use crate::wasm_generator::WasmGenerator;
    use crate::wasm_utils::get_type_in_memory_size;

    fn copy_test(value: &Value, ty: &TypeSignature) {
        let mut gen = WasmGenerator::empty();

        gen.create_module(ty, |gen, builder| {
            let memory = gen.get_memory().expect("couldn't find memory");

            let copy_offset_int = 65536 - get_type_in_memory_size(ty, true);
            let copy_offset = gen.module.locals.add(walrus::ValType::I32);

            gen.pass_value(builder, value, ty)
                .expect("failed to write instructions for passed value");

            let value_locals = gen.save_to_locals(builder, ty, true);

            builder.i32_const(copy_offset_int).local_set(copy_offset);

            gen.copy_value(builder, ty, &value_locals, copy_offset)
                .expect("couldn't copy the value");

            // We memset the memory before the copied value to 0 to make sure we don't reuse
            // any part of the original value.
            builder
                .i32_const(0)
                .i32_const(0)
                .i32_const(copy_offset_int)
                .memory_fill(memory);

            for l in value_locals {
                builder.local_get(l);
            }
        });

        let res = gen.execute_module(ty);
        assert_eq!(value, &res);
    }

    #[test]
    fn copy_int() {
        // should be a no-op
        let v = Value::Int(42);
        let ty = TypeSignature::type_of(&v).unwrap();
        copy_test(&v, &ty);
    }

    #[test]
    fn copy_buffer() {
        let v = Value::buff_from(vec![1, 2, 3, 4, 5]).unwrap();
        let ty = TypeSignature::type_of(&v).unwrap();
        copy_test(&v, &ty);
    }

    #[test]
    fn copy_principal() {
        let v = PrincipalData::parse("STB44HYPYAT2BB2QE513NSP81HTMYWBJP02HPGK6.foobar")
            .unwrap()
            .into();
        let ty = TypeSignature::type_of(&v).unwrap();
        copy_test(&v, &ty);
    }

    #[test]
    fn copy_string_ascii() {
        let v = Value::string_ascii_from_bytes(b"Hello, World!".to_vec()).unwrap();
        let ty = TypeSignature::type_of(&v).unwrap();
        copy_test(&v, &ty);
    }

    #[test]
    fn copy_string_utf8() {
        let v = Value::string_utf8_from_bytes(
            "Hello, 🌍! 你好, Привет, صباح الخير!"
                .to_owned()
                .into_bytes(),
        )
        .unwrap();
        let ty = TypeSignature::type_of(&v).unwrap();
        copy_test(&v, &ty);
    }

    #[test]
    fn copy_some_string_utf8() {
        let v = Value::some(
            Value::string_utf8_from_bytes(
                "Hello, 🌍! 你好, Привет, صباح الخير!"
                    .to_owned()
                    .into_bytes(),
            )
            .unwrap(),
        )
        .unwrap();
        let ty = TypeSignature::type_of(&v).unwrap();
        copy_test(&v, &ty);
    }

    #[test]
    fn copy_ok_string_utf8() {
        let v = Value::okay(
            Value::string_utf8_from_bytes(
                "Hello, 🌍! 你好, Привет, صباح الخير!"
                    .to_owned()
                    .into_bytes(),
            )
            .unwrap(),
        )
        .unwrap();
        let ty = TypeSignature::new_response(
            TypeSignature::SequenceType(clarity_types::types::SequenceSubtype::StringType(
                clarity_types::types::StringSubtype::UTF8(100u32.try_into().unwrap()),
            )),
            TypeSignature::IntType,
        )
        .unwrap();
        copy_test(&v, &ty);
    }

    #[test]
    fn copy_err_string_utf8() {
        let v = Value::error(
            Value::string_utf8_from_bytes(
                "Hello, 🌍! 你好, Привет, صباح الخير!"
                    .to_owned()
                    .into_bytes(),
            )
            .unwrap(),
        )
        .unwrap();
        let ty = TypeSignature::new_response(
            TypeSignature::IntType,
            TypeSignature::SequenceType(clarity_types::types::SequenceSubtype::StringType(
                clarity_types::types::StringSubtype::UTF8(100u32.try_into().unwrap()),
            )),
        )
        .unwrap();
        copy_test(&v, &ty);
    }

    #[test]
    fn copy_list_int() {
        let v = Value::cons_list_unsanitized((0i128..=5).map(Value::Int).collect()).unwrap();
        let ty = TypeSignature::list_of(TypeSignature::IntType, 100).unwrap();
        copy_test(&v, &ty);
    }

    #[test]
    fn copy_list_buff() {
        let v =
            Value::cons_list_unsanitized((0u8..=125).map(Value::buff_from_byte).collect()).unwrap();
        let ty = TypeSignature::type_of(&v).unwrap();
        copy_test(&v, &ty);
    }

    #[test]
    fn copy_tuple() {
        let v = TupleData::from_data(vec![
            ("uint".into(), Value::UInt(5)),
            ("buff".into(), Value::buff_from(vec![52, 53, 54]).unwrap()),
            (
                "list".into(),
                Value::cons_list_unsanitized((1u8..10u8).map(Value::buff_from_byte).collect())
                    .unwrap(),
            ),
            (
                "tuple".into(),
                TupleData::from_data(vec![
                    ("subint".into(), Value::Int(0)),
                    ("subbool".into(), Value::Bool(true)),
                ])
                .unwrap()
                .into(),
            ),
        ])
        .unwrap()
        .into();
        let ty = TypeSignature::type_of(&v).unwrap();
        copy_test(&v, &ty);
    }
}
