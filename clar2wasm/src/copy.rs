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
mod tests {}
