use clarity_types::types::{SequenceSubtype, StringSubtype, TypeSignature};
use walrus::ir::{BinaryOp, MemArg, StoreKind, UnaryOp};
use walrus::LocalId;

use crate::check_args;
use crate::wasm_generator::GeneratorError;
use crate::wasm_utils::ArgumentCountCheck;
use crate::words::{ComplexWord, Word};

#[derive(Debug)]
pub struct ToAscii;

impl Word for ToAscii {
    fn name(&self) -> clarity_types::ClarityName {
        "to-ascii?".into()
    }
}

impl ComplexWord for ToAscii {
    fn traverse(
        &self,
        generator: &mut crate::wasm_generator::WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        expr: &clarity::vm::SymbolicExpression,
        args: &[clarity::vm::SymbolicExpression],
    ) -> Result<(), crate::wasm_generator::GeneratorError> {
        check_args!(generator, builder, 1, args.len(), ArgumentCountCheck::Exact);

        let [arg] = args else {
            // the check above makes sure we have exactly one argument.
            unreachable!()
        };
        let arg_ty = generator.get_expr_type(arg).ok_or_else(|| {
            GeneratorError::TypeError("to-ascii? 's argument should be typed".to_owned())
        })?;

        match arg_ty {
            TypeSignature::BoolType => to_ascii_bool(generator, builder, expr, arg),
            TypeSignature::IntType => todo!(),
            TypeSignature::UIntType => to_ascii_uint(generator, builder, expr, arg),
            TypeSignature::PrincipalType => todo!(),
            TypeSignature::SequenceType(SequenceSubtype::BufferType(_)) => todo!(),
            TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(_))) => {
                todo!()
            }
            _ => Err(GeneratorError::TypeError(format!(
                "to-ascii? 's argument shouldn't be of type {arg_ty}"
            ))),
        }
    }
}

fn to_ascii_bool(
    generator: &mut crate::wasm_generator::WasmGenerator,
    builder: &mut walrus::InstrSeqBuilder,
    _expr: &clarity::vm::SymbolicExpression,
    arg: &clarity::vm::SymbolicExpression,
) -> Result<(), crate::wasm_generator::GeneratorError> {
    // we should allocate a string of size 5 in memory for either the strings "true" or "false"
    // however, we will use 8 bytes so that we can write u64 values directly to memory.
    let (offset, _len) = generator.create_call_stack_local(
        builder,
        &TypeSignature::new_ascii_type_checked(8),
        false,
        true,
    );

    // we traverse and the argument and store the boolean result in a local
    let res = generator.borrow_local(walrus::ValType::I32);
    generator.traverse_expr(builder, arg)?;
    builder.local_set(*res);

    // we need to add the offset where to write the result on the stack
    builder.local_get(offset);

    // we push the "true" or "false" string on the stack
    builder
        .i64_const(i64::from_le_bytes(b"true\0\0\0\0".to_owned()))
        .i64_const(i64::from_le_bytes(b"false\0\0\0".to_owned()))
        .local_get(*res)
        .select(None);

    builder.store(
        generator.get_memory()?,
        walrus::ir::StoreKind::I64 { atomic: false },
        MemArg {
            align: 8,
            offset: 0,
        },
    );

    builder
        // it's always "ok" for a bool argument
        .i32_const(1)
        .local_get(offset)
        // the size is either 4 for true or 5 for false
        .i32_const(5)
        .local_get(*res)
        .binop(BinaryOp::I32Sub)
        // the err value is irrelevant for a bool argument
        .i64_const(0)
        .i64_const(0);

    Ok(())
}

fn to_ascii_uint(
    generator: &mut crate::wasm_generator::WasmGenerator,
    builder: &mut walrus::InstrSeqBuilder,
    _expr: &clarity::vm::SymbolicExpression,
    arg: &clarity::vm::SymbolicExpression,
) -> Result<(), crate::wasm_generator::GeneratorError> {
    // the biggest uint we could write will have the length of u128::MAX: 39 characters.
    // We also need a space for the character 'u'
    let (offset, _len) = generator.create_call_stack_local(
        builder,
        &TypeSignature::new_ascii_type_checked(40),
        false,
        true,
    );

    let lo = generator.borrow_local(walrus::ValType::I64);
    let hi = generator.borrow_local(walrus::ValType::I64);
    let length = generator.borrow_local(walrus::ValType::I32);

    generator.traverse_expr(builder, arg)?;
    builder.local_set(*hi).local_set(*lo);

    builder
        .local_get(offset)
        .i32_const(40)
        .binop(BinaryOp::I32Add)
        .local_set(offset);
    builder.i32_const(0).local_set(*length);

    to_ascii_u128(generator, builder, *lo, *hi, offset, *length)?;

    // we write a 'u' in front of the result
    builder
        .local_get(offset)
        .i32_const(1)
        .binop(BinaryOp::I32Sub)
        .local_tee(offset)
        .i32_const(b'u' as i32)
        .store(
            generator.get_memory()?,
            StoreKind::I32_8 { atomic: false },
            MemArg {
                align: 1,
                offset: 0,
            },
        );

    builder
        .i32_const(1)
        .local_get(offset)
        // length + 1 for the character 'u'
        .local_get(*length)
        .i32_const(1)
        .binop(BinaryOp::I32Add)
        .i64_const(0)
        .i64_const(0);

    Ok(())
}

fn to_ascii_u128(
    generator: &mut crate::wasm_generator::WasmGenerator,
    builder: &mut walrus::InstrSeqBuilder,
    lo: LocalId,
    hi: LocalId,
    offset: LocalId,
    length: LocalId,
) -> Result<(), crate::wasm_generator::GeneratorError> {
    let memory = generator.get_memory()?;
    // we make a first loop with the u128 division while hi > 0
    builder
        .local_get(hi)
        .i64_const(0)
        .binop(BinaryOp::I64Ne)
        .if_else(
            None,
            |then| {
                then.loop_(None, |loop_| {
                    let loop_id = loop_.id();
                    let div_128 = generator.func_by_name("stdlib.div-int128");

                    // we update the offset at which the character should be written
                    loop_
                        .local_get(offset)
                        .i32_const(1)
                        .binop(BinaryOp::I32Sub)
                        .local_set(offset);

                    loop_
                        .local_get(lo)
                        .local_get(hi)
                        .i64_const(10)
                        .i64_const(0)
                        .call(div_128);
                    // drop the remainder hi
                    loop_.drop();
                    // we set the remainder_lo in lo converted to its ascii value
                    loop_.i64_const(48).binop(BinaryOp::I64Add).local_set(lo);
                    // we store it to the correct offset
                    loop_.local_get(offset).local_get(lo).store(
                        memory,
                        StoreKind::I64_8 { atomic: false },
                        MemArg {
                            align: 1,
                            offset: 0,
                        },
                    );

                    // we store the new hi and lo from the stack
                    loop_.local_set(hi).local_set(lo);

                    // we update the result size
                    loop_
                        .local_get(length)
                        .i32_const(1)
                        .binop(BinaryOp::I32Add)
                        .local_set(length);

                    // we keep going through the slow loop while hi is > 0
                    loop_
                        .local_get(hi)
                        .i64_const(0)
                        .binop(BinaryOp::I64Ne)
                        .br_if(loop_id);
                });
            },
            |_else| {},
        );

    // we make a second loop using the faster i64 division when we have only lo
    builder
        .local_get(lo)
        .i64_const(0)
        .binop(BinaryOp::I64Ne)
        .if_else(
            None,
            |then| {
                then.loop_(None, |loop_| {
                    let loop_id = loop_.id();

                    // we update the offset at which the character should be written
                    loop_
                        .local_get(offset)
                        .i32_const(1)
                        .binop(BinaryOp::I32Sub)
                        .local_tee(offset);

                    // we compute (lo % 10) on the stack and set (lo % 10) using the formula
                    // divmod(lo, 10) => { div = lo / 10 ; mod = (div * -10) + lo }
                    loop_
                        .local_get(lo)
                        .local_get(lo)
                        .i64_const(10)
                        .binop(BinaryOp::I64DivU)
                        .local_tee(lo)
                        .i64_const(-10)
                        .binop(BinaryOp::I64Mul)
                        .binop(BinaryOp::I64Add);

                    // we convert the value on stack to its ascii value
                    loop_.i64_const(48).binop(BinaryOp::I64Add);

                    // we store the value (offset already on stack)
                    loop_.store(
                        memory,
                        StoreKind::I64_8 { atomic: false },
                        MemArg {
                            align: 1,
                            offset: 0,
                        },
                    );

                    // we update the result size
                    loop_
                        .local_get(length)
                        .i32_const(1)
                        .binop(BinaryOp::I32Add)
                        .local_set(length);

                    // we keep going through the slow loop while lo is > 0
                    loop_
                        .local_get(lo)
                        .i64_const(0)
                        .binop(BinaryOp::I64Ne)
                        .br_if(loop_id);
                });
            },
            |_else| {},
        );

    // we need to account for the printing of 0. We have 0 if we didn't enter any of the previous loops,
    // which implies that the current value of length is also 0.
    builder.local_get(length).unop(UnaryOp::I32Eqz).if_else(
        None,
        |then| {
            then
                // offset
                .local_get(offset)
                .i32_const(1)
                .local_tee(length)
                .binop(BinaryOp::I32Sub)
                .local_tee(offset)
                // value '0'
                .i32_const(b'0' as i32)
                .store(
                    memory,
                    StoreKind::I32_8 { atomic: false },
                    MemArg {
                        align: 1,
                        offset: 0,
                    },
                );
        },
        |_else| {},
    );

    Ok(())
}

#[cfg(test)]
#[cfg(not(any(
    feature = "test-clarity-v1",
    feature = "test-clarity-v2",
    feature = "test-clarity-v3"
)))]
mod tests {
    use clarity_types::types::ResponseData;
    use clarity_types::Value;

    use crate::tools::crosscheck;

    #[test]
    fn to_ascii_bool() {
        crosscheck(
            "(to-ascii? true)",
            Ok(Some(Value::Response(ResponseData {
                committed: true,
                data: Box::new(Value::string_ascii_from_bytes(b"true".to_vec()).unwrap()),
            }))),
        );

        crosscheck(
            "(to-ascii? false)",
            Ok(Some(Value::Response(ResponseData {
                committed: true,
                data: Box::new(Value::string_ascii_from_bytes(b"false".to_vec()).unwrap()),
            }))),
        );
    }

    #[test]
    fn to_ascii_uint() {
        let check = |i: u128| {
            let i = format!("u{i}");
            crosscheck(
                &format!("(to-ascii? {i})"),
                Ok(Some(
                    Value::okay(
                        Value::string_ascii_from_bytes(i.to_string().into_bytes()).unwrap(),
                    )
                    .unwrap(),
                )),
            )
        };

        check(0);
        check(1);
        check(u64::MAX as u128);
        check(u64::MAX as u128 + 1);
        check(u128::MAX);
    }
}
