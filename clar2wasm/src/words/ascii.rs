use clarity_types::types::{SequenceSubtype, StringSubtype, TypeSignature};
use walrus::ir::{BinaryOp, ExtendedLoad, LoadKind, MemArg, StoreKind, UnaryOp};
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
            TypeSignature::IntType => to_ascii_int(generator, builder, expr, arg),
            TypeSignature::UIntType => to_ascii_uint(generator, builder, expr, arg),
            TypeSignature::PrincipalType => todo!(),
            TypeSignature::SequenceType(SequenceSubtype::BufferType(_)) => {
                to_ascii_buffer(generator, builder, expr, arg)
            }
            TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(_))) => {
                to_ascii_string_utf8(generator, builder, expr, arg)
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

fn to_ascii_int(
    generator: &mut crate::wasm_generator::WasmGenerator,
    builder: &mut walrus::InstrSeqBuilder,
    _expr: &clarity::vm::SymbolicExpression,
    arg: &clarity::vm::SymbolicExpression,
) -> Result<(), crate::wasm_generator::GeneratorError> {
    let memory = generator.get_memory()?;

    // the biggest uint we could write will have the length of i128::MIN: 40 characters, including the '-'.
    let (offset, _len) = generator.create_call_stack_local(
        builder,
        &TypeSignature::new_ascii_type_checked(40),
        false,
        true,
    );

    let lo = generator.borrow_local(walrus::ValType::I64);
    let hi = generator.borrow_local(walrus::ValType::I64);
    let neg = generator.borrow_local(walrus::ValType::I32);
    let length = generator.borrow_local(walrus::ValType::I32);

    generator.traverse_expr(builder, arg)?;
    builder.local_set(*hi).local_set(*lo);

    // checking if our number is negative. If yes, we convert the int value to its
    // absolute uint value.
    builder
        .local_get(*hi)
        .i64_const(0)
        .binop(BinaryOp::I64LtS)
        .local_tee(*neg)
        .if_else(
            None,
            |then| {
                then.i64_const(0)
                    .local_get(*lo)
                    .binop(BinaryOp::I64Sub)
                    .local_get(*lo)
                    .local_get(*neg)
                    .select(None)
                    .local_set(*lo);

                then.i64_const(0)
                    .local_get(*hi)
                    .local_get(*lo)
                    .i64_const(0)
                    .binop(BinaryOp::I64Ne)
                    .unop(walrus::ir::UnaryOp::I64ExtendUI32)
                    .binop(BinaryOp::I64Add)
                    .binop(BinaryOp::I64Sub)
                    .local_get(*hi)
                    .local_get(*neg)
                    .select(None)
                    .local_set(*hi);
            },
            |_else| {},
        );

    builder
        .local_get(offset)
        .i32_const(40)
        .binop(BinaryOp::I32Add)
        .local_set(offset);
    builder.i32_const(0).local_set(*length);

    to_ascii_u128(generator, builder, *lo, *hi, offset, *length)?;

    // we write a '-' in front of the result if needed
    builder.local_get(*neg).if_else(
        None,
        |then| {
            then.local_get(offset)
                .i32_const(1)
                .binop(BinaryOp::I32Sub)
                .local_tee(offset)
                .i32_const(b'-' as i32)
                .store(
                    memory,
                    StoreKind::I32_8 { atomic: false },
                    MemArg {
                        align: 1,
                        offset: 0,
                    },
                );

            then.local_get(*length)
                .i32_const(1)
                .binop(BinaryOp::I32Add)
                .local_set(*length);
        },
        |_else| {},
    );

    builder
        .i32_const(1)
        .local_get(offset)
        .local_get(*length)
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

    // We make a second loop using the faster i64 division when we have only lo.
    // We always have to enter at least once in this loop, since it should account for
    // the input u0.
    builder.loop_(None, |loop_| {
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

    Ok(())
}

fn to_ascii_buffer(
    generator: &mut crate::wasm_generator::WasmGenerator,
    builder: &mut walrus::InstrSeqBuilder,
    _expr: &clarity::vm::SymbolicExpression,
    arg: &clarity::vm::SymbolicExpression,
) -> Result<(), crate::wasm_generator::GeneratorError> {
    let memory = generator.get_memory()?;

    let arg_size: u32 = match generator.get_expr_type(arg) {
        Some(TypeSignature::SequenceType(SequenceSubtype::BufferType(len))) => len.into(),
        _ => {
            return Err(GeneratorError::TypeError(
                "Wrong type for to-ascii argument with buffer".to_owned(),
            ))
        }
    };
    let (result_offset, _len) = generator.create_call_stack_local(
        builder,
        &TypeSignature::new_ascii_type_checked(2 * arg_size + 2),
        false,
        true,
    );
    let result_length = generator.borrow_local(walrus::ValType::I32);

    let current_offset = generator.borrow_local(walrus::ValType::I32);
    let buff_offset = generator.borrow_local(walrus::ValType::I32);
    let buff_length = generator.borrow_local(walrus::ValType::I32);
    let bytes = generator.borrow_local(walrus::ValType::I32);

    generator.traverse_expr(builder, arg)?;
    builder.local_set(*buff_length).local_set(*buff_offset);

    // write 0x at offset and update the current offset and length
    builder
        .local_get(result_offset)
        .i32_const(u16::from_le_bytes(b"0x".to_owned()) as i32)
        .store(
            memory,
            StoreKind::I32_16 { atomic: false },
            MemArg {
                align: 2,
                offset: 0,
            },
        );
    builder
        .local_get(result_offset)
        .i32_const(2)
        .binop(BinaryOp::I32Add)
        .local_set(*current_offset);
    builder.i32_const(2).local_set(*result_length);

    // if we have a non-empty buffer, we start looping through the bytes.
    builder.local_get(*buff_length).if_else(
        None,
        |then| {
            then.loop_(None, |loop_| {
                let tmp = generator.borrow_local(walrus::ValType::I32);
                let loop_id = loop_.id();

                // get the storage offset and push it on the stack
                loop_.local_get(*current_offset);

                loop_
                    .local_get(*buff_offset)
                    .load(
                        memory,
                        walrus::ir::LoadKind::I32_8 {
                            kind: ExtendedLoad::ZeroExtend,
                        },
                        MemArg {
                            align: 1,
                            offset: 0,
                        },
                    )
                    .local_set(*bytes);

                // convert lo 4 bytes to hex
                loop_
                    .i32_const(b'0' as i32)
                    .i32_const(b'a' as i32 - 10)
                    .local_get(*bytes)
                    .i32_const(0xf)
                    .binop(BinaryOp::I32And)
                    .local_tee(*tmp)
                    .i32_const(10)
                    .binop(BinaryOp::I32LtU)
                    .select(None)
                    .local_get(*tmp)
                    .binop(BinaryOp::I32Add)
                    .i32_const(8)
                    .binop(BinaryOp::I32Shl);

                // convert hi 4 bytes to hex
                loop_
                    .i32_const(b'0' as i32)
                    .i32_const(b'a' as i32 - 10)
                    .local_get(*bytes)
                    .i32_const(4)
                    .binop(BinaryOp::I32ShrU)
                    .local_tee(*tmp)
                    .i32_const(10)
                    .binop(BinaryOp::I32LtU)
                    .select(None)
                    .local_get(*tmp)
                    .binop(BinaryOp::I32Add);

                // concat both and store them (offset was already on the stack)
                loop_.binop(BinaryOp::I32Or).store(
                    memory,
                    StoreKind::I32_16 { atomic: false },
                    MemArg {
                        align: 2,
                        offset: 0,
                    },
                );

                // update the offsets and lengths and loop if needed
                loop_
                    .local_get(*current_offset)
                    .i32_const(2)
                    .binop(BinaryOp::I32Add)
                    .local_set(*current_offset);

                loop_
                    .local_get(*result_length)
                    .i32_const(2)
                    .binop(BinaryOp::I32Add)
                    .local_set(*result_length);

                loop_
                    .local_get(*buff_offset)
                    .i32_const(1)
                    .binop(BinaryOp::I32Add)
                    .local_set(*buff_offset);

                loop_
                    .local_get(*buff_length)
                    .i32_const(1)
                    .binop(BinaryOp::I32Sub)
                    .local_tee(*buff_length)
                    .br_if(loop_id);
            });
        },
        |_else| {},
    );

    // The result is always ok - offset - length - 0
    builder
        .i32_const(1)
        .local_get(result_offset)
        .local_get(*result_length)
        .i64_const(0)
        .i64_const(0);

    Ok(())
}

fn to_ascii_string_utf8(
    generator: &mut crate::wasm_generator::WasmGenerator,
    builder: &mut walrus::InstrSeqBuilder,
    _expr: &clarity::vm::SymbolicExpression,
    arg: &clarity::vm::SymbolicExpression,
) -> Result<(), crate::wasm_generator::GeneratorError> {
    let memory = generator.get_memory()?;
    let arg_size: u32 = match generator.get_expr_type(arg) {
        Some(TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(
            len,
        )))) => len.into(),
        _ => {
            return Err(GeneratorError::TypeError(
                "Wrong type for to-ascii argument with string-utf8".to_owned(),
            ))
        }
    };
    let (result_offset, _len) = generator.create_call_stack_local(
        builder,
        &TypeSignature::new_ascii_type_checked(arg_size),
        false,
        true,
    );
    let result_length = generator.borrow_local(walrus::ValType::I32);

    let current_offset = generator.borrow_local(walrus::ValType::I32);
    let utf8_offset = generator.borrow_local(walrus::ValType::I32);
    let utf8_length = generator.borrow_local(walrus::ValType::I32);

    generator.traverse_expr(builder, arg)?;
    builder.local_set(*utf8_length).local_set(*utf8_offset);

    builder.block(None, |block| {
        let block_id = block.id();

        // skip if we have an empty string
        block
            .local_get(*utf8_length)
            .unop(UnaryOp::I32Eqz)
            .br_if(block_id);

        block.local_get(result_offset).local_set(*current_offset);
        block.i32_const(0).local_set(*result_length);

        block.loop_(None, |loop_| {
            let loop_id = loop_.id();
            let unicode = generator.borrow_local(walrus::ValType::I32);

            loop_
                .local_get(*utf8_offset)
                .load(
                    memory,
                    LoadKind::I32 { atomic: false },
                    MemArg {
                        align: 4,
                        offset: 0,
                    },
                )
                .local_tee(*unicode);

            // we break the loop if the character is not ascii
            loop_
                .i32_const(!127u32.to_be() as i32)
                .binop(BinaryOp::I32And)
                .br_if(block_id);

            // otherwise we store the last byte
            // CAUTION: for now, string-utf8 are still stored in big-endian order!!!
            loop_
                .local_get(*current_offset)
                .local_get(*unicode)
                .i32_const(3 * 8)
                .binop(BinaryOp::I32ShrU)
                .store(
                    memory,
                    StoreKind::I32_8 { atomic: false },
                    MemArg {
                        align: 1,
                        offset: 0,
                    },
                );

            // now we update the locals and loop if we still have characters to process
            loop_
                .local_get(*current_offset)
                .i32_const(1)
                .binop(BinaryOp::I32Add)
                .local_set(*current_offset);
            loop_
                .local_get(*result_length)
                .i32_const(1)
                .binop(BinaryOp::I32Add)
                .local_set(*result_length);
            loop_
                .local_get(*utf8_offset)
                .i32_const(4)
                .binop(BinaryOp::I32Add)
                .local_set(*utf8_offset);
            loop_
                .local_get(*utf8_length)
                .i32_const(4)
                .binop(BinaryOp::I32Sub)
                .local_tee(*utf8_length)
                .br_if(loop_id);
        });
    });

    // answer is:
    //   ok if all chars are processed
    builder.local_get(*utf8_length).unop(UnaryOp::I32Eqz);
    //   offset - length
    builder.local_get(result_offset).local_get(*result_length);
    //   1 if all chars weren't processed
    builder.i64_const(1).i64_const(0);

    Ok(())
}

#[cfg(test)]
#[cfg(not(any(
    feature = "test-clarity-v1",
    feature = "test-clarity-v2",
    feature = "test-clarity-v3"
)))]
mod tests {
    use clarity_types::types::{BuffData, ResponseData};
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
                    Value::okay(Value::string_ascii_from_bytes(i.into_bytes()).unwrap()).unwrap(),
                )),
            )
        };

        check(0);
        check(1);
        check(u64::MAX as u128);
        check(u64::MAX as u128 + 1);
        check(u128::MAX);
    }

    #[test]
    fn to_ascii_int() {
        let check = |i: i128| {
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
        check(i64::MAX as i128);
        check(i64::MAX as i128 + 1);
        check(i128::MAX);
        check(-1);
        check(i64::MIN as i128);
        check(i64::MIN as i128 - 1);
        check(i128::MIN);
    }

    #[test]
    fn to_ascii_buffer() {
        let check = |buff: &[u8]| {
            let buff_data = BuffData {
                data: buff.to_owned(),
            };
            crosscheck(
                &format!("(to-ascii? 0x{buff_data})",),
                Ok(Some(
                    Value::okay(
                        Value::string_ascii_from_bytes(format!("0x{buff_data}").into_bytes())
                            .unwrap(),
                    )
                    .unwrap(),
                )),
            );
        };

        check(&[]);
        check(&[1]);
        check(&[1, 2]);
        check(&[1, 2, 3, 4]);
        check(&[255, 125, 84, 64, 37, 1]);
    }

    #[test]
    fn to_ascii_string_utf8() {
        let check = |s: &str| {
            let snippet = format!(r#"(to-ascii? u"{s}")"#);
            let expected =
                Value::okay(Value::string_ascii_from_bytes(s.to_string().into_bytes()).unwrap())
                    .unwrap();
            crosscheck(&snippet, Ok(Some(expected)));
        };

        check("");
        check("a");
        check("abc");
        check("AbCDe1234");

        crosscheck(r#"(to-ascii? u"\u{1f601}")"#, Ok(Some(Value::err_uint(1))));
        crosscheck(r#"(to-ascii? u"a\u{1f601}")"#, Ok(Some(Value::err_uint(1))));
        crosscheck(
            r#"(to-ascii? u"a\u{1f601}bcd")"#,
            Ok(Some(Value::err_uint(1))),
        );
    }
}
