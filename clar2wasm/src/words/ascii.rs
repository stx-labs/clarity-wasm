use clarity_types::types::{SequenceSubtype, StringSubtype, TypeSignature};
use walrus::ir::MemArg;

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
        let arg_ty = generator
            .get_expr_type(arg)
            .ok_or_else(|| {
                GeneratorError::TypeError("to-ascii? 's argument should be typed".to_owned())
            })?
            .clone();

        match arg_ty {
            TypeSignature::BoolType => to_ascii_bool(generator, builder, expr, arg)?,
            TypeSignature::IntType => todo!(),
            TypeSignature::UIntType => todo!(),
            TypeSignature::PrincipalType => todo!(),
            TypeSignature::SequenceType(SequenceSubtype::BufferType(_)) => todo!(),
            TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(_))) => {
                todo!()
            }
            _ => {
                return Err(GeneratorError::TypeError(format!(
                    "to-ascii? 's argument shouldn't be of type {arg_ty}"
                )))
            }
        }

        Ok(())
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
        .binop(walrus::ir::BinaryOp::I32Sub)
        // the err value is irrelevant for a bool argument
        .i64_const(0)
        .i64_const(0);

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
}
