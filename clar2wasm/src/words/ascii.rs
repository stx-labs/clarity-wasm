use clarity_types::types::{SequenceSubtype, StringSubtype, TypeSignature};

use crate::{
    check_args,
    wasm_generator::GeneratorError,
    wasm_utils::ArgumentCountCheck,
    words::{ComplexWord, Word},
};

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
        _expr: &clarity::vm::SymbolicExpression,
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
            TypeSignature::BoolType => todo!(),
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
