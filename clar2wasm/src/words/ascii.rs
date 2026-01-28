use crate::{
    check_args,
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
        Ok(())
    }
}
