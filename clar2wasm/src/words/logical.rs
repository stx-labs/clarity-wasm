use clarity::vm::types::TypeSignature;
use clarity::vm::ClarityName;

use super::{SimpleWord, Word};
use crate::cost::WordCharge;
use crate::wasm_generator::{GeneratorError, WasmGenerator};

#[derive(Debug)]
pub struct Not;

impl Word for Not {
    fn name(&self) -> ClarityName {
        ClarityName::from_literal("not")
    }
}

impl SimpleWord for Not {
    fn visit(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _arg_types: &[TypeSignature],
        _return_type: &TypeSignature,
    ) -> Result<(), GeneratorError> {
        self.charge(generator, builder, 0)?;
        builder.call(generator.func_by_name("stdlib.not"));
        Ok(())
    }
}
