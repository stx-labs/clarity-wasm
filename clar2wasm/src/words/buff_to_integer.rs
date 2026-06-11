use clarity::vm::types::TypeSignature;
use clarity_types::ClarityName;

use crate::cost::WordCharge;
use crate::wasm_generator::{GeneratorError, WasmGenerator};
use crate::words::{SimpleWord, Word};

fn traverse_buffer_to_integer(
    word: &impl SimpleWord,
    generator: &mut WasmGenerator,
    builder: &mut walrus::InstrSeqBuilder,
) -> Result<(), GeneratorError> {
    word.charge(generator, builder, 0)?;

    let name = word.name();

    let func = generator.func_by_name(&format!("stdlib.{name}"));
    builder.call(func);

    Ok(())
}

#[derive(Debug)]
pub struct BuffToUintBe;

impl Word for BuffToUintBe {
    fn name(&self) -> clarity::vm::ClarityName {
        ClarityName::from_literal("buff-to-uint-be")
    }
}

impl SimpleWord for BuffToUintBe {
    fn visit(
        &self,
        generator: &mut crate::wasm_generator::WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _arg_types: &[TypeSignature],
        _return_type: &TypeSignature,
    ) -> Result<(), crate::wasm_generator::GeneratorError> {
        traverse_buffer_to_integer(self, generator, builder)
    }
}

#[derive(Debug)]
pub struct BuffToIntBe;

impl Word for BuffToIntBe {
    fn name(&self) -> clarity::vm::ClarityName {
        ClarityName::from_literal("buff-to-int-be")
    }
}

impl SimpleWord for BuffToIntBe {
    fn visit(
        &self,
        generator: &mut crate::wasm_generator::WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _arg_types: &[TypeSignature],
        _return_type: &TypeSignature,
    ) -> Result<(), crate::wasm_generator::GeneratorError> {
        // This is the same function as "buff-to-uint-be", with the result interpreted
        // as i128 instead of u128.
        traverse_buffer_to_integer(&BuffToUintBe, generator, builder)
    }
}

#[derive(Debug)]
pub struct BuffToUintLe;

impl Word for BuffToUintLe {
    fn name(&self) -> clarity::vm::ClarityName {
        ClarityName::from_literal("buff-to-uint-le")
    }
}

impl SimpleWord for BuffToUintLe {
    fn visit(
        &self,
        generator: &mut crate::wasm_generator::WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _arg_types: &[TypeSignature],
        _return_type: &TypeSignature,
    ) -> Result<(), crate::wasm_generator::GeneratorError> {
        traverse_buffer_to_integer(self, generator, builder)
    }
}

#[derive(Debug)]
pub struct BuffToIntLe;

impl Word for BuffToIntLe {
    fn name(&self) -> clarity::vm::ClarityName {
        ClarityName::from_literal("buff-to-int-le")
    }
}

impl SimpleWord for BuffToIntLe {
    fn visit(
        &self,
        generator: &mut crate::wasm_generator::WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _arg_types: &[TypeSignature],
        _return_type: &TypeSignature,
    ) -> Result<(), crate::wasm_generator::GeneratorError> {
        // This is the same function as "buff-to-uint-le", with the result interpreted
        // as i128 instead of u128.
        traverse_buffer_to_integer(&BuffToUintLe, generator, builder)
    }
}
