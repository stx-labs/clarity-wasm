use clarity::vm::types::TypeSignature;
use clarity::vm::ClarityName;
use walrus::InstrSeqBuilder;

use super::{SimpleWord, Word};
use crate::cost::WordCharge;
use crate::wasm_generator::{GeneratorError, WasmGenerator};

#[derive(Debug)]
pub struct BitwiseNot;

impl Word for BitwiseNot {
    fn name(&self) -> ClarityName {
        "bit-not".into()
    }
}

impl SimpleWord for BitwiseNot {
    fn visit(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _arg_types: &[TypeSignature],
        _return_type: &TypeSignature,
    ) -> Result<(), GeneratorError> {
        self.charge(generator, builder, 0)?;

        let helper_func = generator.func_by_name("stdlib.bit-not");
        builder.call(helper_func);
        Ok(())
    }
}

// multi value bit-operations

fn traverse_bitwise(
    word: &impl SimpleWord,
    generator: &mut WasmGenerator,
    builder: &mut InstrSeqBuilder,
    arg_types: &[TypeSignature],
) -> Result<(), GeneratorError> {
    println!("arg_types.len: {}", arg_types.len());
    word.charge(generator, builder, arg_types.len() as u32)?;

    let name = word.name();

    let helper_func = generator.func_by_name(&format!("stdlib.{name}"));
    // Run this once for every arg except first
    for _ in arg_types.iter().skip(1) {
        builder.call(helper_func);
    }
    Ok(())
}

#[derive(Debug)]
pub struct BitwiseOr;

impl Word for BitwiseOr {
    fn name(&self) -> ClarityName {
        "bit-or".into()
    }
}

impl SimpleWord for BitwiseOr {
    fn visit(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        arg_types: &[TypeSignature],
        _return_type: &TypeSignature,
    ) -> Result<(), GeneratorError> {
        traverse_bitwise(self, generator, builder, arg_types)
    }
}

#[derive(Debug)]
pub struct BitwiseAnd;

impl Word for BitwiseAnd {
    fn name(&self) -> ClarityName {
        "bit-and".into()
    }
}

impl SimpleWord for BitwiseAnd {
    fn visit(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        arg_types: &[TypeSignature],
        _return_type: &TypeSignature,
    ) -> Result<(), GeneratorError> {
        traverse_bitwise(self, generator, builder, arg_types)
    }
}

#[derive(Debug)]
pub struct BitwiseXor;

impl Word for BitwiseXor {
    fn name(&self) -> ClarityName {
        "bit-xor".into()
    }
}

impl SimpleWord for BitwiseXor {
    fn visit(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        arg_types: &[TypeSignature],
        _return_type: &TypeSignature,
    ) -> Result<(), GeneratorError> {
        traverse_bitwise(self, generator, builder, arg_types)
    }
}

#[derive(Debug)]
pub struct BitwiseLShift;

impl Word for BitwiseLShift {
    fn name(&self) -> ClarityName {
        "bit-shift-left".into()
    }
}

impl SimpleWord for BitwiseLShift {
    fn visit(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _arg_types: &[TypeSignature],
        _return_type: &TypeSignature,
    ) -> Result<(), GeneratorError> {
        self.charge(generator, builder, 0)?;

        let func = generator.func_by_name("stdlib.bit-shift-left");
        builder.call(func);
        Ok(())
    }
}

#[derive(Debug)]
pub struct BitwiseRShift;

impl Word for BitwiseRShift {
    fn name(&self) -> ClarityName {
        "bit-shift-right".into()
    }
}

impl SimpleWord for BitwiseRShift {
    fn visit(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        arg_types: &[TypeSignature],
        _return_type: &TypeSignature,
    ) -> Result<(), GeneratorError> {
        self.charge(generator, builder, 0)?;

        let type_suffix = match arg_types[0] {
            TypeSignature::IntType => "int",
            TypeSignature::UIntType => "uint",
            _ => {
                return Err(GeneratorError::TypeError(
                    "invalid type for shift".to_string(),
                ));
            }
        };

        let helper = generator.func_by_name(&format!("stdlib.bit-shift-right-{type_suffix}"));

        builder.call(helper);

        Ok(())
    }
}

#[derive(Debug)]
pub struct Xor;

impl Word for Xor {
    fn name(&self) -> ClarityName {
        "xor".into()
    }
}

impl SimpleWord for Xor {
    fn visit(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        arg_types: &[TypeSignature],
        _return_type: &TypeSignature,
    ) -> Result<(), GeneratorError> {
        // xor is a proxy call to bit-xor since they share the same implementation.
        traverse_bitwise(&BitwiseXor, generator, builder, arg_types)
    }
}

#[cfg(not(feature = "test-clarity-v1"))]
#[cfg(test)]
mod tests {
    #[cfg(test)]
    mod clarity_v2_v3 {
        use crate::tools::{crosscheck, evaluate};

        #[test]
        fn test_bitwise_and() {
            crosscheck(
                "
(define-public (assert)
  (ok (bit-and 3 3)))

(assert)",
                evaluate("(ok 3)"),
            )
        }

        #[test]
        fn test_bitwise_not() {
            crosscheck(
                "
(define-public (assert)
  (ok (bit-not 3)))

(assert)",
                evaluate("(ok -4)"),
            )
        }

        #[test]
        fn test_bitwise_or() {
            crosscheck(
                "
(define-public (assert)
  (ok (bit-or 1 2 3)))

(assert)",
                evaluate("(ok 3)"),
            )
        }

        #[test]
        fn test_bit_shift_left() {
            crosscheck(
                "
(define-public (assert)
  (ok (bit-shift-left 3 u1)))

(assert)",
                evaluate("(ok 6)"),
            )
        }

        #[test]
        fn test_bit_shift_right() {
            crosscheck(
                "
(define-public (assert)
  (ok (bit-shift-right 6 u1)))

(assert)",
                evaluate("(ok 3)"),
            )
        }

        #[test]
        fn test_bitwise_xor() {
            crosscheck(
                "
(define-public (assert)
  (ok (bit-xor 3 2)))

(assert)",
                evaluate("(ok 1)"),
            )
        }
    }
}
