use clarity::vm::types::{BufferLength, SequenceSubtype, TypeSignature};
use clarity::vm::ClarityName;
use walrus::ValType;

use super::{SimpleWord, Word};
use crate::cost::WordCharge;
use crate::wasm_generator::{GeneratorError, WasmGenerator};

pub fn traverse_hash(
    word: &impl SimpleWord,
    generator: &mut WasmGenerator,
    builder: &mut walrus::InstrSeqBuilder,
    arg_types: &[TypeSignature],
    work_space: u32, // constant upper bound
) -> Result<(), GeneratorError> {
    let name = word.name();

    // Buffer type for the result based on the hash function
    let buffer_size = match name.as_str() {
        "hash160" => 20,
        "sha512" => 64,
        _ => 32, // sha256
    };
    let return_ty = TypeSignature::SequenceType(SequenceSubtype::BufferType(
        BufferLength::try_from(buffer_size as usize)
            .map_err(|_| GeneratorError::InternalError("buffer size too large".to_string()))?,
    ));

    // Allocate space on the stack for the result
    let (result_local, _) = generator.create_call_stack_local(builder, &return_ty, false, true);

    let hash_type = match &arg_types[0] {
        TypeSignature::IntType | TypeSignature::UIntType => {
            // an integer is 16 bytes
            word.charge(generator, builder, 16)?;

            generator.ensure_work_space(work_space);
            "int"
        }
        TypeSignature::SequenceType(SequenceSubtype::BufferType(len)) => {
            // for cost tracking we need the length of the input to the hash,
            // so we load it onto a new local
            let buf_len = generator.module.locals.add(ValType::I32);
            builder.local_tee(buf_len);
            word.charge(generator, builder, buf_len)?;

            // Input buff is also copied
            generator.ensure_work_space(u32::from(len) + work_space);
            "buf"
        }
        _ => {
            return Err(GeneratorError::NotImplemented);
        }
    };

    let hash_func = generator
        .module
        .funcs
        .by_name(&format!("stdlib.{name}-{hash_type}"))
        .ok_or_else(|| {
            GeneratorError::InternalError(format!("function not found: {name}-{hash_type}"))
        })?;

    builder.local_get(result_local).call(hash_func);

    Ok(())
}

#[derive(Debug)]
pub struct Hash160;

impl Word for Hash160 {
    fn name(&self) -> ClarityName {
        "hash160".into()
    }
}

impl SimpleWord for Hash160 {
    fn visit(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        arg_types: &[TypeSignature],
        _return_type: &TypeSignature,
    ) -> Result<(), GeneratorError> {
        // work_space values from sha256, see `Sha256::visit`
        traverse_hash(self, generator, builder, arg_types, 64 + 8 + 289)
    }
}

#[derive(Debug)]
pub struct Sha256;

impl Word for Sha256 {
    fn name(&self) -> ClarityName {
        "sha256".into()
    }
}

impl SimpleWord for Sha256 {
    fn visit(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        arg_types: &[TypeSignature],
        _return_type: &TypeSignature,
    ) -> Result<(), GeneratorError> {
        // work_space values from `standard.wat::$extend-data`: 64 for padding, 8 for padded size and 289 for the data shift
        traverse_hash(self, generator, builder, arg_types, 64 + 8 + 289)
    }
}

#[derive(Debug)]
pub struct Keccak256;

impl Word for Keccak256 {
    fn name(&self) -> ClarityName {
        "keccak256".into()
    }
}

impl SimpleWord for Keccak256 {
    fn visit(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        arg_types: &[TypeSignature],
        _return_type: &TypeSignature,
    ) -> Result<(), GeneratorError> {
        let ty = &arg_types[0];
        match ty {
            TypeSignature::IntType | TypeSignature::UIntType => {
                // Convert integers to buffers by storing them to memory
                let (buffer_local, size) =
                    generator.create_call_stack_local(builder, ty, false, true);
                generator.write_to_memory(builder, buffer_local, 0, ty)?;

                // Then load the offset and length onto the stack
                builder.local_get(buffer_local).i32_const(size);
            }
            TypeSignature::SequenceType(SequenceSubtype::BufferType(_)) => {}
            _ => {
                return Err(GeneratorError::TypeError(
                    "invalid type for keccak256".to_string(),
                ))
            }
        }

        // for cost tracking we need the length of the input to the hash,
        // so we load it onto a new local
        let buf_len = generator.module.locals.add(ValType::I32);
        builder.local_tee(buf_len);
        self.charge(generator, builder, buf_len)?;

        // Reserve stack space for the host-function to write the result
        let ret_ty = TypeSignature::BUFFER_32.clone();
        let (result_local, result_size) =
            generator.create_call_stack_local(builder, &ret_ty, false, true);
        builder.local_get(result_local).i32_const(result_size);

        // Call the host interface function, `keccak256`
        builder.call(
            generator
                .module
                .funcs
                .by_name("stdlib.keccak256")
                .ok_or_else(|| {
                    GeneratorError::InternalError("stdlib.keccak256 not found".to_owned())
                })?,
        );

        Ok(())
    }
}

#[derive(Debug)]
pub struct Sha512;

impl Word for Sha512 {
    fn name(&self) -> ClarityName {
        "sha512".into()
    }
}

impl SimpleWord for Sha512 {
    fn visit(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        arg_types: &[TypeSignature],
        _return_type: &TypeSignature,
    ) -> Result<(), GeneratorError> {
        // work_space values from `standard.wat::$pad-sha512-data`: 128 for padding, 16 for padded size and 705 for the data shift
        traverse_hash(self, generator, builder, arg_types, 128 + 16 + 705)
    }
}

#[derive(Debug)]
pub struct Sha512_256;

impl Word for Sha512_256 {
    fn name(&self) -> ClarityName {
        "sha512/256".into()
    }
}

impl SimpleWord for Sha512_256 {
    fn visit(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        arg_types: &[TypeSignature],
        _return_type: &TypeSignature,
    ) -> Result<(), GeneratorError> {
        let ty = &arg_types[0];
        match ty {
            TypeSignature::IntType | TypeSignature::UIntType => {
                // Convert integers to buffers by storing them to memory
                let (buffer_local, size) =
                    generator.create_call_stack_local(builder, ty, false, true);
                generator.write_to_memory(builder, buffer_local, 0, ty)?;

                // Then load the offset and length onto the stack
                builder.local_get(buffer_local).i32_const(size);
            }
            TypeSignature::SequenceType(SequenceSubtype::BufferType(_)) => {}
            _ => {
                return Err(GeneratorError::TypeError(
                    "invalid type for sha512/256".to_string(),
                ))
            }
        }

        // for cost tracking we need the length of the input to the hash,
        // so we load it onto a new local
        let buf_len = generator.module.locals.add(ValType::I32);
        builder.local_tee(buf_len);
        self.charge(generator, builder, buf_len)?;

        // Reserve stack space for the host-function to write the result
        let ret_ty = TypeSignature::BUFFER_32.clone();
        let (result_local, result_size) =
            generator.create_call_stack_local(builder, &ret_ty, false, true);
        builder.local_get(result_local).i32_const(result_size);

        // Call the host interface function, `sha512_256`
        builder.call(
            generator
                .module
                .funcs
                .by_name("stdlib.sha512_256")
                .ok_or_else(|| {
                    GeneratorError::InternalError("stdlib.sha512_256 not found".to_owned())
                })?,
        );

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use clarity::vm::Value;

    use crate::tools::{crosscheck, interpret};

    #[test]
    fn map_hash160() {
        crosscheck(
            "(map hash160 (list 1 2 3))",
            interpret("(list 0x7c2d0e4bb1fdd9b98784c04a255e5991bcefb47f 0x3e3dfec3717972aad4735db5e32507a82ad66783 0xb2c1ebcf775ebf585f4dd70e9f2e6cd6a1dc02bf)"),
        );
    }

    #[test]
    fn map_sha256() {
        crosscheck(
            "(map sha256 (list 1 2 3))",
            interpret("(list 0x4cbbd8ca5215b8d161aec181a74b694f4e24b001d5b081dc0030ed797a8973e0 0xb1535c7783ea8829b6b0cf67704539798b4d16c39bf0bfe09494c5d9f12eee30 0x59d5966c96af7ecad5c9d2918d6582d102b2c67f6b765ea28ac24371ab4f93be)"),
        );
    }

    #[test]
    fn map_sha512() {
        crosscheck(
            "(map sha512 (list 1 2 3))",
            interpret("(list 0x6fcee9a7b7a7b821d241c03c82377928bc6882e7a08c78a4221199bfa220cdc55212273018ee613317c8293bb8d1ce08d1e017508e94e06ab85a734c99c7cc34 0x6e4821d2319c9b43fd8eaf4a79007d04572aa61f1de7c7161b569cf1e80a36b3ed33949c54fe9ff7d82b4a5aa570e1f57f266b70405ec09daf868ba8b6b09695 0x65a88e32b391d61b95c8c1d77067439edc52e54502e6fe5549b73b6609a89c77a629b7f4db5b34a590d3b36e32ad4c143180197185f9bc83a23a39f863e446e8)"),
        );
    }

    #[test]
    fn test_keccak256() {
        let mut expected = [0u8; 32];
        hex::decode_to_slice(
            "f490de2920c8a35fabeb13208852aa28c76f9be9b03a4dd2b3c075f7a26923b4",
            &mut expected,
        )
        .unwrap();
        crosscheck(
            "(keccak256 0)",
            Ok(Some(Value::buff_from(expected.to_vec()).unwrap())),
        )
    }

    #[test]
    fn test_sha512() {
        let mut expected = [0u8; 64];
        hex::decode_to_slice(
            "6fcee9a7b7a7b821d241c03c82377928bc6882e7a08c78a4221199bfa220cdc55212273018ee613317c8293bb8d1ce08d1e017508e94e06ab85a734c99c7cc34",
            &mut expected,
        )
        .unwrap();
        crosscheck(
            "(sha512 1)",
            Ok(Some(Value::buff_from(expected.to_vec()).unwrap())),
        );
    }

    #[test]
    fn test_sha512_overwrite() {
        let expected = [0u8; 64];
        crosscheck(
            "(sha512 1)
0x00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
            Ok(Some(Value::buff_from(expected.to_vec()).unwrap())),
        );
    }

    #[test]
    fn test_sha512_256_overwrite() {
        let expected = [0u8; 32];
        crosscheck(
            "(sha512/256 1)
0x0000000000000000000000000000000000000000000000000000000000000000",
            Ok(Some(Value::buff_from(expected.to_vec()).unwrap())),
        );
    }

    #[test]
    fn test_sha256_overwrite() {
        let expected = [0u8; 32];
        crosscheck(
            "(sha256 1)
0x0000000000000000000000000000000000000000000000000000000000000000",
            Ok(Some(Value::buff_from(expected.to_vec()).unwrap())),
        );
    }

    #[test]
    fn test_sha512_256() {
        let mut expected = [0u8; 32];
        hex::decode_to_slice(
            "515a7e92e7c60522db968d81ff70b80818fc17aeabbec36baf0dda2812e94a86",
            &mut expected,
        )
        .unwrap();
        crosscheck(
            "(sha512/256 1)",
            Ok(Some(Value::buff_from(expected.to_vec()).unwrap())),
        )
    }

    #[test]
    fn test_sha256_large_buff() {
        let mut expected = [0u8; 32];
        hex::decode_to_slice(
            "c4145364a3ba46002fb14242872f795535bae6738b1e47ba21eb405cfdf820a5",
            &mut expected,
        )
        .unwrap();
        crosscheck(
            &format!("(sha256 0x{})", "aa".repeat(1048576)),
            Ok(Some(Value::buff_from(expected.to_vec()).unwrap())),
        )
    }

    #[test]
    fn test_sha512_large_buff() {
        let mut expected = [0u8; 64];
        hex::decode_to_slice(
            "e3bbbc0cc37e452a5d2674240c77f7d5137b93fb9d4026b40a10a2ffeda543ff303df1220492cb9e8caba96c24aebb2d2ea359a38141b62d31d80996defdf874",
            &mut expected,
        )
        .unwrap();
        crosscheck(
            &format!("(sha512 0x{})", "aa".repeat(1048576)),
            Ok(Some(Value::buff_from(expected.to_vec()).unwrap())),
        )
    }

    #[test]
    fn test_sha512256_large_buff() {
        let mut expected = [0u8; 32];
        hex::decode_to_slice(
            "7d5b92a003008bb3ef9656e2212b27c47f325ecfba4ed78f1d7e83161bcaab4a",
            &mut expected,
        )
        .unwrap();
        crosscheck(
            &format!("(sha512/256 0x{})", "aa".repeat(1048576)),
            Ok(Some(Value::buff_from(expected.to_vec()).unwrap())),
        )
    }

    #[test]
    fn test_hash160_large_buff() {
        let mut expected = [0u8; 20];
        hex::decode_to_slice("b7ec553926497b8cb2ae106bf75396359296830e", &mut expected).unwrap();
        crosscheck(
            &format!("(hash160 0x{})", "aa".repeat(1048576)),
            Ok(Some(Value::buff_from(expected.to_vec()).unwrap())),
        )
    }

    #[test]
    fn test_keccak256_large_buff() {
        let mut expected = [0u8; 32];
        hex::decode_to_slice(
            "b285806915c373a14ab20b503b1fe58a50544363263a1a17f50841ed08da85cb",
            &mut expected,
        )
        .unwrap();
        crosscheck(
            &format!("(keccak256 0x{})", "aa".repeat(1048576)),
            Ok(Some(Value::buff_from(expected.to_vec()).unwrap())),
        )
    }
}
