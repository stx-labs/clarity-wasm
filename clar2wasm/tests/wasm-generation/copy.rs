use clar2wasm::wasm_generator::WasmGenerator;
use clarity_types::Value;
use proptest::prelude::*;
use walrus::ValType;

use crate::{prop_signature, PropValue};

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn copy_value(
        (ty, value) in prop_signature().prop_ind_flat_map2(PropValue::from_type)
    ) {
        let mut gen = WasmGenerator::empty();
        gen.create_module(&ty, |gen, builder| {
            let memory = gen.get_memory_with_pages(2);
            let copy_offset_int = 65536;

            let copy_offset = gen.borrow_local(ValType::I32);

            gen.pass_value(builder, &value, &ty).expect("couldn't pass value");

            let value_locals = gen.save_to_locals(builder, &ty, true);

            builder.i32_const(copy_offset_int).local_set(*copy_offset);

            gen.copy_value(builder, &ty, &value_locals, *copy_offset).expect("couldn't copy value");

            // We memset the memory before the copied value to 0 to make sure we don't reuse
            // any part of the original value.
            builder.i32_const(0).i32_const(0).i32_const(copy_offset_int).memory_fill(memory);

            for l in value_locals {
                builder.local_get(l);
            }
        });

        let res = gen.execute_module(&ty);

        assert_eq!(Value::from(value), res);
    }
}
