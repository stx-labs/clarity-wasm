use clar2wasm::wasm_generator::WasmGenerator;
use clarity::vm::types::{TupleData, TupleTypeSignature, TypeSignature};
use clarity::vm::Value;
use clarity_types::ClarityName;
use proptest::prelude::*;

use crate::{prop_signature, PropValue};

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn compare_serialization_size(
        (ty, value) in prop_signature()
            .prop_ind_flat_map2(|ty| PropValue::from_type(ty).prop_map_into())
            .no_shrink()
    ) {
        let mut gen = WasmGenerator::empty();

        // since `serialization_size` push on the stack the value and the size,
        // we'll expect a tuple {a: value, b: size}
        let return_ty: TypeSignature = TupleTypeSignature::try_from(vec![
            (ClarityName::from_literal("a"), ty.clone()),
            (ClarityName::from_literal("b"), TypeSignature::UIntType),
        ])
        .unwrap()
        .into();

        gen.create_module(&return_ty, |gen, builder| {
            gen.pass_value(builder, &value, &ty)
                .expect("failed to write instructions for original value");

            gen.serialization_size(builder, &ty)
                .expect("failed to write serialization size instructions");

            // we need to extend the u32 we get for the size into a uint
            builder
                .unop(walrus::ir::UnaryOp::I64ExtendUI32)
                .i64_const(0);
        });

        let res = gen.execute_module(&return_ty);

        let expected_size = value
            .serialized_size()
            .expect("could not compute serialized size");
        let expected = TupleData::from_data(vec![
            (ClarityName::from_literal("a"), value),
            (ClarityName::from_literal("b"), Value::UInt(expected_size as u128)),
        ])
        .unwrap()
        .into();

        assert_eq!(res, expected);
    }
}
