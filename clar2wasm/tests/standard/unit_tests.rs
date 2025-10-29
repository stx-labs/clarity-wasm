use clar2wasm::linker::load_stdlib;
use clar2wasm::wasm_generator::END_OF_STANDARD_DATA;
use clarity::vm::types::{
    BuffData, PrincipalData, QualifiedContractIdentifier, ResponseData, SequenceData,
    StandardPrincipalData, TupleData,
};
use clarity::vm::Value;
use hex::FromHex;
use wasmtime::Val;

#[test]
fn test_add_uint() {
    let (instance, mut store) = load_stdlib().unwrap();
    let add = instance.get_func(&mut store, "stdlib.add-uint").unwrap();
    let mut sum = [Val::I64(0), Val::I64(0)];

    // 0 + 0 = 0
    add.call(
        &mut store,
        &[Val::I64(0), Val::I64(0), Val::I64(0), Val::I64(0)],
        &mut sum,
    )
    .expect("call to add-uint failed");
    assert_eq!(sum[0].i64(), Some(0));
    assert_eq!(sum[1].i64(), Some(0));

    // 1 + 2 = 3
    add.call(
        &mut store,
        &[Val::I64(1), Val::I64(0), Val::I64(2), Val::I64(0)],
        &mut sum,
    )
    .expect("call to add-uint failed");
    assert_eq!(sum[0].i64(), Some(3));
    assert_eq!(sum[1].i64(), Some(0));

    // Carry
    // 0xffff_ffff_ffff_ffff + 1 = 0x1_0000_0000_0000_0000
    add.call(
        &mut store,
        &[Val::I64(-1), Val::I64(0), Val::I64(1), Val::I64(0)],
        &mut sum,
    )
    .expect("call to add-uint failed");
    assert_eq!(sum[0].i64(), Some(0));
    assert_eq!(sum[1].i64(), Some(1));

    // Overflow
    // 0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffff + 1 = Overflow
    add.call(
        &mut store,
        &[Val::I64(-1), Val::I64(-1), Val::I64(1), Val::I64(0)],
        &mut sum,
    )
    .expect_err("expected overflow");

    // Overflow
    // 1 + 0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffff = Overflow
    add.call(
        &mut store,
        &[Val::I64(1), Val::I64(0), Val::I64(-1), Val::I64(-1)],
        &mut sum,
    )
    .expect_err("expected overflow");
}

#[test]
fn test_add_int() {
    let (instance, mut store) = load_stdlib().unwrap();
    let add = instance.get_func(&mut store, "stdlib.add-int").unwrap();
    let mut sum = [Val::I64(0), Val::I64(0)];

    // 0 + 0 = 0
    add.call(
        &mut store,
        &[Val::I64(0), Val::I64(0), Val::I64(0), Val::I64(0)],
        &mut sum,
    )
    .expect("call to add-int failed");
    assert_eq!(sum[0].i64(), Some(0));
    assert_eq!(sum[1].i64(), Some(0));

    // 1 + 2 = 3
    add.call(
        &mut store,
        &[Val::I64(1), Val::I64(0), Val::I64(2), Val::I64(0)],
        &mut sum,
    )
    .expect("call to add-int failed");
    assert_eq!(sum[0].i64(), Some(3));
    assert_eq!(sum[1].i64(), Some(0));

    // Carry
    // 0xffff_ffff_ffff_ffff + 1 = 0x1_0000_0000_0000_0000
    add.call(
        &mut store,
        &[Val::I64(-1), Val::I64(0), Val::I64(1), Val::I64(0)],
        &mut sum,
    )
    .expect("call to add-int failed");
    assert_eq!(sum[0].i64(), Some(0));
    assert_eq!(sum[1].i64(), Some(1));

    // Overflow in signed 64-bit, but fine in 128-bit
    // 0x7fff_ffff_ffff_ffff + 0x7fff_ffff_ffff_ffff = 0xffff_ffff_ffff_fffe
    add.call(
        &mut store,
        &[
            Val::I64(0x7fff_ffff_ffff_ffff),
            Val::I64(0),
            Val::I64(0x7fff_ffff_ffff_ffff),
            Val::I64(0),
        ],
        &mut sum,
    )
    .expect("call to add-int failed");
    assert_eq!(sum[0].i64(), Some(-2));
    assert_eq!(sum[1].i64(), Some(0));

    // Overflow
    // 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff + 1 = Overflow
    add.call(
        &mut store,
        &[
            Val::I64(-1),
            Val::I64(0x7fff_ffff_ffff_ffff),
            Val::I64(1),
            Val::I64(0),
        ],
        &mut sum,
    )
    .expect_err("expected overflow");

    // Overflow
    // 1 + 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff = Overflow
    add.call(
        &mut store,
        &[
            Val::I64(1),
            Val::I64(0),
            Val::I64(-1),
            Val::I64(0x7fff_ffff_ffff_ffff),
        ],
        &mut sum,
    )
    .expect_err("expected overflow");

    // Overflow
    // 0x8000_0000_0000_0000_0000_0000_0000_0000 + -1 = Overflow
    add.call(
        &mut store,
        &[
            Val::I64(0),
            Val::I64(-9223372036854775808),
            Val::I64(-1),
            Val::I64(-1),
        ],
        &mut sum,
    )
    .expect_err("expected overflow");
}

#[test]
fn test_sub_uint() {
    let (instance, mut store) = load_stdlib().unwrap();
    let sub = instance.get_func(&mut store, "stdlib.sub-uint").unwrap();
    let mut sum = [Val::I64(0), Val::I64(0)];

    // 0 - 0 = 0
    sub.call(
        &mut store,
        &[Val::I64(0), Val::I64(0), Val::I64(0), Val::I64(0)],
        &mut sum,
    )
    .expect("call to sub-uint failed");
    assert_eq!(sum[0].i64(), Some(0));
    assert_eq!(sum[1].i64(), Some(0));

    // 3 - 2 = 1
    sub.call(
        &mut store,
        &[Val::I64(3), Val::I64(0), Val::I64(2), Val::I64(0)],
        &mut sum,
    )
    .expect("call to sub-uint failed");
    assert_eq!(sum[0].i64(), Some(1));
    assert_eq!(sum[1].i64(), Some(0));

    // Borrow
    // 0x1_0000_0000_0000_0000 - 1 = 0xffff_ffff_ffff_ffff
    sub.call(
        &mut store,
        &[Val::I64(0), Val::I64(1), Val::I64(1), Val::I64(0)],
        &mut sum,
    )
    .expect("call to sub-uint failed");
    assert_eq!(sum[0].i64(), Some(-1));
    assert_eq!(sum[1].i64(), Some(0));

    // Signed underflow, but fine for unsigned
    // 0x8000_0000_0000_0000_0000_0000_0000_0000 - 1 = 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff
    sub.call(
        &mut store,
        &[
            Val::I64(0),
            Val::I64(-9223372036854775808),
            Val::I64(1),
            Val::I64(0),
        ],
        &mut sum,
    )
    .expect("call to sub-uint failed");
    assert_eq!(sum[0].i64(), Some(-1));
    assert_eq!(sum[1].i64(), Some(0x7fff_ffff_ffff_ffff));

    // Underflow
    // 1 - 2 = Underflow
    sub.call(
        &mut store,
        &[Val::I64(1), Val::I64(0), Val::I64(2), Val::I64(0)],
        &mut sum,
    )
    .expect_err("expected underflow");
}

#[test]
fn test_sub_int() {
    let (instance, mut store) = load_stdlib().unwrap();
    let sub = instance.get_func(&mut store, "stdlib.sub-int").unwrap();
    let mut sum = [Val::I64(0), Val::I64(0)];

    // 0 - 0 = 0
    sub.call(
        &mut store,
        &[Val::I64(0), Val::I64(0), Val::I64(0), Val::I64(0)],
        &mut sum,
    )
    .expect("call to sub-int failed");
    assert_eq!(sum[0].i64(), Some(0));
    assert_eq!(sum[1].i64(), Some(0));

    // 3 - 2 = 1
    sub.call(
        &mut store,
        &[Val::I64(3), Val::I64(0), Val::I64(2), Val::I64(0)],
        &mut sum,
    )
    .expect("call to sub-int failed");
    assert_eq!(sum[0].i64(), Some(1));
    assert_eq!(sum[1].i64(), Some(0));

    // 1 - 2 = -1
    sub.call(
        &mut store,
        &[Val::I64(1), Val::I64(0), Val::I64(2), Val::I64(0)],
        &mut sum,
    )
    .expect("call to sub-int failed");
    assert_eq!(sum[0].i64(), Some(-1));
    assert_eq!(sum[1].i64(), Some(-1));

    // Borrow
    // 0x1_0000_0000_0000_0000 - 1 = 0xffff_ffff_ffff_ffff
    sub.call(
        &mut store,
        &[Val::I64(0), Val::I64(1), Val::I64(1), Val::I64(0)],
        &mut sum,
    )
    .expect("call to sub-int failed");
    assert_eq!(sum[0].i64(), Some(-1));
    assert_eq!(sum[1].i64(), Some(0));

    // Underflow
    // 0x8000_0000_0000_0000_0000_0000_0000_0000 - 1 = Underflow
    sub.call(
        &mut store,
        &[
            Val::I64(0),
            Val::I64(-9223372036854775808),
            Val::I64(1),
            Val::I64(0),
        ],
        &mut sum,
    )
    .expect_err("expected underflow");
}

#[test]
fn test_mul_uint() {
    let (instance, mut store) = load_stdlib().unwrap();
    let mul = instance.get_func(&mut store, "stdlib.mul-uint").unwrap();
    let mut result = [Val::I64(0), Val::I64(0)];

    // 0 * 0 = 0
    mul.call(
        &mut store,
        &[Val::I64(0), Val::I64(0), Val::I64(0), Val::I64(0)],
        &mut result,
    )
    .expect("call to mul-uint failed");
    assert_eq!(result[0].i64(), Some(0));
    assert_eq!(result[1].i64(), Some(0));

    // 0 * 0x0123_4567_89ab_cdef_fedc_ba98_7654_3210 = 0
    mul.call(
        &mut store,
        &[
            Val::I64(0),
            Val::I64(0),
            Val::I64(-81985529216486896),
            Val::I64(0x0123_4567_89ab_cdef),
        ],
        &mut result,
    )
    .expect("call to mul-uint failed");
    assert_eq!(result[0].i64(), Some(0));
    assert_eq!(result[1].i64(), Some(0));

    // 0x0123_4567_89ab_cdef_fedc_ba98_7654_3210 * 0 = 0
    mul.call(
        &mut store,
        &[
            Val::I64(-81985529216486896),
            Val::I64(0x0123_4567_89ab_cdef),
            Val::I64(0),
            Val::I64(0),
        ],
        &mut result,
    )
    .expect("call to mul-uint failed");
    assert_eq!(result[0].i64(), Some(0));
    assert_eq!(result[1].i64(), Some(0));

    // 1 * 2 = 2
    mul.call(
        &mut store,
        &[Val::I64(1), Val::I64(0), Val::I64(2), Val::I64(0)],
        &mut result,
    )
    .expect("call to mul-uint failed");
    assert_eq!(result[0].i64(), Some(2));
    assert_eq!(result[1].i64(), Some(0));

    // 0xffff_ffff_ffff_ffff * 0xffff_ffff_ffff_ffff = 0xffff_ffff_ffff_fffe_0000_0000_0000_0001
    mul.call(
        &mut store,
        &[Val::I64(-1), Val::I64(0), Val::I64(-1), Val::I64(0)],
        &mut result,
    )
    .expect("call to mul-uint failed");
    assert_eq!(result[0].i64(), Some(1));
    assert_eq!(result[1].i64(), Some(-2));

    // Overflow
    // 0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffff * 2 = Overflow
    mul.call(
        &mut store,
        &[Val::I64(-1), Val::I64(-1), Val::I64(2), Val::I64(0)],
        &mut result,
    )
    .expect_err("expected overflow");

    // Overflow (a2b2)
    // 0x1_0000_0000_0000_0000 * 0x1_0000_0000_0000_0000 = Overflow
    mul.call(
        &mut store,
        &[Val::I64(0), Val::I64(1), Val::I64(0), Val::I64(1)],
        &mut result,
    )
    .expect_err("expected overflow");

    // Overflow (a3b1)
    // 0x1_0000_0000_0000_0000_0000_0000 * 0x1_0000_0000 = Overflow
    mul.call(
        &mut store,
        &[
            Val::I64(0),
            Val::I64(0x1_0000_0000),
            Val::I64(0x1_0000_0000),
            Val::I64(0),
        ],
        &mut result,
    )
    .expect_err("expected overflow");

    // Overflow (a1b3)
    // 0x1_0000_0000 * 0x1_0000_0000_0000_0000_0000_0000 = Overflow
    mul.call(
        &mut store,
        &[
            Val::I64(0x1_0000_0000),
            Val::I64(0),
            Val::I64(0),
            Val::I64(0x1_0000_0000),
        ],
        &mut result,
    )
    .expect_err("expected overflow");

    // Overflow (a3b2)
    // 0x1_0000_0000_0000_0000_0000_0000 * 0x1_0000_0000_0000_0000 = Overflow
    mul.call(
        &mut store,
        &[
            Val::I64(0),
            Val::I64(0x1_0000_0000),
            Val::I64(0),
            Val::I64(1),
        ],
        &mut result,
    )
    .expect_err("expected overflow");

    // Overflow (a2b3)
    // 0x1_0000_0000_0000_0000 * 0x1_0000_0000_0000_0000_0000_0000 = Overflow
    mul.call(
        &mut store,
        &[
            Val::I64(0),
            Val::I64(1),
            Val::I64(0),
            Val::I64(0x1_0000_0000),
        ],
        &mut result,
    )
    .expect_err("expected overflow");

    // Overflow (a3b3)
    // 0x1_0000_0000_0000_0000_0000_0000 * 0x1_0000_0000_0000_0000_0000_0000 = Overflow
    mul.call(
        &mut store,
        &[
            Val::I64(0),
            Val::I64(0x1_0000_0000),
            Val::I64(0),
            Val::I64(0x1_0000_0000),
        ],
        &mut result,
    )
    .expect_err("expected overflow");

    // 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff * 2 = 0xffff_ffff_ffff_ffff_ffff_ffff_ffff_fffe
    mul.call(
        &mut store,
        &[
            Val::I64(-1),
            Val::I64(9223372036854775807),
            Val::I64(2),
            Val::I64(0),
        ],
        &mut result,
    )
    .expect("call to mul-uint failed");
    assert_eq!(result[0].i64(), Some(-2));
    assert_eq!(result[1].i64(), Some(-1));

    // 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff * 3 = Overflow
    mul.call(
        &mut store,
        &[
            Val::I64(-1),
            Val::I64(9223372036854775807),
            Val::I64(3),
            Val::I64(0),
        ],
        &mut result,
    )
    .expect_err("expected overflow");
}

#[test]
fn test_mul_int() {
    let (instance, mut store) = load_stdlib().unwrap();
    let mul = instance.get_func(&mut store, "stdlib.mul-int").unwrap();
    let mut result = [Val::I64(0), Val::I64(0)];

    // 0 * 0 = 0
    mul.call(
        &mut store,
        &[Val::I64(0), Val::I64(0), Val::I64(0), Val::I64(0)],
        &mut result,
    )
    .expect("call to mul-int failed");
    assert_eq!(result[0].i64(), Some(0));
    assert_eq!(result[1].i64(), Some(0));

    // 0 * 0x0123_4567_89ab_cdef_fedc_ba98_7654_3210 = 0
    mul.call(
        &mut store,
        &[
            Val::I64(0),
            Val::I64(0),
            Val::I64(-81985529216486896),
            Val::I64(0x0123_4567_89ab_cdef),
        ],
        &mut result,
    )
    .expect("call to mul-int failed");
    assert_eq!(result[0].i64(), Some(0));
    assert_eq!(result[1].i64(), Some(0));

    // 0x0123_4567_89ab_cdef_fedc_ba98_7654_3210 * 0 = 0
    mul.call(
        &mut store,
        &[
            Val::I64(-81985529216486896),
            Val::I64(0x0123_4567_89ab_cdef),
            Val::I64(0),
            Val::I64(0),
        ],
        &mut result,
    )
    .expect("call to mul-int failed");
    assert_eq!(result[0].i64(), Some(0));
    assert_eq!(result[1].i64(), Some(0));

    // 1 * 2 = 2
    mul.call(
        &mut store,
        &[Val::I64(1), Val::I64(0), Val::I64(2), Val::I64(0)],
        &mut result,
    )
    .expect("call to mul-int failed");
    assert_eq!(result[0].i64(), Some(2));
    assert_eq!(result[1].i64(), Some(0));

    // 0xffff_ffff_ffff_ffff * 0xffff_ffff_ffff_ffff = 0xffff_ffff_ffff_fffe_0000_0000_0000_0001
    mul.call(
        &mut store,
        &[Val::I64(-1), Val::I64(0), Val::I64(-1), Val::I64(0)],
        &mut result,
    )
    .expect_err("expected overflow");

    // Overflow on unsigned multiplication
    // 0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffff * 2 = -2
    mul.call(
        &mut store,
        &[Val::I64(-1), Val::I64(-1), Val::I64(2), Val::I64(0)],
        &mut result,
    )
    .expect("call to mul-int failed");
    assert_eq!(result[0].i64(), Some(-2));
    assert_eq!(result[1].i64(), Some(-1));

    // cannot take the absolute value of i128::MIN but should be able to multiply by 1
    mul.call(
        &mut store,
        &[
            Val::I64(1),
            Val::I64(0),
            Val::I64(0),
            Val::I64(0x8000000000000000u64 as i64),
        ],
        &mut result,
    )
    .expect("call to mul-int failed");
    assert_eq!(result[0].i64(), Some(0));
    assert_eq!(result[1].i64(), Some(0x8000000000000000u64 as i64));

    // cannot take the absolute value of i128::MIN but should be able to multiply by 1 (reverse)
    mul.call(
        &mut store,
        &[
            Val::I64(0),
            Val::I64(0x8000000000000000u64 as i64),
            Val::I64(1),
            Val::I64(0),
        ],
        &mut result,
    )
    .expect("call to mul-int failed");
    assert_eq!(result[0].i64(), Some(0));
    assert_eq!(result[1].i64(), Some(0x8000000000000000u64 as i64));

    // i128::MIN * 2 overflows
    mul.call(
        &mut store,
        &[
            Val::I64(2),
            Val::I64(0),
            Val::I64(0),
            Val::I64(0x8000000000000000u64 as i64),
        ],
        &mut result,
    )
    .expect_err("expected overflow");

    // i128::MIN * -1 overflows
    mul.call(
        &mut store,
        &[
            Val::I64(-1),
            Val::I64(-1),
            Val::I64(0),
            Val::I64(0x8000000000000000u64 as i64),
        ],
        &mut result,
    )
    .expect_err("expected overflow");

    // -1 * i128::MIN overflows
    mul.call(
        &mut store,
        &[
            Val::I64(0),
            Val::I64(0x8000000000000000u64 as i64),
            Val::I64(-1),
            Val::I64(-1),
        ],
        &mut result,
    )
    .expect_err("expected overflow");
}

#[test]
fn test_div_uint() {
    let (instance, mut store) = load_stdlib().unwrap();
    let div = instance.get_func(&mut store, "stdlib.div-uint").unwrap();
    let mut result = [Val::I64(0), Val::I64(0)];

    // 4 / 2 = 2
    div.call(
        &mut store,
        &[Val::I64(4), Val::I64(0), Val::I64(2), Val::I64(0)],
        &mut result,
    )
    .expect("call to div-uint failed");
    assert_eq!(result[0].i64(), Some(2));
    assert_eq!(result[1].i64(), Some(0));

    // 7 / 4 = 1
    div.call(
        &mut store,
        &[Val::I64(7), Val::I64(0), Val::I64(4), Val::I64(0)],
        &mut result,
    )
    .expect("call to div-uint failed");
    assert_eq!(result[0].i64(), Some(1));
    assert_eq!(result[1].i64(), Some(0));

    // 123 / 456 = 0
    div.call(
        &mut store,
        &[Val::I64(123), Val::I64(0), Val::I64(456), Val::I64(0)],
        &mut result,
    )
    .expect("call to div-uint failed");
    assert_eq!(result[0].i64(), Some(0));
    assert_eq!(result[1].i64(), Some(0));

    // 0 / 0x123_0000_0000_0000_0456 = 0
    div.call(
        &mut store,
        &[Val::I64(0), Val::I64(0), Val::I64(0x456), Val::I64(0x123)],
        &mut result,
    )
    .expect("call to div-uint failed");
    assert_eq!(result[0].i64(), Some(0));
    assert_eq!(result[1].i64(), Some(0));

    // 0x123_0000_0000_0000_0456 / 0 = DivideByZero
    div.call(
        &mut store,
        &[Val::I64(0x456), Val::I64(0x123), Val::I64(0), Val::I64(0)],
        &mut result,
    )
    .expect_err("expected divide by zero");

    // 0x123_0000_0000_0000_0456 / 22 = 0xd_3a2e_8ba2_e8ba_2ebe
    div.call(
        &mut store,
        &[Val::I64(0x456), Val::I64(0x123), Val::I64(22), Val::I64(0)],
        &mut result,
    )
    .expect("call to div-uint failed");
    assert_eq!(result[0].i64(), Some(0x3a2e_8ba2_e8ba_2ebe));
    assert_eq!(result[1].i64(), Some(0xd));
}

#[test]
fn test_div_int() {
    let (instance, mut store) = load_stdlib().unwrap();
    let div = instance.get_func(&mut store, "stdlib.div-int").unwrap();
    let mut result = [Val::I64(0), Val::I64(0)];

    // i128::MIN / -1 overflows
    div.call(
        &mut store,
        &[
            Val::I64(0),
            Val::I64(-9223372036854775808),
            Val::I64(-1),
            Val::I64(-1),
        ],
        &mut result,
    )
    .expect_err("expected overflow");

    // 4 / 2 = 2
    div.call(
        &mut store,
        &[Val::I64(4), Val::I64(0), Val::I64(2), Val::I64(0)],
        &mut result,
    )
    .expect("call to div-int failed");
    assert_eq!(result[0].i64(), Some(2));
    assert_eq!(result[1].i64(), Some(0));

    // -4 / 2 = -2
    div.call(
        &mut store,
        &[Val::I64(-4), Val::I64(-1), Val::I64(2), Val::I64(0)],
        &mut result,
    )
    .expect("call to div-int failed");
    assert_eq!(result[0].i64(), Some(-2));
    assert_eq!(result[1].i64(), Some(-1));

    // 4 / -2 = -2
    div.call(
        &mut store,
        &[Val::I64(4), Val::I64(0), Val::I64(-2), Val::I64(-1)],
        &mut result,
    )
    .expect("call to div-int failed");
    assert_eq!(result[0].i64(), Some(-2));
    assert_eq!(result[1].i64(), Some(-1));

    // -4 / -2 = 2
    div.call(
        &mut store,
        &[Val::I64(-4), Val::I64(-1), Val::I64(-2), Val::I64(-1)],
        &mut result,
    )
    .expect("call to div-int failed");
    assert_eq!(result[0].i64(), Some(2));
    assert_eq!(result[1].i64(), Some(0));

    // 0x8000_0000_0000_0000_0000_0000_0000_0000 / -2 = 0xc000_0000_0000_0000_0000_0000_0000_0000
    div.call(
        &mut store,
        &[
            Val::I64(0),
            Val::I64(-9223372036854775808),
            Val::I64(2),
            Val::I64(0),
        ],
        &mut result,
    )
    .expect("call to div-int failed");
    assert_eq!(result[0].i64(), Some(0));
    assert_eq!(result[1].i64(), Some(-4611686018427387904i64));
}

#[test]
fn test_mod_uint() {
    let (instance, mut store) = load_stdlib().unwrap();
    let modulo = instance.get_func(&mut store, "stdlib.mod-uint").unwrap();
    let mut result = [Val::I64(0), Val::I64(0)];

    // 4 % 2 = 0
    modulo
        .call(
            &mut store,
            &[Val::I64(4), Val::I64(0), Val::I64(2), Val::I64(0)],
            &mut result,
        )
        .expect("call to mod-uint failed");
    assert_eq!(result[0].i64(), Some(0));
    assert_eq!(result[1].i64(), Some(0));

    // 7 % 4 = 3
    modulo
        .call(
            &mut store,
            &[Val::I64(7), Val::I64(0), Val::I64(4), Val::I64(0)],
            &mut result,
        )
        .expect("call to mod-uint failed");
    assert_eq!(result[0].i64(), Some(3));
    assert_eq!(result[1].i64(), Some(0));

    // 123 % 456 = 123
    modulo
        .call(
            &mut store,
            &[Val::I64(123), Val::I64(0), Val::I64(456), Val::I64(0)],
            &mut result,
        )
        .expect("call to mod-uint failed");
    assert_eq!(result[0].i64(), Some(123));
    assert_eq!(result[1].i64(), Some(0));

    // 0 % 0x123_0000_0000_0000_0456 = 0
    modulo
        .call(
            &mut store,
            &[Val::I64(0), Val::I64(0), Val::I64(0x456), Val::I64(0x123)],
            &mut result,
        )
        .expect("call to mod-uint failed");
    assert_eq!(result[0].i64(), Some(0));
    assert_eq!(result[1].i64(), Some(0));

    // 0x123_0000_0000_0000_0456 % 0 = DivideByZero
    modulo
        .call(
            &mut store,
            &[Val::I64(0x456), Val::I64(0x123), Val::I64(0), Val::I64(0)],
            &mut result,
        )
        .expect_err("expected divide by zero");

    // 0x123_0000_0000_0000_0456 % 22 = 2
    modulo
        .call(
            &mut store,
            &[Val::I64(0x456), Val::I64(0x123), Val::I64(22), Val::I64(0)],
            &mut result,
        )
        .expect("call to mod-uint failed");
    assert_eq!(result[0].i64(), Some(2));
    assert_eq!(result[1].i64(), Some(0));
}

#[test]
fn test_mod_int() {
    let (instance, mut store) = load_stdlib().unwrap();
    let modulo = instance.get_func(&mut store, "stdlib.mod-int").unwrap();
    let mut result = [Val::I64(0), Val::I64(0)];

    // 7 % 4 = 3
    modulo
        .call(
            &mut store,
            &[Val::I64(7), Val::I64(0), Val::I64(4), Val::I64(0)],
            &mut result,
        )
        .expect("call to mod-int failed");
    assert_eq!(result[0].i64(), Some(3));
    assert_eq!(result[1].i64(), Some(0));

    // -7 / 4 = -3
    modulo
        .call(
            &mut store,
            &[Val::I64(-7), Val::I64(-1), Val::I64(4), Val::I64(0)],
            &mut result,
        )
        .expect("call to mod-int failed");
    assert_eq!(result[0].i64(), Some(-3));
    assert_eq!(result[1].i64(), Some(-1));

    // 7 / -4 = 3
    modulo
        .call(
            &mut store,
            &[Val::I64(7), Val::I64(0), Val::I64(-4), Val::I64(-1)],
            &mut result,
        )
        .expect("call to mod-int failed");
    assert_eq!(result[0].i64(), Some(3));
    assert_eq!(result[1].i64(), Some(0));

    // -7 / -4 = -3
    modulo
        .call(
            &mut store,
            &[Val::I64(-7), Val::I64(-1), Val::I64(-4), Val::I64(-1)],
            &mut result,
        )
        .expect("call to mod-int failed");
    assert_eq!(result[0].i64(), Some(-3));
    assert_eq!(result[1].i64(), Some(-1));

    // 0x123_0000_0000_0000_0456 % 0 = DivideByZero
    modulo
        .call(
            &mut store,
            &[Val::I64(0x456), Val::I64(0x123), Val::I64(0), Val::I64(0)],
            &mut result,
        )
        .expect_err("expected divide by zero");
}

#[test]
fn test_lt_uint() {
    let (instance, mut store) = load_stdlib().unwrap();
    let lt = instance.get_func(&mut store, "stdlib.lt-uint").unwrap();
    let mut result = [Val::I32(0)];

    // 0 < 1 is true
    lt.call(
        &mut store,
        &[Val::I64(0), Val::I64(0), Val::I64(1), Val::I64(0)],
        &mut result,
    )
    .expect("call to lt-uint failed");
    assert_eq!(result[0].i32(), Some(1));

    // 1 < 0 is false
    lt.call(
        &mut store,
        &[Val::I64(1), Val::I64(0), Val::I64(0), Val::I64(0)],
        &mut result,
    )
    .expect("call to lt-uint failed");
    assert_eq!(result[0].i32(), Some(0));

    // 1 < 1 is false
    lt.call(
        &mut store,
        &[Val::I64(0), Val::I64(1), Val::I64(0), Val::I64(1)],
        &mut result,
    )
    .expect("call to lt-uint failed");
    assert_eq!(result[0].i32(), Some(0));

    // 1 < 0x1_0000_0000_0000_0000 is true
    lt.call(
        &mut store,
        &[Val::I64(1), Val::I64(0), Val::I64(0), Val::I64(1)],
        &mut result,
    )
    .expect("call to lt-uint failed");
    assert_eq!(result[0].i32(), Some(1));

    // 1 < 0x1_0000_0000_0000_0001 is true
    lt.call(
        &mut store,
        &[Val::I64(1), Val::I64(0), Val::I64(1), Val::I64(1)],
        &mut result,
    )
    .expect("call to lt-uint failed");
    assert_eq!(result[0].i32(), Some(1));

    // 0x1_0000_0000_0000_0000 < 1 is false
    lt.call(
        &mut store,
        &[Val::I64(0), Val::I64(1), Val::I64(1), Val::I64(0)],
        &mut result,
    )
    .expect("call to lt-uint failed");
    assert_eq!(result[0].i32(), Some(0));

    // 0x1_0000_0000_0000_0001 < 1 is false
    lt.call(
        &mut store,
        &[Val::I64(1), Val::I64(1), Val::I64(1), Val::I64(0)],
        &mut result,
    )
    .expect("call to lt-uint failed");
    assert_eq!(result[0].i32(), Some(0));

    // 0x1_0000_0000_0000_0000 < 0x1_0000_0000_0000_0001 is true
    lt.call(
        &mut store,
        &[Val::I64(0), Val::I64(1), Val::I64(1), Val::I64(1)],
        &mut result,
    )
    .expect("call to lt-uint failed");
    assert_eq!(result[0].i32(), Some(1));

    // 0x1_0000_0000_0000_0001 < 0x1_0000_0000_0000_0000 is false
    lt.call(
        &mut store,
        &[Val::I64(1), Val::I64(1), Val::I64(0), Val::I64(1)],
        &mut result,
    )
    .expect("call to lt-uint failed");
    assert_eq!(result[0].i32(), Some(0));

    // 0x1_0000_0000_0000_0001 < 0x1_0000_0000_0000_0001 is false
    lt.call(
        &mut store,
        &[Val::I64(1), Val::I64(1), Val::I64(1), Val::I64(1)],
        &mut result,
    )
    .expect("call to lt-uint failed");
    assert_eq!(result[0].i32(), Some(0));

    // u128::MAX (-1 if signed) < 1 is false
    lt.call(
        &mut store,
        &[Val::I64(-1), Val::I64(-1), Val::I64(1), Val::I64(0)],
        &mut result,
    )
    .expect("call to lt-uint failed");
    assert_eq!(result[0].i32(), Some(0));

    // 1 < u128::MAX (-1 if signed) is true
    lt.call(
        &mut store,
        &[Val::I64(0), Val::I64(0), Val::I64(-1), Val::I64(-1)],
        &mut result,
    )
    .expect("call to lt-uint failed");
    assert_eq!(result[0].i32(), Some(1));
}

#[test]
fn test_gt_uint() {
    let (instance, mut store) = load_stdlib().unwrap();
    let gt = instance.get_func(&mut store, "stdlib.gt-uint").unwrap();
    let mut result = [Val::I32(0)];

    // 0 > 1 is false
    gt.call(
        &mut store,
        &[Val::I64(0), Val::I64(0), Val::I64(1), Val::I64(0)],
        &mut result,
    )
    .expect("call to gt-uint failed");
    assert_eq!(result[0].i32(), Some(0));

    // 1 > 0 is true
    gt.call(
        &mut store,
        &[Val::I64(1), Val::I64(0), Val::I64(0), Val::I64(0)],
        &mut result,
    )
    .expect("call to gt-uint failed");
    assert_eq!(result[0].i32(), Some(1));

    // 1 > 1 is false
    gt.call(
        &mut store,
        &[Val::I64(1), Val::I64(0), Val::I64(1), Val::I64(0)],
        &mut result,
    )
    .expect("call to gt-uint failed");
    assert_eq!(result[0].i32(), Some(0));

    // 1 > 0x1_0000_0000_0000_0000 is false
    gt.call(
        &mut store,
        &[Val::I64(1), Val::I64(0), Val::I64(0), Val::I64(1)],
        &mut result,
    )
    .expect("call to gt-uint failed");
    assert_eq!(result[0].i32(), Some(0));

    // 1 > 0x1_0000_0000_0000_0001 is false
    gt.call(
        &mut store,
        &[Val::I64(1), Val::I64(0), Val::I64(1), Val::I64(1)],
        &mut result,
    )
    .expect("call to gt-uint failed");
    assert_eq!(result[0].i32(), Some(0));

    // 0x1_0000_0000_0000_0000 > 1 is true
    gt.call(
        &mut store,
        &[Val::I64(0), Val::I64(1), Val::I64(1), Val::I64(0)],
        &mut result,
    )
    .expect("call to gt-uint failed");
    assert_eq!(result[0].i32(), Some(1));

    // 0x1_0000_0000_0000_0001 > 1 is true
    gt.call(
        &mut store,
        &[Val::I64(1), Val::I64(1), Val::I64(1), Val::I64(0)],
        &mut result,
    )
    .expect("call to gt-uint failed");
    assert_eq!(result[0].i32(), Some(1));

    // 0x1_0000_0000_0000_0000 > 0x1_0000_0000_0000_0001 is false
    gt.call(
        &mut store,
        &[Val::I64(0), Val::I64(1), Val::I64(1), Val::I64(1)],
        &mut result,
    )
    .expect("call to gt-uint failed");
    assert_eq!(result[0].i32(), Some(0));

    // 0x1_0000_0000_0000_0001 > 0x1_0000_0000_0000_0000 is true
    gt.call(
        &mut store,
        &[Val::I64(1), Val::I64(1), Val::I64(0), Val::I64(1)],
        &mut result,
    )
    .expect("call to gt-uint failed");
    assert_eq!(result[0].i32(), Some(1));

    // 0x1_0000_0000_0000_0001 > 0x1_0000_0000_0000_0001 is false
    gt.call(
        &mut store,
        &[Val::I64(1), Val::I64(1), Val::I64(1), Val::I64(1)],
        &mut result,
    )
    .expect("call to gt-uint failed");
    assert_eq!(result[0].i32(), Some(0));

    // u128::MAX (-1 if signed) > 1 is true
    gt.call(
        &mut store,
        &[Val::I64(-1), Val::I64(-1), Val::I64(1), Val::I64(0)],
        &mut result,
    )
    .expect("call to lt-uint failed");
    assert_eq!(result[0].i32(), Some(1));

    // 1 > u128::MAX (-1 if signed) is false
    gt.call(
        &mut store,
        &[Val::I64(0), Val::I64(0), Val::I64(-1), Val::I64(-1)],
        &mut result,
    )
    .expect("call to lt-uint failed");
    assert_eq!(result[0].i32(), Some(0));
}

#[test]
fn test_le_uint() {
    let (instance, mut store) = load_stdlib().unwrap();
    let le = instance.get_func(&mut store, "stdlib.le-uint").unwrap();
    let mut result = [Val::I32(0)];

    // 0 <= 1 is true
    le.call(
        &mut store,
        &[Val::I64(0), Val::I64(0), Val::I64(1), Val::I64(0)],
        &mut result,
    )
    .expect("call to le-uint failed");
    assert_eq!(result[0].i32(), Some(1));

    // 1 <= 0 is false
    le.call(
        &mut store,
        &[Val::I64(1), Val::I64(0), Val::I64(0), Val::I64(0)],
        &mut result,
    )
    .expect("call to le-uint failed");
    assert_eq!(result[0].i32(), Some(0));

    // 1 <= 1 is true
    le.call(
        &mut store,
        &[Val::I64(1), Val::I64(0), Val::I64(1), Val::I64(0)],
        &mut result,
    )
    .expect("call to le-uint failed");
    assert_eq!(result[0].i32(), Some(1));

    // 1 <= 0x1_0000_0000_0000_0000 is true
    le.call(
        &mut store,
        &[Val::I64(1), Val::I64(0), Val::I64(0), Val::I64(1)],
        &mut result,
    )
    .expect("call to le-uint failed");
    assert_eq!(result[0].i32(), Some(1));

    // 1 <= 0x1_0000_0000_0000_0001 is true
    le.call(
        &mut store,
        &[Val::I64(1), Val::I64(0), Val::I64(1), Val::I64(1)],
        &mut result,
    )
    .expect("call to le-uint failed");
    assert_eq!(result[0].i32(), Some(1));

    // 0x1_0000_0000_0000_0000 <= 1 is false
    le.call(
        &mut store,
        &[Val::I64(0), Val::I64(1), Val::I64(1), Val::I64(0)],
        &mut result,
    )
    .expect("call to le-uint failed");
    assert_eq!(result[0].i32(), Some(0));

    // 0x1_0000_0000_0000_0001 <= 1 is false
    le.call(
        &mut store,
        &[Val::I64(1), Val::I64(1), Val::I64(1), Val::I64(0)],
        &mut result,
    )
    .expect("call to le-uint failed");
    assert_eq!(result[0].i32(), Some(0));

    // 0x1_0000_0000_0000_0000 <= 0x1_0000_0000_0000_0001 is true
    le.call(
        &mut store,
        &[Val::I64(0), Val::I64(1), Val::I64(1), Val::I64(1)],
        &mut result,
    )
    .expect("call to le-uint failed");
    assert_eq!(result[0].i32(), Some(1));

    // 0x1_0000_0000_0000_0001 <= 0x1_0000_0000_0000_0000 is false
    le.call(
        &mut store,
        &[Val::I64(1), Val::I64(1), Val::I64(0), Val::I64(1)],
        &mut result,
    )
    .expect("call to le-uint failed");
    assert_eq!(result[0].i32(), Some(0));

    // 0x1_0000_0000_0000_0001 <= 0x1_0000_0000_0000_0001 is true
    le.call(
        &mut store,
        &[Val::I64(1), Val::I64(1), Val::I64(1), Val::I64(1)],
        &mut result,
    )
    .expect("call to le-uint failed");
    assert_eq!(result[0].i32(), Some(1));

    // u128::MAX (-1 if signed) <= 1 is false
    le.call(
        &mut store,
        &[Val::I64(-1), Val::I64(-1), Val::I64(1), Val::I64(0)],
        &mut result,
    )
    .expect("call to lt-uint failed");
    assert_eq!(result[0].i32(), Some(0));

    // 1 <= u128::MAX (-1 if signed) is true
    le.call(
        &mut store,
        &[Val::I64(0), Val::I64(0), Val::I64(-1), Val::I64(-1)],
        &mut result,
    )
    .expect("call to lt-uint failed");
    assert_eq!(result[0].i32(), Some(1));
}

#[test]
fn test_ge_uint() {
    let (instance, mut store) = load_stdlib().unwrap();
    let ge = instance.get_func(&mut store, "stdlib.ge-uint").unwrap();
    let mut result = [Val::I32(0)];

    // 0 >= 1 is false
    ge.call(
        &mut store,
        &[Val::I64(0), Val::I64(0), Val::I64(1), Val::I64(0)],
        &mut result,
    )
    .expect("call to ge-uint failed");
    assert_eq!(result[0].i32(), Some(0));

    // 1 >= 0 is true
    ge.call(
        &mut store,
        &[Val::I64(1), Val::I64(0), Val::I64(0), Val::I64(0)],
        &mut result,
    )
    .expect("call to ge-uint failed");
    assert_eq!(result[0].i32(), Some(1));

    // 1 >= 1 is true
    ge.call(
        &mut store,
        &[Val::I64(1), Val::I64(0), Val::I64(1), Val::I64(0)],
        &mut result,
    )
    .expect("call to ge-uint failed");
    assert_eq!(result[0].i32(), Some(1));

    // 1 >= 0x1_0000_0000_0000_0000 is false
    ge.call(
        &mut store,
        &[Val::I64(1), Val::I64(0), Val::I64(0), Val::I64(1)],
        &mut result,
    )
    .expect("call to ge-uint failed");
    assert_eq!(result[0].i32(), Some(0));

    // 1 >= 0x1_0000_0000_0000_0001 is false
    ge.call(
        &mut store,
        &[Val::I64(1), Val::I64(0), Val::I64(1), Val::I64(1)],
        &mut result,
    )
    .expect("call to ge-uint failed");
    assert_eq!(result[0].i32(), Some(0));

    // 0x1_0000_0000_0000_0000 >= 1 is true
    ge.call(
        &mut store,
        &[Val::I64(0), Val::I64(1), Val::I64(1), Val::I64(0)],
        &mut result,
    )
    .expect("call to ge-uint failed");
    assert_eq!(result[0].i32(), Some(1));

    // 0x1_0000_0000_0000_0001 >= 1 is true
    ge.call(
        &mut store,
        &[Val::I64(1), Val::I64(1), Val::I64(1), Val::I64(0)],
        &mut result,
    )
    .expect("call to ge-uint failed");
    assert_eq!(result[0].i32(), Some(1));

    // 0x1_0000_0000_0000_0000 >= 0x1_0000_0000_0000_0001 is false
    ge.call(
        &mut store,
        &[Val::I64(0), Val::I64(1), Val::I64(1), Val::I64(1)],
        &mut result,
    )
    .expect("call to ge-uint failed");
    assert_eq!(result[0].i32(), Some(0));

    // 0x1_0000_0000_0000_0001 >= 0x1_0000_0000_0000_0000 is true
    ge.call(
        &mut store,
        &[Val::I64(1), Val::I64(1), Val::I64(0), Val::I64(1)],
        &mut result,
    )
    .expect("call to ge-uint failed");
    assert_eq!(result[0].i32(), Some(1));

    // 0x1_0000_0000_0000_0001 >= 0x1_0000_0000_0000_0001 is true
    ge.call(
        &mut store,
        &[Val::I64(1), Val::I64(1), Val::I64(1), Val::I64(1)],
        &mut result,
    )
    .expect("call to ge-uint failed");
    assert_eq!(result[0].i32(), Some(1));

    // u128::MAX (-1 if signed) >= 1 is true
    ge.call(
        &mut store,
        &[Val::I64(-1), Val::I64(-1), Val::I64(1), Val::I64(0)],
        &mut result,
    )
    .expect("call to lt-uint failed");
    assert_eq!(result[0].i32(), Some(1));

    // 1 >= u128::MAX (-1 if signed) is false
    ge.call(
        &mut store,
        &[Val::I64(0), Val::I64(0), Val::I64(-1), Val::I64(-1)],
        &mut result,
    )
    .expect("call to lt-uint failed");
    assert_eq!(result[0].i32(), Some(0));
}

#[test]
fn test_lt_int() {
    let (instance, mut store) = load_stdlib().unwrap();
    let lt = instance.get_func(&mut store, "stdlib.lt-int").unwrap();
    let mut result = [Val::I32(0)];

    // 1 < 1 is false
    lt.call(
        &mut store,
        &[Val::I64(1), Val::I64(0), Val::I64(1), Val::I64(0)],
        &mut result,
    )
    .expect("call to lt-int failed");
    assert_eq!(result[0].i32(), Some(0));

    // -1 < -1 is false
    lt.call(
        &mut store,
        &[Val::I64(-1), Val::I64(-1), Val::I64(-1), Val::I64(-1)],
        &mut result,
    )
    .expect("call to lt-int failed");
    assert_eq!(result[0].i32(), Some(0));

    // -1 < 1 is true
    lt.call(
        &mut store,
        &[Val::I64(-1), Val::I64(-1), Val::I64(1), Val::I64(0)],
        &mut result,
    )
    .expect("call to lt-int failed");
    assert_eq!(result[0].i32(), Some(1));

    // 1 < -1 is false
    lt.call(
        &mut store,
        &[Val::I64(1), Val::I64(0), Val::I64(-1), Val::I64(-1)],
        &mut result,
    )
    .expect("call to lt-int failed");
    assert_eq!(result[0].i32(), Some(0));

    // -1 < 0 is true
    lt.call(
        &mut store,
        &[Val::I64(-1), Val::I64(-1), Val::I64(0), Val::I64(0)],
        &mut result,
    )
    .expect("call to lt-int failed");
    assert_eq!(result[0].i32(), Some(1));

    // -2 < -1 is true
    lt.call(
        &mut store,
        &[Val::I64(-2), Val::I64(-1), Val::I64(-1), Val::I64(-1)],
        &mut result,
    )
    .expect("call to lt-int failed");
    assert_eq!(result[0].i32(), Some(1));

    // -2 < -3 is false
    lt.call(
        &mut store,
        &[Val::I64(-2), Val::I64(-1), Val::I64(-3), Val::I64(-1)],
        &mut result,
    )
    .expect("call to lt-int failed");
    assert_eq!(result[0].i32(), Some(0));

    // I128::MIN < -1 is true
    lt.call(
        &mut store,
        &[Val::I64(0), Val::I64(i64::MIN), Val::I64(-1), Val::I64(-1)],
        &mut result,
    )
    .expect("call to lt-int failed");
    assert_eq!(result[0].i32(), Some(1));

    // -1 < I128::MIN is false
    lt.call(
        &mut store,
        &[Val::I64(-1), Val::I64(-1), Val::I64(0), Val::I64(i64::MIN)],
        &mut result,
    )
    .expect("call to lt-int failed");
    assert_eq!(result[0].i32(), Some(0));
}

#[test]
fn test_gt_int() {
    let (instance, mut store) = load_stdlib().unwrap();
    let gt = instance.get_func(&mut store, "stdlib.gt-int").unwrap();
    let mut result = [Val::I32(0)];

    // 1 > 1 is false
    gt.call(
        &mut store,
        &[Val::I64(1), Val::I64(0), Val::I64(1), Val::I64(0)],
        &mut result,
    )
    .expect("call to gt-int failed");
    assert_eq!(result[0].i32(), Some(0));

    // -1 > -1 is false
    gt.call(
        &mut store,
        &[Val::I64(-1), Val::I64(-1), Val::I64(-1), Val::I64(-1)],
        &mut result,
    )
    .expect("call to gt-int failed");
    assert_eq!(result[0].i32(), Some(0));

    // -1 > 1 is false
    gt.call(
        &mut store,
        &[Val::I64(-1), Val::I64(-1), Val::I64(1), Val::I64(0)],
        &mut result,
    )
    .expect("call to gt-int failed");
    assert_eq!(result[0].i32(), Some(0));

    // 1 > -1 is true
    gt.call(
        &mut store,
        &[Val::I64(1), Val::I64(0), Val::I64(-1), Val::I64(-1)],
        &mut result,
    )
    .expect("call to gt-int failed");
    assert_eq!(result[0].i32(), Some(1));

    // -1 > 0 is false
    gt.call(
        &mut store,
        &[Val::I64(-1), Val::I64(-1), Val::I64(0), Val::I64(0)],
        &mut result,
    )
    .expect("call to gt-int failed");
    assert_eq!(result[0].i32(), Some(0));

    // -2 > -1 is false
    gt.call(
        &mut store,
        &[Val::I64(-2), Val::I64(-1), Val::I64(-1), Val::I64(-1)],
        &mut result,
    )
    .expect("call to gt-int failed");
    assert_eq!(result[0].i32(), Some(0));

    // -2 > -3 is true
    gt.call(
        &mut store,
        &[Val::I64(-2), Val::I64(-1), Val::I64(-3), Val::I64(-1)],
        &mut result,
    )
    .expect("call to gt-int failed");
    assert_eq!(result[0].i32(), Some(1));

    // I128::MIN > -1 is false
    gt.call(
        &mut store,
        &[Val::I64(0), Val::I64(i64::MIN), Val::I64(-1), Val::I64(-1)],
        &mut result,
    )
    .expect("call to gt-int failed");
    assert_eq!(result[0].i32(), Some(0));

    // -1 > I128::MIN is true
    gt.call(
        &mut store,
        &[Val::I64(-1), Val::I64(-1), Val::I64(0), Val::I64(i64::MIN)],
        &mut result,
    )
    .expect("call to gt-int failed");
    assert_eq!(result[0].i32(), Some(1));
}

#[test]
fn test_le_int() {
    let (instance, mut store) = load_stdlib().unwrap();
    let le = instance.get_func(&mut store, "stdlib.le-int").unwrap();
    let mut result = [Val::I32(0)];

    // 1 <= 1 is true
    le.call(
        &mut store,
        &[Val::I64(1), Val::I64(0), Val::I64(1), Val::I64(0)],
        &mut result,
    )
    .expect("call to le-int failed");
    assert_eq!(result[0].i32(), Some(1));

    // -1 <= -1 is true
    le.call(
        &mut store,
        &[Val::I64(-1), Val::I64(-1), Val::I64(-1), Val::I64(-1)],
        &mut result,
    )
    .expect("call to le-int failed");
    assert_eq!(result[0].i32(), Some(1));

    // -1 <= 1 is true
    le.call(
        &mut store,
        &[Val::I64(-1), Val::I64(-1), Val::I64(1), Val::I64(0)],
        &mut result,
    )
    .expect("call to le-int failed");
    assert_eq!(result[0].i32(), Some(1));

    // 1 <= -1 is false
    le.call(
        &mut store,
        &[Val::I64(1), Val::I64(0), Val::I64(-1), Val::I64(-1)],
        &mut result,
    )
    .expect("call to le-int failed");
    assert_eq!(result[0].i32(), Some(0));

    // -1 <= 0 is true
    le.call(
        &mut store,
        &[Val::I64(-1), Val::I64(-1), Val::I64(0), Val::I64(0)],
        &mut result,
    )
    .expect("call to le-int failed");
    assert_eq!(result[0].i32(), Some(1));

    // -2 <= -1 is true
    le.call(
        &mut store,
        &[Val::I64(-2), Val::I64(-1), Val::I64(-1), Val::I64(-1)],
        &mut result,
    )
    .expect("call to le-int failed");
    assert_eq!(result[0].i32(), Some(1));

    // -2 <= -3 is false
    le.call(
        &mut store,
        &[Val::I64(-2), Val::I64(-1), Val::I64(-3), Val::I64(-1)],
        &mut result,
    )
    .expect("call to le-int failed");
    assert_eq!(result[0].i32(), Some(0));

    // I128::MIN <= -1 is true
    le.call(
        &mut store,
        &[Val::I64(0), Val::I64(i64::MIN), Val::I64(-1), Val::I64(-1)],
        &mut result,
    )
    .expect("call to le-int failed");
    assert_eq!(result[0].i32(), Some(1));

    // -1 <= I128::MIN is false
    le.call(
        &mut store,
        &[Val::I64(-1), Val::I64(-1), Val::I64(0), Val::I64(i64::MIN)],
        &mut result,
    )
    .expect("call to le-int failed");
    assert_eq!(result[0].i32(), Some(0));
}

#[test]
fn test_ge_int() {
    let (instance, mut store) = load_stdlib().unwrap();
    let ge = instance.get_func(&mut store, "stdlib.ge-int").unwrap();
    let mut result = [Val::I32(0)];

    // 1 >= 1 is true
    ge.call(
        &mut store,
        &[Val::I64(1), Val::I64(0), Val::I64(1), Val::I64(0)],
        &mut result,
    )
    .expect("call to ge-int failed");
    assert_eq!(result[0].i32(), Some(1));

    // -1 >= -1 is true
    ge.call(
        &mut store,
        &[Val::I64(-1), Val::I64(-1), Val::I64(-1), Val::I64(-1)],
        &mut result,
    )
    .expect("call to ge-int failed");
    assert_eq!(result[0].i32(), Some(1));

    // -1 >= 1 is false
    ge.call(
        &mut store,
        &[Val::I64(-1), Val::I64(-1), Val::I64(1), Val::I64(0)],
        &mut result,
    )
    .expect("call to ge-int failed");
    assert_eq!(result[0].i32(), Some(0));

    // 1 >= -1 is true
    ge.call(
        &mut store,
        &[Val::I64(1), Val::I64(0), Val::I64(-1), Val::I64(-1)],
        &mut result,
    )
    .expect("call to ge-int failed");
    assert_eq!(result[0].i32(), Some(1));

    // -1 >= 0 is false
    ge.call(
        &mut store,
        &[Val::I64(-1), Val::I64(-1), Val::I64(0), Val::I64(0)],
        &mut result,
    )
    .expect("call to ge-int failed");
    assert_eq!(result[0].i32(), Some(0));

    // -2 >= -1 is false
    ge.call(
        &mut store,
        &[Val::I64(-2), Val::I64(-1), Val::I64(-1), Val::I64(-1)],
        &mut result,
    )
    .expect("call to ge-int failed");
    assert_eq!(result[0].i32(), Some(0));

    // -2 >= -3 is true
    ge.call(
        &mut store,
        &[Val::I64(-2), Val::I64(-1), Val::I64(-3), Val::I64(-1)],
        &mut result,
    )
    .expect("call to ge-int failed");
    assert_eq!(result[0].i32(), Some(1));

    // I128::MIN >= -1 is false
    ge.call(
        &mut store,
        &[Val::I64(0), Val::I64(i64::MIN), Val::I64(-1), Val::I64(-1)],
        &mut result,
    )
    .expect("call to ge-int failed");
    assert_eq!(result[0].i32(), Some(0));

    // -1 >= I128::MIN is true
    ge.call(
        &mut store,
        &[Val::I64(-1), Val::I64(-1), Val::I64(0), Val::I64(i64::MIN)],
        &mut result,
    )
    .expect("call to ge-int failed");
    assert_eq!(result[0].i32(), Some(1));
}

fn test_cmp_buff(func_name: &str, reference_func: impl Fn(&[u8], &[u8]) -> bool) {
    let (instance, mut store) = load_stdlib().unwrap();
    let memory = instance
        .get_memory(&mut store, "memory")
        .expect("Could not find memory");

    let cmp = instance.get_func(&mut store, func_name).unwrap();
    let mut result = [Val::I32(0)];

    let mut test_cmp = |buff_a: &[u8], buff_b: &[u8]| {
        let offset_a = 1000;
        let offset_b = offset_a + buff_a.len();
        memory
            .write(&mut store, offset_a, buff_a)
            .expect("could not write to memory");
        memory
            .write(&mut store, offset_b, buff_b)
            .expect("could not write to memory");

        cmp.call(
            &mut store,
            &[
                Val::I32(offset_a as i32),
                Val::I32(buff_a.len() as i32),
                Val::I32(offset_b as i32),
                Val::I32(buff_b.len() as i32),
            ],
            &mut result,
        )
        .expect("call to lt-buff failed");

        assert_eq!(
            result[0].unwrap_i32(),
            reference_func(buff_a, buff_b) as i32
        )
    };

    // tests with empty buffers
    test_cmp(&[], &[]);
    test_cmp(&[], &[0]);
    test_cmp(&[0], &[]);

    // test with longer equal buffers up to...
    test_cmp(&[1, 2, 3], &[1, 2, 3]);
    test_cmp(&[1, 2, 3, 4], &[1, 2, 3]);
    test_cmp(&[1, 2, 3], &[1, 2, 3, 4]);

    // test different end
    test_cmp(&[1, 2, 3], &[1, 2, 4]);
    test_cmp(&[1, 2, 3], &[1, 2, 2]);
}

#[test]
fn test_lt_buff() {
    test_cmp_buff("stdlib.lt-buff", |a, b| a < b)
}

#[test]
fn test_gt_buff() {
    test_cmp_buff("stdlib.gt-buff", |a, b| a > b)
}

#[test]
fn test_le_buff() {
    test_cmp_buff("stdlib.le-buff", |a, b| a <= b)
}

#[test]
fn test_ge_buff() {
    test_cmp_buff("stdlib.ge-buff", |a, b| a >= b)
}

#[test]
fn test_log2_uint() {
    let (instance, mut store) = load_stdlib().unwrap();
    let log2 = instance.get_func(&mut store, "stdlib.log2-uint").unwrap();
    let mut result = [Val::I64(0), Val::I64(0)];

    // log2(0) is an error
    log2.call(&mut store, &[Val::I64(0), Val::I64(0)], &mut result)
        .expect_err("expected log of 0 error");

    // log2(u128::MAX) is not an error (-1 if signed)
    log2.call(&mut store, &[Val::I64(-1), Val::I64(-1)], &mut result)
        .expect("call to log2-uint failed");
    assert_eq!(result[0].i64(), Some(127));
    assert_eq!(result[1].i64(), Some(0));

    // log2(u64::MAX) is not an error
    log2.call(&mut store, &[Val::I64(-1), Val::I64(0)], &mut result)
        .expect("call to log2-uint failed");
    assert_eq!(result[0].i64(), Some(63));
    assert_eq!(result[1].i64(), Some(0));

    // log2(u128::MAX-u64::MAX) is not an error
    log2.call(&mut store, &[Val::I64(0), Val::I64(-1)], &mut result)
        .expect("call to log2-uint failed");
    assert_eq!(result[0].i64(), Some(127));
    assert_eq!(result[1].i64(), Some(0));
}

#[test]
fn test_log2_int() {
    let (instance, mut store) = load_stdlib().unwrap();
    let log2 = instance.get_func(&mut store, "stdlib.log2-int").unwrap();
    let mut result = [Val::I64(0), Val::I64(0)];

    // log2(0) is an error
    log2.call(&mut store, &[Val::I64(0), Val::I64(0)], &mut result)
        .expect_err("expected log of 0 error");

    // log2(-1) is an error
    log2.call(&mut store, &[Val::I64(-1), Val::I64(-1)], &mut result)
        .expect_err("expected log of negative number error");

    // log2(u64::MAX) is not an error
    log2.call(&mut store, &[Val::I64(-1), Val::I64(0)], &mut result)
        .expect("call to log2-int failed");
    assert_eq!(result[0].i64(), Some(63));
    assert_eq!(result[1].i64(), Some(0));

    // log2(u128::MAX-u64::MAX) is an error
    log2.call(&mut store, &[Val::I64(0), Val::I64(-1)], &mut result)
        .expect_err("expected log of negative number error");
}

#[test]
fn test_sqrti_uint() {
    let (instance, mut store) = load_stdlib().unwrap();
    let sqrti = instance.get_func(&mut store, "stdlib.sqrti-uint").unwrap();
    let mut result = [Val::I64(0), Val::I64(0)];

    // sqrti(0) = 0
    sqrti
        .call(&mut store, &[Val::I64(0), Val::I64(0)], &mut result)
        .expect("call to sqrti-uint failed");
    assert_eq!(result[0].i64(), Some(0));
    assert_eq!(result[1].i64(), Some(0));

    // sqrti(1) = 1
    sqrti
        .call(&mut store, &[Val::I64(1), Val::I64(0)], &mut result)
        .expect("call to sqrti-uint failed");
    assert_eq!(result[0].i64(), Some(1));
    assert_eq!(result[1].i64(), Some(0));

    // sqrti(0xffff_ffff_ffff_ffff) = 0xffff_ffff
    sqrti
        .call(&mut store, &[Val::I64(-1), Val::I64(0)], &mut result)
        .expect("call to sqrti-uint failed");
    assert_eq!(result[0].i64(), Some(0xffff_ffff));
    assert_eq!(result[1].i64(), Some(0));

    // sqrti(0x1_0000_0000_0000_0000) = 0x1_0000_0000
    sqrti
        .call(&mut store, &[Val::I64(0), Val::I64(1)], &mut result)
        .expect("call to sqrti-uint failed");
    assert_eq!(result[0].i64(), Some(0x1_0000_0000));
    assert_eq!(result[1].i64(), Some(0));

    // sqrti(u128::MAX)  = 0xffff_ffff_ffff_ffff
    sqrti
        .call(&mut store, &[Val::I64(-1), Val::I64(-1)], &mut result)
        .expect("call to sqrti-uint failed");
    assert_eq!(result[0].i64(), Some(-1));
    assert_eq!(result[1].i64(), Some(0));
}

#[test]
fn test_sqrti_int() {
    let (instance, mut store) = load_stdlib().unwrap();
    let sqrti = instance.get_func(&mut store, "stdlib.sqrti-int").unwrap();
    let mut result = [Val::I64(0), Val::I64(0)];

    // sqrti(0) = 0
    sqrti
        .call(&mut store, &[Val::I64(0), Val::I64(0)], &mut result)
        .expect("call to sqrti-int failed");
    assert_eq!(result[0].i64(), Some(0));
    assert_eq!(result[1].i64(), Some(0));

    // sqrti(1) = 1
    sqrti
        .call(&mut store, &[Val::I64(1), Val::I64(0)], &mut result)
        .expect("call to sqrti-int failed");
    assert_eq!(result[0].i64(), Some(1));
    assert_eq!(result[1].i64(), Some(0));

    // sqrti(0xffff_ffff_ffff_ffff) = 0xffff_ffff
    sqrti
        .call(&mut store, &[Val::I64(-1), Val::I64(0)], &mut result)
        .expect("call to sqrti-int failed");
    assert_eq!(result[0].i64(), Some(0xffff_ffff));
    assert_eq!(result[1].i64(), Some(0));

    // sqrti(0x1_0000_0000_0000_0000) = 0x1_0000_0000
    sqrti
        .call(&mut store, &[Val::I64(0), Val::I64(1)], &mut result)
        .expect("call to sqrti-int failed");
    assert_eq!(result[0].i64(), Some(0x1_0000_0000));
    assert_eq!(result[1].i64(), Some(0));

    // sqrti(-1) is error
    sqrti
        .call(&mut store, &[Val::I64(-1), Val::I64(-1)], &mut result)
        .expect_err("expected sqrti of negative integer");
}

#[test]
fn bit_not_int() {
    let (instance, mut store) = load_stdlib().unwrap();
    let bitnot = instance.get_func(&mut store, "stdlib.bit-not-int").unwrap();
    let mut result = [Val::I64(0), Val::I64(0)];

    // bit-not(3) = -4
    bitnot
        .call(&mut store, &[Val::I64(3), Val::I64(0)], &mut result)
        .expect("call to bit-not failed");
    assert_eq!(result[0].i64(), Some(-4));
    assert_eq!(result[1].i64(), Some(-1));
}

#[test]
fn pow_uint() {
    let (instance, mut store) = load_stdlib().unwrap();
    let pow = instance.get_func(&mut store, "stdlib.pow-uint").unwrap();
    let mut result = [Val::I64(0), Val::I64(0)];

    // pow(0, 0) == 1
    pow.call(
        &mut store,
        &[Val::I64(0), Val::I64(0), Val::I64(0), Val::I64(0)],
        &mut result,
    )
    .expect("call to pow-uint failed");
    assert_eq!(result[0].unwrap_i64(), 1);
    assert_eq!(result[1].unwrap_i64(), 0);

    // pow(1, 0) == 1
    pow.call(
        &mut store,
        &[Val::I64(1), Val::I64(0), Val::I64(0), Val::I64(0)],
        &mut result,
    )
    .expect("call to pow-uint failed");
    assert_eq!(result[0].unwrap_i64(), 1);
    assert_eq!(result[1].unwrap_i64(), 0);

    // pow(2, 0) == 1
    pow.call(
        &mut store,
        &[Val::I64(2), Val::I64(0), Val::I64(0), Val::I64(0)],
        &mut result,
    )
    .expect("call to pow-uint failed");
    assert_eq!(result[0].unwrap_i64(), 1);
    assert_eq!(result[1].unwrap_i64(), 0);

    // pow(0, 1) == 0
    pow.call(
        &mut store,
        &[Val::I64(0), Val::I64(0), Val::I64(1), Val::I64(0)],
        &mut result,
    )
    .expect("call to pow-uint failed");
    assert_eq!(result[0].unwrap_i64(), 0);
    assert_eq!(result[1].unwrap_i64(), 0);

    // pow(123, 1) == 123
    pow.call(
        &mut store,
        &[Val::I64(123), Val::I64(0), Val::I64(1), Val::I64(0)],
        &mut result,
    )
    .expect("call to pow-uint failed");
    assert_eq!(result[0].unwrap_i64(), 123);
    assert_eq!(result[1].unwrap_i64(), 0);

    // pow(3, 2) == 9
    pow.call(
        &mut store,
        &[Val::I64(3), Val::I64(0), Val::I64(2), Val::I64(0)],
        &mut result,
    )
    .expect("call to pow-uint failed");
    assert_eq!(result[0].unwrap_i64(), 9);
    assert_eq!(result[1].unwrap_i64(), 0);

    // pow(3, 3) == 27
    pow.call(
        &mut store,
        &[Val::I64(3), Val::I64(0), Val::I64(3), Val::I64(0)],
        &mut result,
    )
    .expect("call to pow-uint failed");
    assert_eq!(result[0].unwrap_i64(), 27);
    assert_eq!(result[1].unwrap_i64(), 0);

    // pow(3, 80) = large number
    pow.call(
        &mut store,
        &[Val::I64(3), Val::I64(0), Val::I64(80), Val::I64(0)],
        &mut result,
    )
    .expect("call to pow-uint failed");
    assert_eq!(result[0].unwrap_i64(), 4389419161382147137);
    assert_eq!(result[1].unwrap_i64(), 8012732698178659004);

    // pow(3, 81) overflows
    pow.call(
        &mut store,
        &[Val::I64(3), Val::I64(0), Val::I64(81), Val::I64(0)],
        &mut result,
    )
    .expect_err("expected overflow");

    // pow(2, 127) = 1 << 127
    pow.call(
        &mut store,
        &[Val::I64(2), Val::I64(0), Val::I64(127), Val::I64(0)],
        &mut result,
    )
    .expect("call to pow-uint failed");
    assert_eq!(result[0].unwrap_i64(), 0);
    assert_eq!(result[1].unwrap_i64(), 0x8000000000000000u64 as i64);

    // pow(2, 128) overflows
    pow.call(
        &mut store,
        &[Val::I64(2), Val::I64(0), Val::I64(128), Val::I64(0)],
        &mut result,
    )
    .expect_err("expected overflow");
}

#[test]
fn pow_int() {
    let (instance, mut store) = load_stdlib().unwrap();
    let pow = instance.get_func(&mut store, "stdlib.pow-int").unwrap();
    let mut result = [Val::I64(0), Val::I64(0)];

    // pow(0, 0) == 1
    pow.call(
        &mut store,
        &[Val::I64(0), Val::I64(0), Val::I64(0), Val::I64(0)],
        &mut result,
    )
    .expect("call to pow-int failed");
    assert_eq!(result[0].unwrap_i64(), 1);
    assert_eq!(result[1].unwrap_i64(), 0);

    // pow(1, 0) == 1
    pow.call(
        &mut store,
        &[Val::I64(1), Val::I64(0), Val::I64(0), Val::I64(0)],
        &mut result,
    )
    .expect("call to pow-int failed");
    assert_eq!(result[0].unwrap_i64(), 1);
    assert_eq!(result[1].unwrap_i64(), 0);

    // pow(2, 0) == 1
    pow.call(
        &mut store,
        &[Val::I64(2), Val::I64(0), Val::I64(0), Val::I64(0)],
        &mut result,
    )
    .expect("call to pow-int failed");
    assert_eq!(result[0].unwrap_i64(), 1);
    assert_eq!(result[1].unwrap_i64(), 0);

    // pow(0, 1) == 0
    pow.call(
        &mut store,
        &[Val::I64(0), Val::I64(0), Val::I64(1), Val::I64(0)],
        &mut result,
    )
    .expect("call to pow-int failed");
    assert_eq!(result[0].unwrap_i64(), 0);
    assert_eq!(result[1].unwrap_i64(), 0);

    // pow(123, 1) == 123
    pow.call(
        &mut store,
        &[Val::I64(123), Val::I64(0), Val::I64(1), Val::I64(0)],
        &mut result,
    )
    .expect("call to pow-int failed");
    assert_eq!(result[0].unwrap_i64(), 123);
    assert_eq!(result[1].unwrap_i64(), 0);

    // pow(3, 2) == 9
    pow.call(
        &mut store,
        &[Val::I64(3), Val::I64(0), Val::I64(2), Val::I64(0)],
        &mut result,
    )
    .expect("call to pow-int failed");
    assert_eq!(result[0].unwrap_i64(), 9);
    assert_eq!(result[1].unwrap_i64(), 0);

    // pow(3, 3) == 27
    pow.call(
        &mut store,
        &[Val::I64(3), Val::I64(0), Val::I64(3), Val::I64(0)],
        &mut result,
    )
    .expect("call to pow-int failed");
    assert_eq!(result[0].unwrap_i64(), 27);
    assert_eq!(result[1].unwrap_i64(), 0);

    // pow(3, 80) = large number
    pow.call(
        &mut store,
        &[Val::I64(3), Val::I64(0), Val::I64(80), Val::I64(0)],
        &mut result,
    )
    .expect("call to pow-int failed");
    assert_eq!(result[0].unwrap_i64(), 4389419161382147137);
    assert_eq!(result[1].unwrap_i64(), 8012732698178659004);

    // pow(3, 81) overflows
    pow.call(
        &mut store,
        &[Val::I64(3), Val::I64(0), Val::I64(81), Val::I64(0)],
        &mut result,
    )
    .expect_err("expected overflow");

    // pow(2, 126) = 1 << 126
    pow.call(
        &mut store,
        &[Val::I64(2), Val::I64(0), Val::I64(126), Val::I64(0)],
        &mut result,
    )
    .expect("call to pow-uint failed");
    assert_eq!(result[0].unwrap_i64(), 0);
    assert_eq!(result[1].unwrap_i64(), 0x4000000000000000u64 as i64);

    // pow(2, 127) overflows
    pow.call(
        &mut store,
        &[Val::I64(2), Val::I64(0), Val::I64(127), Val::I64(0)],
        &mut result,
    )
    .expect_err("expected overflow");

    // pow(-2, 1) == -2
    pow.call(
        &mut store,
        &[Val::I64(-2), Val::I64(-1), Val::I64(1), Val::I64(0)],
        &mut result,
    )
    .expect("call to pow-uint failed");
    assert_eq!(result[0].unwrap_i64(), -2);
    assert_eq!(result[1].unwrap_i64(), -1);

    // pow(-2, 2) == 4
    pow.call(
        &mut store,
        &[Val::I64(-2), Val::I64(-1), Val::I64(2), Val::I64(0)],
        &mut result,
    )
    .expect("call to pow-uint failed");
    assert_eq!(result[0].unwrap_i64(), 4);
    assert_eq!(result[1].unwrap_i64(), 0);

    // pow(-2, 126) == 0x40000000000000000000000000000000
    pow.call(
        &mut store,
        &[Val::I64(-2), Val::I64(-1), Val::I64(126), Val::I64(0)],
        &mut result,
    )
    .expect("call to pow-uint failed");
    assert_eq!(result[0].unwrap_i64(), 0);
    assert_eq!(result[1].unwrap_i64(), 0x4000000000000000u64 as i64);

    // pow(-2, 127) == i128::MIN
    pow.call(
        &mut store,
        &[Val::I64(-2), Val::I64(-1), Val::I64(127), Val::I64(0)],
        &mut result,
    )
    .expect("call to pow-uint failed");
    assert_eq!(result[0].unwrap_i64(), 0);
    assert_eq!(result[1].unwrap_i64(), 0x8000000000000000u64 as i64);

    // pow(-3, 2) = 9
    pow.call(
        &mut store,
        &[Val::I64(-3), Val::I64(-1), Val::I64(2), Val::I64(0)],
        &mut result,
    )
    .expect("call to pow-int failed");
    assert_eq!(result[0].unwrap_i64(), 9);
    assert_eq!(result[1].unwrap_i64(), 0);

    // pow(-3, 3) = -27
    pow.call(
        &mut store,
        &[Val::I64(-3), Val::I64(-1), Val::I64(3), Val::I64(0)],
        &mut result,
    )
    .expect("call to pow-int failed");
    assert_eq!(result[0].unwrap_i64(), -27);
    assert_eq!(result[1].unwrap_i64(), -1);

    // edge case i128::MIN^1 is ok
    pow.call(
        &mut store,
        &[
            Val::I64(0),
            Val::I64(0x8000000000000000u64 as i64),
            Val::I64(1),
            Val::I64(0),
        ],
        &mut result,
    )
    .expect("call to pow-int failed");
    assert_eq!(result[0].unwrap_i64(), 0);
    assert_eq!(result[1].unwrap_i64(), 0x8000000000000000u64 as i64);

    // edge case i128::MIN^2 overflows
    pow.call(
        &mut store,
        &[
            Val::I64(0),
            Val::I64(0x8000000000000000u64 as i64),
            Val::I64(2),
            Val::I64(0),
        ],
        &mut result,
    )
    .expect_err("expected overflow");

    // 2^0x10000000000000000 overflows (correct branch overflows, issue #356)
    pow.call(
        &mut store,
        &[Val::I64(2), Val::I64(0), Val::I64(0), Val::I64(1)],
        &mut result,
    )
    .expect_err("expected overflow");
}

#[test]
fn sha256_prerequisite() {
    let (instance, mut store) = load_stdlib().unwrap();

    let memory = instance
        .get_memory(&mut store, "memory")
        .expect("Could not find memory");

    // check initial hash values in memory at offset 0 with length 32
    let mut buffer = vec![0u8; 32];
    memory
        .read(&mut store, 0, &mut buffer)
        .expect("Could not read initial hash from memory");
    let buffer: Vec<_> = buffer
        .chunks_exact(4)
        .map(|i| u32::from_le_bytes(i.try_into().unwrap()))
        .collect();
    assert_eq!(
        buffer,
        [
            0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
            0x5be0cd19
        ]
    );

    // check K values in memory at offset 32 with length 256
    let mut buffer = vec![0u8; 256];
    memory
        .read(&mut store, 32, &mut buffer)
        .expect("could not read K values from memory");
    let buffer: Vec<_> = buffer
        .chunks_exact(4)
        .map(|i| i32::from_le_bytes(i.try_into().unwrap()))
        .collect();
    assert_eq!(
        buffer,
        [
            1116352408,
            1899447441,
            -1245643825,
            -373957723,
            961987163,
            1508970993,
            -1841331548,
            -1424204075,
            -670586216,
            310598401,
            607225278,
            1426881987,
            1925078388,
            -2132889090,
            -1680079193,
            -1046744716,
            -459576895,
            -272742522,
            264347078,
            604807628,
            770255983,
            1249150122,
            1555081692,
            1996064986,
            -1740746414,
            -1473132947,
            -1341970488,
            -1084653625,
            -958395405,
            -710438585,
            113926993,
            338241895,
            666307205,
            773529912,
            1294757372,
            1396182291,
            1695183700,
            1986661051,
            -2117940946,
            -1838011259,
            -1564481375,
            -1474664885,
            -1035236496,
            -949202525,
            -778901479,
            -694614492,
            -200395387,
            275423344,
            430227734,
            506948616,
            659060556,
            883997877,
            958139571,
            1322822218,
            1537002063,
            1747873779,
            1955562222,
            2024104815,
            -2067236844,
            -1933114872,
            -1866530822,
            -1538233109,
            -1090935817,
            -965641998
        ]
    );
}

#[test]
fn sha256_buf() {
    let (instance, mut store) = load_stdlib().unwrap();
    let memory = instance
        .get_memory(&mut store, "memory")
        .expect("Could not find memory");

    let sha256 = instance.get_func(&mut store, "stdlib.sha256-buf").unwrap();
    let mut result = [Val::I32(0), Val::I32(0)];

    // This algo needs space on the stack,
    // we move the initial value of $stack-pointer
    // to a random one where it wouldn't matter
    let stack_pointer = instance.get_global(&mut store, "stack-pointer").unwrap();
    stack_pointer.set(&mut store, Val::I32(1500)).unwrap();

    // The offset where the result hash will be written to
    let res_offset = 3000i32;
    let workspace_offset = 2048i32;

    // test with "Hello, World!", which requires only one pass
    let text = b"Hello, World!";
    memory
        .write(&mut store, END_OF_STANDARD_DATA as usize, text)
        .expect("Should be able to write to memory");

    sha256
        .call(
            &mut store,
            &[
                Val::I32(END_OF_STANDARD_DATA as i32),
                Val::I32(text.len() as i32),
                res_offset.into(),
                workspace_offset.into(),
            ],
            &mut result,
        )
        .expect("call to sha256-buf failed");
    assert_eq!(result[0].unwrap_i32(), res_offset);
    assert_eq!(result[1].unwrap_i32(), 32);

    let mut buffer = vec![0u8; result[1].unwrap_i32() as usize];
    memory
        .read(&mut store, result[0].unwrap_i32() as usize, &mut buffer)
        .expect("could not read resulting hash from memory");
    let expected_result =
        Vec::from_hex("dffd6021bb2bd5b0af676290809ec3a53191dd81c7f70a4b28688a362182986f").unwrap();
    assert_eq!(&buffer, &expected_result);

    // test with Lorem Ipsum, which will require multiple passes
    let text = b"Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua.";
    memory
        .write(&mut store, END_OF_STANDARD_DATA as usize, text)
        .expect("Should be able to write to memory");

    sha256
        .call(
            &mut store,
            &[
                Val::I32(END_OF_STANDARD_DATA as i32),
                Val::I32(text.len() as i32),
                res_offset.into(),
                workspace_offset.into(),
            ],
            &mut result,
        )
        .expect("call to sha256-buf failed");
    assert_eq!(result[0].unwrap_i32(), res_offset);
    assert_eq!(result[1].unwrap_i32(), 32);

    let mut buffer = vec![0u8; result[1].unwrap_i32() as usize];
    memory
        .read(&mut store, result[0].unwrap_i32() as usize, &mut buffer)
        .expect("could not read resulting hash from memory");
    let expected_result =
        Vec::from_hex("973153f86ec2da1748e63f0cf85b89835b42f8ee8018c549868a1308a19f6ca3").unwrap();
    assert_eq!(&buffer, &expected_result);

    // test with buffer of size 55, the limit between 1 and 2 blocks
    let text = &[0; 55];
    memory
        .write(&mut store, END_OF_STANDARD_DATA as usize, text)
        .expect("Should be able to write to memory");

    sha256
        .call(
            &mut store,
            &[
                Val::I32(END_OF_STANDARD_DATA as i32),
                Val::I32(text.len() as i32),
                res_offset.into(),
                workspace_offset.into(),
            ],
            &mut result,
        )
        .expect("call to sha256-buf failed");
    assert_eq!(result[0].unwrap_i32(), res_offset);
    assert_eq!(result[1].unwrap_i32(), 32);

    let mut buffer = vec![0u8; result[1].unwrap_i32() as usize];
    memory
        .read(&mut store, result[0].unwrap_i32() as usize, &mut buffer)
        .expect("could not read resulting hash from memory");
    let expected_result =
        Vec::from_hex("02779466cdec163811d078815c633f21901413081449002f24aa3e80f0b88ef7").unwrap();
    assert_eq!(&buffer, &expected_result);
}

#[test]
fn sha256_int() {
    let (instance, mut store) = load_stdlib().unwrap();
    let memory = instance
        .get_memory(&mut store, "memory")
        .expect("Could not find memory");

    let sha256 = instance.get_func(&mut store, "stdlib.sha256-int").unwrap();
    let mut result = [Val::I32(0), Val::I32(0)];

    // This algo needs space on the stack,
    // we move the initial value of $stack-pointer
    // to a random one where it wouldn't matter
    let stack_pointer = instance.get_global(&mut store, "stack-pointer").unwrap();
    stack_pointer.set(&mut store, Val::I32(1500)).unwrap();

    // The offset where the result hash will be written to
    let res_offset = 3000i32;
    let workspace_offset = 2048i32;

    // Test on 0xfeedc0dedeadbeefcafed00dcafebabe
    sha256
        .call(
            &mut store,
            &[
                Val::I64(0xcafed00dcafebabe_u64 as i64),
                Val::I64(0xfeedc0dedeadbeef_u64 as i64),
                res_offset.into(),
                workspace_offset.into(),
            ],
            &mut result,
        )
        .expect("call to sha256-int failed");
    assert_eq!(result[0].unwrap_i32(), res_offset);
    assert_eq!(result[1].unwrap_i32(), 32);

    let mut buffer = vec![0u8; result[1].unwrap_i32() as usize];
    memory
        .read(&mut store, result[0].unwrap_i32() as usize, &mut buffer)
        .expect("could not read resulting hash from memory");
    let expected_result =
        Vec::from_hex("2099af4a709288ebee47cad01952a37d2d04b8003b3f4f2d520a94f3fdfe4210").unwrap();
    assert_eq!(&buffer, &expected_result);
}

#[test]
fn hash160_prerequisite() {
    let (instance, mut store) = load_stdlib().unwrap();

    let memory = instance
        .get_memory(&mut store, "memory")
        .expect("Could not find memory");

    // check selection of message word at offset 288 with size 80
    let mut buffer = vec![0u8; 80];
    memory
        .read(&mut store, 288, &mut buffer)
        .expect("Could not read initial hash from memory");
    assert_eq!(
        buffer,
        [
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 7, 4, 13, 1, 10, 6, 15, 3, 12, 0,
            9, 5, 2, 14, 11, 8, 3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12, 1, 9, 11, 10,
            0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2, 4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6,
            15, 13
        ]
    );

    // check parallel selection of message word at offset 368 with size 80
    let mut buffer = vec![0u8; 80];
    memory
        .read(&mut store, 368, &mut buffer)
        .expect("Could not read initial hash from memory");
    assert_eq!(
        buffer,
        [
            5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12, 6, 11, 3, 7, 0, 13, 5, 10, 14,
            15, 8, 12, 4, 9, 1, 2, 15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13, 8, 6, 4,
            1, 3, 11, 15, 0, 5, 12, 2, 13, 9, 7, 10, 14, 12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14,
            0, 3, 9, 11
        ]
    );

    // check left-rotation value at offset 448 with size 80
    let mut buffer = vec![0u8; 80];
    memory
        .read(&mut store, 448, &mut buffer)
        .expect("Could not read initial hash from memory");
    assert_eq!(
        buffer,
        [
            11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8, 7, 6, 8, 13, 11, 9, 7, 15, 7,
            12, 15, 9, 11, 7, 13, 12, 11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5, 11,
            12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12, 9, 15, 5, 11, 6, 8, 13, 12, 5, 12,
            13, 14, 11, 8, 5, 6
        ]
    );

    // check parallel left-rotation value at offset 528 with size 80
    let mut buffer = vec![0u8; 80];
    memory
        .read(&mut store, 528, &mut buffer)
        .expect("Could not read initial hash from memory");
    assert_eq!(
        buffer,
        [
            8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6, 9, 13, 15, 7, 12, 8, 9, 11, 7,
            7, 12, 7, 6, 15, 13, 11, 9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5, 15, 5,
            8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5, 15, 8, 8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6,
            5, 15, 13, 11, 11
        ]
    );

    // check constants K values at offset 608 with size 20
    let mut buffer = vec![0u8; 20];
    memory
        .read(&mut store, 608, &mut buffer)
        .expect("Could not read initial hash from memory");
    let buffer: Vec<_> = buffer
        .chunks_exact(4)
        .map(|i| u32::from_le_bytes(i.try_into().unwrap()))
        .collect();
    assert_eq!(buffer, [0, 0x5a827999, 0x6ed9eba1, 0x8f1bbcdc, 0xa953fd4e]);

    // check parallel constants K' values at offset 628 with size 20
    let mut buffer = vec![0u8; 20];
    memory
        .read(&mut store, 628, &mut buffer)
        .expect("Could not read initial hash from memory");
    let buffer: Vec<_> = buffer
        .chunks_exact(4)
        .map(|i| u32::from_le_bytes(i.try_into().unwrap()))
        .collect();
    assert_eq!(buffer, [0x50a28be6, 0x5c4dd124, 0x6d703ef3, 0x7a6d76e9, 0]);
}

#[test]
fn hash160_buf() {
    let (instance, mut store) = load_stdlib().unwrap();
    let memory = instance
        .get_memory(&mut store, "memory")
        .expect("Could not find memory");

    let hash160 = instance.get_func(&mut store, "stdlib.hash160-buf").unwrap();
    let mut result = [Val::I32(0), Val::I32(0)];

    // This algo needs space on the stack,
    // we move the initial value of $stack-pointer
    // to a random one where it wouldn't matter
    let stack_pointer = instance.get_global(&mut store, "stack-pointer").unwrap();
    stack_pointer.set(&mut store, Val::I32(1500)).unwrap();

    // The offset where the result hash will be written to
    let res_offset = 3000i32;
    let workspace_offset = 2048i32;

    // test with "Hello, World!"
    let text = b"Hello, World!";
    memory
        .write(&mut store, END_OF_STANDARD_DATA as usize, text)
        .expect("Should be able to write to memory");

    hash160
        .call(
            &mut store,
            &[
                Val::I32(END_OF_STANDARD_DATA as i32),
                Val::I32(text.len() as i32),
                res_offset.into(),
                workspace_offset.into(),
            ],
            &mut result,
        )
        .expect("call to hash160-buf failed");
    assert_eq!(result[0].unwrap_i32(), res_offset);
    assert_eq!(result[1].unwrap_i32(), 20);

    let mut buffer = vec![0u8; result[1].unwrap_i32() as usize];
    memory
        .read(&mut store, result[0].unwrap_i32() as usize, &mut buffer)
        .expect("could not read resulting hash from memory");
    let expected_result = Vec::from_hex("e3c83f9d9adb8fcbccc4399da8ebe609ba4352e4").unwrap();
    assert_eq!(&buffer, &expected_result);

    // test with Lorem Ipsum
    let text = b"Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua.";
    memory
        .write(&mut store, END_OF_STANDARD_DATA as usize, text)
        .expect("Should be able to write to memory");

    hash160
        .call(
            &mut store,
            &[
                Val::I32(END_OF_STANDARD_DATA as i32),
                Val::I32(text.len() as i32),
                res_offset.into(),
                workspace_offset.into(),
            ],
            &mut result,
        )
        .expect("call to hash160-buf failed");
    assert_eq!(result[0].unwrap_i32(), res_offset);
    assert_eq!(result[1].unwrap_i32(), 20);

    let mut buffer = vec![0u8; result[1].unwrap_i32() as usize];
    memory
        .read(&mut store, result[0].unwrap_i32() as usize, &mut buffer)
        .expect("could not read resulting hash from memory");
    let expected_result = Vec::from_hex("d6f2b43388048a339abd861be2babd817e3717cd").unwrap();
    assert_eq!(&buffer, &expected_result);
}

#[test]
fn hash160_int() {
    let (instance, mut store) = load_stdlib().unwrap();
    let memory = instance
        .get_memory(&mut store, "memory")
        .expect("Could not find memory");

    let hash160 = instance.get_func(&mut store, "stdlib.hash160-int").unwrap();
    let mut result = [Val::I32(0), Val::I32(0)];

    // This algo needs space on the stack,
    // we move the initial value of $stack-pointer
    // to a random one where it wouldn't matter
    let stack_pointer = instance.get_global(&mut store, "stack-pointer").unwrap();
    stack_pointer.set(&mut store, Val::I32(1500)).unwrap();

    // The offset where the result hash will be written to
    let res_offset = 3000i32;
    let workspace_offset = 2048i32;

    // Test on 0xfeedc0dedeadbeefcafed00dcafebabe
    hash160
        .call(
            &mut store,
            &[
                Val::I64(0xcafed00dcafebabe_u64 as i64),
                Val::I64(0xfeedc0dedeadbeef_u64 as i64),
                res_offset.into(),
                workspace_offset.into(),
            ],
            &mut result,
        )
        .expect("call to hash160-int failed");
    assert_eq!(result[0].unwrap_i32(), res_offset);
    assert_eq!(result[1].unwrap_i32(), 20);

    let mut buffer = vec![0u8; result[1].unwrap_i32() as usize];
    memory
        .read(&mut store, result[0].unwrap_i32() as usize, &mut buffer)
        .expect("could not read resulting hash from memory");
    let expected_result = Vec::from_hex("aeae89e821d429940dff0d3412377815dae9ab07").unwrap();
    assert_eq!(&buffer, &expected_result);
}

#[test]
fn store_i32_be() {
    let (instance, mut store) = load_stdlib().unwrap();
    let store_i32_be = instance
        .get_func(&mut store, "stdlib.store-i32-be")
        .unwrap();
    let mut result = [];

    // Write to a random unused place in the memory
    store_i32_be
        .call(
            &mut store,
            &[Val::I32(1500), Val::I32(0x01234567)],
            &mut result,
        )
        .expect("call to store-i32-be failed");

    let memory = instance
        .get_memory(&mut store, "memory")
        .expect("Could not find memory");

    // check value of memory at offset 1500 with size 4
    let mut buffer = vec![0u8; 4];
    memory
        .read(&mut store, 1500, &mut buffer)
        .expect("Could not read value from memory");
    assert_eq!(buffer, [0x01, 0x23, 0x45, 0x67]);
}

#[test]
fn store_i64_be() {
    let (instance, mut store) = load_stdlib().unwrap();
    let store_i64_be = instance
        .get_func(&mut store, "stdlib.store-i64-be")
        .unwrap();
    let mut result = [];

    // Write to a random unused place in the memory
    store_i64_be
        .call(
            &mut store,
            &[Val::I32(1500), Val::I64(0x0123_4567_89ab_cdef)],
            &mut result,
        )
        .expect("call to store-i64-be failed");

    let memory = instance
        .get_memory(&mut store, "memory")
        .expect("Could not find memory");

    // check value of memory at offset 1500 with size 8
    let mut buffer = vec![0u8; 8];
    memory
        .read(&mut store, 1500, &mut buffer)
        .expect("Could not read value from memory");
    assert_eq!(buffer, [0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef]);
}

#[test]
fn buff_to_uint_be() {
    let (instance, mut store) = load_stdlib().unwrap();

    let memory = instance
        .get_memory(&mut store, "memory")
        .expect("Could not find memory");

    let buff_to_uint_be = instance
        .get_func(&mut store, "stdlib.buff-to-uint-be")
        .unwrap();
    let mut result = [Val::I64(0), Val::I64(0)];

    let mut test_buff = |buf: &[u8], expected_lo: u64, expected_hi: u64| {
        memory
            .write(&mut store, 1500, buf)
            .expect("Could not write to memory");
        buff_to_uint_be
            .call(
                &mut store,
                &[Val::I32(1500), Val::I32(buf.len() as i32)],
                &mut result,
            )
            .expect("call to buff-to-uint-be failed");
        assert_eq!(result[0].unwrap_i64(), expected_lo as i64);
        assert_eq!(result[1].unwrap_i64(), expected_hi as i64);
    };

    // Empty buffer == 0
    test_buff(&[], 0, 0);

    // 0x01
    test_buff(&[1], 1, 0);

    // 0x0102
    test_buff(&[1, 2], 0x0102, 0);

    // 0x0102030405060708
    test_buff(&[1, 2, 3, 4, 5, 6, 7, 8], 0x0102030405060708, 0);

    // 0x010203040506070809
    test_buff(&[1, 2, 3, 4, 5, 6, 7, 8, 9], 0x0203040506070809, 0x01);

    // 0x0102030405060708090a0b0c0d0e0f10
    test_buff(
        &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16],
        0x090a0b0c0d0e0f10,
        0x0102030405060708,
    );

    // Fail for buffer with length > 16
    let buf = [0u8; 17];
    memory
        .write(&mut store, 1500, &buf)
        .expect("Could not write to memory");
    buff_to_uint_be
        .call(
            &mut store,
            &[Val::I32(1500), Val::I32(buf.len() as i32)],
            &mut result,
        )
        .expect_err("expected runtime error");
}

#[test]
fn buff_to_uint_le() {
    let (instance, mut store) = load_stdlib().unwrap();

    let memory = instance
        .get_memory(&mut store, "memory")
        .expect("Could not find memory");

    let buff_to_uint_le = instance
        .get_func(&mut store, "stdlib.buff-to-uint-le")
        .unwrap();
    let mut result = [Val::I64(0), Val::I64(0)];

    let mut test_buff = |buf: &[u8], expected_lo: u64, expected_hi: u64| {
        memory
            .write(&mut store, 1500, buf)
            .expect("Could not write to memory");
        buff_to_uint_le
            .call(
                &mut store,
                &[Val::I32(1500), Val::I32(buf.len() as i32)],
                &mut result,
            )
            .expect("call to buff-to-uint-be failed");
        assert_eq!(result[0].unwrap_i64(), expected_lo as i64);
        assert_eq!(result[1].unwrap_i64(), expected_hi as i64);
    };

    // Empty buffer == 0
    test_buff(&[], 0, 0);

    // 0x01
    test_buff(&[1], 1, 0);

    // 0x0102
    test_buff(&[1, 2], 0x0201, 0);

    // 0x0102030405060708
    test_buff(&[1, 2, 3, 4, 5, 6, 7, 8], 0x0807060504030201, 0);

    // 0x010203040506070809
    test_buff(&[1, 2, 3, 4, 5, 6, 7, 8, 9], 0x0807060504030201, 0x09);

    // 0x0102030405060708090a0b0c0d0e0f10
    test_buff(
        &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16],
        0x0807060504030201,
        0x100f0e0d0c0b0a09,
    );

    // Fail for buffer with length > 16
    let buf = [0u8; 17];
    memory
        .write(&mut store, 1500, &buf)
        .expect("Could not write to memory");
    buff_to_uint_le
        .call(
            &mut store,
            &[Val::I32(1500), Val::I32(buf.len() as i32)],
            &mut result,
        )
        .expect_err("expected runtime error");
}

#[test]
fn string_to_uint() {
    let (instance, mut store) = load_stdlib().unwrap();

    let memory = instance
        .get_memory(&mut store, "memory")
        .expect("Could not find memory");

    let conv = instance
        .get_func(&mut store, "stdlib.string-to-uint")
        .unwrap();
    let mut result = [Val::I32(0), Val::I64(0), Val::I64(0)];

    let mut test_str = |string: &str, expected_opt: i32, expected_lo: i64, expected_hi: i64| {
        memory
            .write(&mut store, 1500, string.as_bytes())
            .expect("Could not write to memory");
        conv.call(
            &mut store,
            &[Val::I32(1500), Val::I32(string.len() as i32)],
            &mut result,
        )
        .expect("call to string-to-uint failed");
        assert_eq!(result[0].unwrap_i32(), expected_opt);
        assert_eq!(result[1].unwrap_i64(), expected_lo);
        assert_eq!(result[2].unwrap_i64(), expected_hi);
    };

    // Fails with empty string
    test_str("", 0, 0, 0);

    // Basic tests only using low bytes
    test_str("0", 1, 0, 0);
    test_str("1", 1, 1, 0);
    test_str("42", 1, 42, 0);
    test_str("1024", 1, 1024, 0);

    // Basic tests with big numbers
    test_str("184467440737095516156789", 1, -3211, 9999);
    test_str(
        "374467440737095681245698132",
        1,
        -6666426393504524204,
        20299920,
    );

    // Tests with number between 64 and 65 bits
    let n = u64::MAX as u128;
    for i in -5..=5 {
        test_str(
            &n.checked_add_signed(i).unwrap().to_string(),
            1,
            (i - 1) as i64,
            (i > 0) as i64,
        );
    }

    // Tests with number close to u128::MAX
    let n = u128::MAX - 10;
    for i in 0..=10 {
        test_str(&(n + i).to_string(), 1, -11 + i as i64, -1);
    }

    // None with too big numbers
    test_str("340282366920938463463374607431768211456", 0, 0, 0);
    test_str("1000000000000000000000000000000000000000", 0, 0, 0);

    // None with invalid inputs
    test_str("a", 0, 0, 0);
    test_str("123a", 0, 0, 0);
    test_str("12v345", 0, 0, 0);
    test_str("340282366920938463463374607431768211455!", 0, 0, 0)
}

#[test]
fn string_to_int() {
    let (instance, mut store) = load_stdlib().unwrap();

    let memory = instance
        .get_memory(&mut store, "memory")
        .expect("Could not find memory");

    let conv = instance
        .get_func(&mut store, "stdlib.string-to-int")
        .unwrap();
    let mut result = [Val::I32(0), Val::I64(0), Val::I64(0)];

    let mut test_str = |string: &str, expected_opt: i32, expected_lo: i64, expected_hi: i64| {
        memory
            .write(&mut store, 1500, string.as_bytes())
            .expect("Could not write to memory");
        conv.call(
            &mut store,
            &[Val::I32(1500), Val::I32(string.len() as i32)],
            &mut result,
        )
        .expect("call to buff-to-uint-be failed");
        assert_eq!(result[0].unwrap_i32(), expected_opt);
        assert_eq!(result[1].unwrap_i64(), expected_lo);
        assert_eq!(result[2].unwrap_i64(), expected_hi);
    };

    // Fails with empty string
    test_str("", 0, 0, 0);

    // Basic tests only using low bytes
    test_str("0", 1, 0, 0);
    test_str("1", 1, 1, 0);
    test_str("42", 1, 42, 0);
    test_str("1024", 1, 1024, 0);

    // Basic tests with big numbers
    test_str("184467440737095516156789", 1, -3211, 9999);
    test_str(
        "374467440737095681245698132",
        1,
        -6666426393504524204,
        20299920,
    );

    // Tests with negative numbers
    test_str("-0", 1, 0, 0);
    test_str("-1", 1, -1, -1);
    test_str("-1024", 1, -1024, -1);
    test_str("-184467440737095516156789", 1, 3211, -10000);
    test_str(
        "-37446744073709568124569813",
        1,
        -1178031768020502741,
        -2029993,
    );

    // Test with biggest valid int
    test_str(&i128::MIN.to_string(), 1, 0, -9223372036854775808);
    test_str(&i128::MAX.to_string(), 1, -1, 9223372036854775807);

    // Test with valid uint but invalid int
    test_str(
        &(1u128 << 127).to_string(), // abs(i127::MIN)
        0,
        0,
        0,
    );
    test_str(&u128::MAX.to_string(), 0, 0, 0);

    // None with invalid inputs
    test_str("a", 0, 0, 0);
    test_str("-a", 0, 0, 0);
    test_str("123a", 0, 0, 0);
    test_str("12v345", 0, 0, 0);
    test_str("-340282366920938463463374607431768211455!", 0, 0, 0)
}

#[test]
fn utf8_to_uint() {
    let (instance, mut store) = load_stdlib().unwrap();

    let memory = instance
        .get_memory(&mut store, "memory")
        .expect("Could not find memory");

    let conv = instance
        .get_func(&mut store, "stdlib.utf8-to-uint")
        .unwrap();
    let mut result = [Val::I32(0), Val::I64(0), Val::I64(0)];

    let mut test_str = |string: &str, expected_opt: i32, expected_lo: i64, expected_hi: i64| {
        let string: Vec<_> = string
            .bytes()
            .flat_map(|b| (b as u32).to_be_bytes())
            .collect();
        memory
            .write(&mut store, 1500, &string)
            .expect("Could not write to memory");
        conv.call(
            &mut store,
            &[Val::I32(1500), Val::I32(string.len() as i32)],
            &mut result,
        )
        .expect("call to string-to-uint failed");
        assert_eq!(result[0].unwrap_i32(), expected_opt);
        assert_eq!(result[1].unwrap_i64(), expected_lo);
        assert_eq!(result[2].unwrap_i64(), expected_hi);
    };

    // Fails with empty string
    test_str("", 0, 0, 0);

    // Basic tests only using low bytes
    test_str("0", 1, 0, 0);
    test_str("1", 1, 1, 0);
    test_str("42", 1, 42, 0);
    test_str("1024", 1, 1024, 0);

    // Basic tests with big numbers
    test_str("184467440737095516156789", 1, -3211, 9999);
    test_str(
        "374467440737095681245698132",
        1,
        -6666426393504524204,
        20299920,
    );

    // Tests with number between 64 and 65 bits
    let n = u64::MAX as u128;
    for i in -5..=5 {
        test_str(
            &n.checked_add_signed(i).unwrap().to_string(),
            1,
            (i - 1) as i64,
            (i > 0) as i64,
        );
    }

    // Tests with number close to u128::MAX
    let n = u128::MAX - 10;
    for i in 0..=10 {
        test_str(&(n + i).to_string(), 1, -11 + i as i64, -1);
    }

    // None with too big numbers
    test_str("340282366920938463463374607431768211456", 0, 0, 0);
    test_str("1000000000000000000000000000000000000000", 0, 0, 0);

    // None with invalid inputs
    test_str("a", 0, 0, 0);
    test_str("123a", 0, 0, 0);
    test_str("12v345", 0, 0, 0);
    test_str("340282366920938463463374607431768211455!", 0, 0, 0);

    // valid number with a utf8 char -> 123 and something that starts with a valid number, but is actually a utf8 thingy
    let string = vec![49, 0, 0, 0, 50, 0, 0, 0, 51, 0, 0, 0, 52, 1, 0, 0];
    memory
        .write(&mut store, 1500, &string)
        .expect("Could not write to memory");
    conv.call(
        &mut store,
        &[Val::I32(1500), Val::I32(string.len() as i32)],
        &mut result,
    )
    .expect("call to string-to-uint failed");
    assert_eq!(result[0].unwrap_i32(), 0);
    assert_eq!(result[1].unwrap_i64(), 0);
    assert_eq!(result[2].unwrap_i64(), 0);
}

#[test]
fn utf8_to_int() {
    let (instance, mut store) = load_stdlib().unwrap();

    let memory = instance
        .get_memory(&mut store, "memory")
        .expect("Could not find memory");

    let conv = instance.get_func(&mut store, "stdlib.utf8-to-int").unwrap();
    let mut result = [Val::I32(0), Val::I64(0), Val::I64(0)];

    let mut test_str = |string: &str, expected_opt: i32, expected_lo: i64, expected_hi: i64| {
        let string: Vec<_> = string
            .bytes()
            .flat_map(|b| (b as u32).to_be_bytes())
            .collect();
        memory
            .write(&mut store, 1500, &string)
            .expect("Could not write to memory");
        conv.call(
            &mut store,
            &[Val::I32(1500), Val::I32(string.len() as i32)],
            &mut result,
        )
        .expect("call to buff-to-uint-be failed");
        assert_eq!(result[0].unwrap_i32(), expected_opt);
        assert_eq!(result[1].unwrap_i64(), expected_lo);
        assert_eq!(result[2].unwrap_i64(), expected_hi);
    };

    // Fails with empty string
    test_str("", 0, 0, 0);

    // Basic tests only using low bytes
    test_str("0", 1, 0, 0);
    test_str("1", 1, 1, 0);
    test_str("42", 1, 42, 0);
    test_str("1024", 1, 1024, 0);

    // Basic tests with big numbers
    test_str("184467440737095516156789", 1, -3211, 9999);
    test_str(
        "374467440737095681245698132",
        1,
        -6666426393504524204,
        20299920,
    );

    // Tests with negative numbers
    test_str("-0", 1, 0, 0);
    test_str("-1", 1, -1, -1);
    test_str("-1024", 1, -1024, -1);
    test_str("-184467440737095516156789", 1, 3211, -10000);
    test_str(
        "-37446744073709568124569813",
        1,
        -1178031768020502741,
        -2029993,
    );

    // Test with biggest valid int
    test_str(&i128::MIN.to_string(), 1, 0, -9223372036854775808);
    test_str(&i128::MAX.to_string(), 1, -1, 9223372036854775807);

    // Test with valid uint but invalid int
    test_str(
        &(1u128 << 127).to_string(), // abs(i127::MIN)
        0,
        0,
        0,
    );
    test_str(&u128::MAX.to_string(), 0, 0, 0);

    // None with invalid inputs
    test_str("a", 0, 0, 0);
    test_str("-a", 0, 0, 0);
    test_str("123a", 0, 0, 0);
    test_str("12v345", 0, 0, 0);
    test_str("-340282366920938463463374607431768211455!", 0, 0, 0);

    // valid number with a utf8 char -> -123 and something that starts with a valid number, but is actually a utf8 thingy
    let string = vec![
        45, 0, 0, 0, 49, 0, 0, 0, 50, 0, 0, 0, 51, 0, 0, 0, 52, 1, 0, 0,
    ];
    memory
        .write(&mut store, 1500, &string)
        .expect("Could not write to memory");
    conv.call(
        &mut store,
        &[Val::I32(1500), Val::I32(string.len() as i32)],
        &mut result,
    )
    .expect("call to string-to-uint failed");
    assert_eq!(result[0].unwrap_i32(), 0);
    assert_eq!(result[1].unwrap_i64(), 0);
    assert_eq!(result[2].unwrap_i64(), 0);
}

#[test]
fn is_transient() {
    let (instance, mut store) = load_stdlib().unwrap();

    let memory = instance
        .get_memory(&mut store, "memory")
        .expect("Could not find memory");

    let is_transient = instance
        .get_func(&mut store, "stdlib.is-transient")
        .unwrap();
    let mut result = [Val::I32(0)];

    let mut test_string = |s: &str, expected: bool| {
        let s = s.as_bytes();
        memory
            .write(&mut store, 1500, s)
            .expect("Could not write to memory");
        is_transient
            .call(
                &mut store,
                &[Val::I32(1500), Val::I32(s.len() as i32)],
                &mut result,
            )
            .expect("call to is_transient failed");
        assert_eq!(result[0].unwrap_i32(), expected as i32);
    };

    // Empty string
    test_string("", false);

    // Non-transient string
    test_string("HelloWorld", false);

    // Partial transient string
    test_string("__tra", false);

    // Transient plus suffix string
    test_string("__transient_", false);

    // Transient string
    test_string("__transient", true);
}

#[test]
fn is_alpha() {
    let (instance, mut store) = load_stdlib().unwrap();

    let is_alpha = instance.get_func(&mut store, "stdlib.is-alpha").unwrap();
    let mut result = [Val::I32(0)];

    let mut test_char = |c: char, expected: bool| {
        is_alpha
            .call(&mut store, &[Val::I32(c as i32)], &mut result)
            .expect("call to is-alpha failed");
        assert_eq!(result[0].unwrap_i32(), expected as i32);
    };

    test_char('a', true);
    test_char('z', true);
    test_char('m', true);
    test_char('A', true);
    test_char('Z', true);
    test_char('N', true);
    test_char('0', false);
    test_char('@', false);
}

#[test]
fn is_valid_char() {
    let (instance, mut store) = load_stdlib().unwrap();

    let is_valid = instance
        .get_func(&mut store, "stdlib.is-valid-char")
        .unwrap();
    let mut result = [Val::I32(0)];

    let mut test_char = |c: char, expected: bool| {
        is_valid
            .call(&mut store, &[Val::I32(c as i32)], &mut result)
            .expect("call to is-valid-char failed");
        assert_eq!(result[0].unwrap_i32(), expected as i32);
    };

    test_char('a', true);
    test_char('z', true);
    test_char('m', true);
    test_char('A', true);
    test_char('Z', true);
    test_char('N', true);
    test_char('0', true);
    test_char('9', true);
    test_char('-', true);
    test_char('_', true);
    test_char('?', false);
    test_char('@', false);
}

#[test]
fn is_valid_contract_name() {
    let (instance, mut store) = load_stdlib().unwrap();

    let memory = instance
        .get_memory(&mut store, "memory")
        .expect("Could not find memory");

    let is_valid = instance
        .get_func(&mut store, "stdlib.is-valid-contract-name")
        .unwrap();
    let mut result = [Val::I32(0)];

    let mut test_string = |s: &str, expected: bool| {
        let s = s.as_bytes();
        memory
            .write(&mut store, 1500, s)
            .expect("Could not write to memory");
        is_valid
            .call(
                &mut store,
                &[Val::I32(1500), Val::I32(s.len() as i32)],
                &mut result,
            )
            .expect("call to is_transient failed");
        assert_eq!(result[0].unwrap_i32(), expected as i32);
    };

    // Empty string
    test_string("", false);

    // Starts with capital letter
    test_string("HelloWorld", true);

    // Starts with lowercase letter
    test_string("helloWorld", true);

    // Transient string
    test_string("__transient", true);

    // Single letter
    test_string("a", true);

    // Starts with '_'
    test_string("_helloWorld", false);

    // Starts with number
    test_string("1uhoh", false);

    // Contains '-' character
    test_string("hello-world", true);

    // Contains '?' character
    test_string("hello?world", false);
}

#[test]
fn principal_construct() {
    let (instance, mut store) = load_stdlib().unwrap();

    let memory = instance
        .get_memory(&mut store, "memory")
        .expect("Could not find memory");

    let construct = instance
        .get_func(&mut store, "stdlib.principal-construct")
        .unwrap();
    let mut result = [
        Val::I32(0),
        Val::I32(0),
        Val::I32(0),
        Val::I64(0),
        Val::I64(0),
        Val::I32(0),
        Val::I32(0),
        Val::I32(0),
    ];

    let mut test_construct = |version: &[u8],
                              pkhash: &[u8],
                              contract: Option<&str>,
                              expected_ok: bool,
                              expected_principal: Option<&[u8]>,
                              expected_err: u128| {
        memory
            .write(&mut store, 1500, version)
            .expect("Could not write to memory");
        memory
            .write(&mut store, 1600, pkhash)
            .expect("Could not write to memory");
        let contract_len = if let Some(contract) = contract {
            memory
                .write(&mut store, 1700, contract.as_bytes())
                .expect("Could not write to memory");
            contract.len() as i32
        } else {
            0
        };
        construct
            .call(
                &mut store,
                &[
                    Val::I32(1500),
                    Val::I32(version.len() as i32),
                    Val::I32(1600),
                    Val::I32(pkhash.len() as i32),
                    Val::I32(contract.is_some() as i32),
                    Val::I32(1700),
                    Val::I32(contract_len),
                    Val::I32(5000),
                ],
                &mut result,
            )
            .expect("call to is_transient failed");
        assert_eq!(result[0].unwrap_i32(), expected_ok as i32);
        if let Some(expected_principal) = expected_principal {
            let (offset, length) = if expected_ok {
                (result[1].unwrap_i32(), result[2].unwrap_i32())
            } else {
                assert_eq!(result[5].unwrap_i32(), 1);
                (result[6].unwrap_i32(), result[7].unwrap_i32())
            };
            assert_eq!(length, expected_principal.len() as i32);
            let mut buffer = vec![0u8; expected_principal.len()];
            memory
                .read(&mut store, offset as usize, &mut buffer)
                .expect("Could not read from memory");
            assert_eq!(&buffer, expected_principal);
        }

        let err = ((result[4].unwrap_i64() as u128) << 64) | result[3].unwrap_i64() as u128;
        assert_eq!(err, expected_err);
    };

    // Standard principal
    test_construct(
        &[26],
        &[
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
        ],
        None,
        true,
        Some(&[
            26, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 0,
        ]),
        0,
    );

    // Contract principal
    test_construct(
        &[21],
        &[
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
        ],
        Some("foo"),
        true,
        Some(&[
            21, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 3, b'f',
            b'o', b'o',
        ]),
        0,
    );

    // Empty version
    test_construct(
        &[],
        &[
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
        ],
        None,
        false,
        None,
        1,
    );

    // Mainnet version
    test_construct(
        &[22],
        &[
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
        ],
        None,
        false,
        Some(&[
            22, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 0,
        ]),
        0,
    );

    // Too high version
    test_construct(
        &[42],
        &[
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
        ],
        None,
        false,
        None,
        1,
    );

    // Other version
    test_construct(
        &[12],
        &[
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
        ],
        None,
        false,
        Some(&[
            12, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 0,
        ]),
        0,
    );

    // Too short pkhash
    test_construct(
        &[26],
        &[
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18,
        ],
        None,
        false,
        None,
        1,
    );

    // Invalid contract name
    test_construct(
        &[21],
        &[
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
        ],
        Some("foo!"),
        false,
        None,
        2,
    );

    // Empty contract name
    test_construct(
        &[21],
        &[
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
        ],
        Some(""),
        false,
        None,
        2,
    );
}

#[test]
fn is_version_valid() {
    let (instance, mut store) = load_stdlib().unwrap();

    let is_valid = instance
        .get_func(&mut store, "stdlib.is-version-valid")
        .unwrap();
    let mut result = [Val::I32(0)];

    let mut test_version = |version: u8, expected: bool| {
        is_valid
            .call(&mut store, &[Val::I32(version as i32)], &mut result)
            .expect("call to is-version-valid failed");
        assert_eq!(result[0].unwrap_i32(), expected as i32);
    };

    test_version(21, true);
    test_version(26, true);
    test_version(20, false);
    test_version(22, false);
    test_version(42, false);
    test_version(11, false);
}

#[test]
fn uint_to_string() {
    let (instance, mut store) = load_stdlib().unwrap();

    let memory = instance
        .get_memory(&mut store, "memory")
        .expect("Could not find memory");
    // This algo needs space on the stack,
    // we move the initial value of $stack-pointer
    // to a random one where it wouldn't matter
    let stack_pointer = instance.get_global(&mut store, "stack-pointer").unwrap();
    stack_pointer.set(&mut store, Val::I32(1500)).unwrap();

    let conv = instance
        .get_func(&mut store, "stdlib.uint-to-string")
        .unwrap();
    let mut result = [Val::I32(0), Val::I32(0)];

    let mut test_num = |num: u128| {
        let lo = num as i64;
        let hi = (num >> 64) as i64;

        let expected = num.to_string();

        let res_offset = 1500;

        conv.call(
            &mut store,
            &[lo.into(), hi.into(), res_offset.into()],
            &mut result,
        )
        .expect("call to uint-to-string failed");
        assert_eq!(result[0].unwrap_i32(), res_offset);
        assert_eq!(result[1].unwrap_i32(), expected.len() as i32);

        let mut buffer = vec![0u8; expected.len()];
        memory
            .read(&mut store, 1500, &mut buffer)
            .expect("could not read string answer from memory");

        assert_eq!(buffer, expected.as_bytes());
    };

    // test basic numbers
    test_num(0);
    test_num(1);
    test_num(42);
    test_num(1024);

    // Basic tests with big numbers
    test_num(184467440737095516156789);
    test_num(374467440737095681245698132);

    // Tests with number between 64 and 65 bits
    let n = u64::MAX as u128;
    for i in -5..=5 {
        test_num(n.checked_add_signed(i).unwrap());
    }

    // Tests with number close to u128::MAX
    let n = u128::MAX - 10;
    for i in 0..=10 {
        test_num(n + i);
    }
}

#[test]
fn int_to_string() {
    let (instance, mut store) = load_stdlib().unwrap();

    let memory = instance
        .get_memory(&mut store, "memory")
        .expect("Could not find memory");

    let conv = instance
        .get_func(&mut store, "stdlib.int-to-string")
        .unwrap();
    let mut result = [Val::I32(0), Val::I32(0)];

    let mut test_num = |num: i128| {
        let expected = num.to_string();

        let num = num as u128;
        let lo = num as i64;
        let hi = (num >> 64) as i64;

        // Use a safe offset in memory where we know we have space
        let res_offset = 1500;

        conv.call(
            &mut store,
            &[lo.into(), hi.into(), res_offset.into()],
            &mut result,
        )
        .expect("call to int-to-string failed");

        assert_eq!(result[0].unwrap_i32(), res_offset); // Should return the same offset
        assert_eq!(result[1].unwrap_i32(), expected.len() as i32);

        let mut buffer = vec![0u8; expected.len()];
        memory
            .read(&mut store, 1500, &mut buffer)
            .expect("could not read string answer from memory");

        assert_eq!(buffer, expected.as_bytes());
    };

    // test basic numbers
    test_num(0);
    test_num(1);
    test_num(42);
    test_num(1024);

    // Basic tests with big numbers
    test_num(184467440737095516156789);
    test_num(374467440737095681245698132);

    // Tests with negative numbers
    test_num(-1);
    test_num(-1024);
    test_num(-184467440737095516156789);
    test_num(-374467440737095681245698133);

    // Test with biggest ints
    test_num(i128::MIN);
    test_num(i128::MAX);
}

#[test]
fn uint_to_utf8() {
    let (instance, mut store) = load_stdlib().unwrap();

    let memory = instance
        .get_memory(&mut store, "memory")
        .expect("Could not find memory");
    // This algo needs space on the stack,
    // we move the initial value of $stack-pointer
    // to a random one where it wouldn't matter
    let stack_pointer = instance.get_global(&mut store, "stack-pointer").unwrap();
    stack_pointer.set(&mut store, Val::I32(1500)).unwrap();

    let conv = instance
        .get_func(&mut store, "stdlib.uint-to-utf8")
        .unwrap();
    let mut result = [Val::I32(0), Val::I32(0)];

    let mut test_num = |num: u128| {
        let lo = num as i64;
        let hi = (num >> 64) as i64;

        let expected = num.to_string();
        let expected_len = 4 * expected.len();

        let res_offset = 1500;

        conv.call(
            &mut store,
            &[lo.into(), hi.into(), res_offset.into()],
            &mut result,
        )
        .expect("call to uint-to-string failed");
        assert_eq!(result[0].unwrap_i32(), res_offset);
        assert_eq!(result[1].unwrap_i32(), expected_len as i32);

        let mut buffer = vec![0u8; expected_len];
        memory
            .read(&mut store, 1500, &mut buffer)
            .expect("could not read string answer from memory");

        let buffer: Option<String> = buffer
            .chunks_exact(4)
            .map(|c| u32::from_be_bytes(c.try_into().unwrap()))
            .map(char::from_u32)
            .collect();

        assert_eq!(buffer, Some(expected));
    };

    // test basic numbers
    test_num(0);
    test_num(1);
    test_num(42);
    test_num(1024);

    // // Basic tests with big numbers
    test_num(184467440737095516156789);
    test_num(374467440737095681245698132);

    // Tests with number between 64 and 65 bits
    let n = u64::MAX as u128;
    for i in -5..=5 {
        test_num(n.checked_add_signed(i).unwrap());
    }

    // Tests with number close to u128::MAX
    let n = u128::MAX - 10;
    for i in 0..=10 {
        test_num(n + i);
    }
}

#[test]
fn int_to_utf8() {
    let (instance, mut store) = load_stdlib().unwrap();

    let memory = instance
        .get_memory(&mut store, "memory")
        .expect("Could not find memory");

    let conv = instance.get_func(&mut store, "stdlib.int-to-utf8").unwrap();
    let mut result = [Val::I32(0), Val::I32(0)];

    let mut test_num = |num: i128| {
        let expected = num.to_string();
        let expected_len = 4 * expected.len();

        let num = num as u128;
        let lo = num as i64;
        let hi = (num >> 64) as i64;

        let res_offset = 1500;

        conv.call(
            &mut store,
            &[lo.into(), hi.into(), res_offset.into()],
            &mut result,
        )
        .expect("call to uint-to-string failed");
        assert_eq!(result[0].unwrap_i32(), res_offset);
        assert_eq!(result[1].unwrap_i32(), expected_len as i32);

        let mut buffer = vec![0u8; expected_len];
        memory
            .read(&mut store, 1500, &mut buffer)
            .expect("could not read string answer from memory");

        let buffer: Option<String> = buffer
            .chunks_exact(4)
            .map(|c| u32::from_be_bytes(c.try_into().unwrap()))
            .map(char::from_u32)
            .collect();

        assert_eq!(buffer, Some(expected));
    };

    // test basic numbers
    test_num(0);
    test_num(1);
    test_num(42);
    test_num(1024);

    // Basic tests with big numbers
    test_num(184467440737095516156789);
    test_num(374467440737095681245698132);

    // Tests with negative numbers
    test_num(-1);
    test_num(-1024);
    test_num(-184467440737095516156789);
    test_num(-374467440737095681245698133);

    // Test with biggest ints
    test_num(i128::MIN);
    test_num(i128::MAX);
}

#[test]
fn sha512_buf() {
    let (instance, mut store) = load_stdlib().unwrap();
    let memory = instance
        .get_memory(&mut store, "memory")
        .expect("Could not find memory");

    let sha512 = instance.get_func(&mut store, "stdlib.sha512-buf").unwrap();
    let mut result = [Val::I32(0), Val::I32(0)];

    // This algo needs space on the stack,
    // we move the initial value of $stack-pointer
    // to a random one where it wouldn't matter
    let stack_pointer = instance.get_global(&mut store, "stack-pointer").unwrap();
    stack_pointer.set(&mut store, Val::I32(1500)).unwrap();

    // The offset where the result hash will be written to
    let res_offset = 3000i32;
    let workspace_offset = 2048i32;

    // test with "Hello, World!", which requires only one pass
    let text = b"Hello, World!";
    memory
        .write(&mut store, END_OF_STANDARD_DATA as usize, text)
        .expect("Should be able to write to memory");

    sha512
        .call(
            &mut store,
            &[
                Val::I32(END_OF_STANDARD_DATA as i32),
                Val::I32(text.len() as i32),
                res_offset.into(),
                workspace_offset.into(),
            ],
            &mut result,
        )
        .expect("call to sha512-buf failed");
    assert_eq!(result[0].unwrap_i32(), res_offset);
    assert_eq!(result[1].unwrap_i32(), 64);

    let mut buffer = vec![0u8; result[1].unwrap_i32() as usize];
    memory
        .read(&mut store, result[0].unwrap_i32() as usize, &mut buffer)
        .expect("could not read resulting hash from memory");
    let expected_result =
        Vec::from_hex("374d794a95cdcfd8b35993185fef9ba368f160d8daf432d08ba9f1ed1e5abe6cc69291e0fa2fe0006a52570ef18c19def4e617c33ce52ef0a6e5fbe318cb0387").unwrap();
    assert_eq!(&buffer, &expected_result);

    // test with Lorem Ipsum, which will require multiple passes
    let text = b"Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua.";
    memory
        .write(&mut store, END_OF_STANDARD_DATA as usize, text)
        .expect("Should be able to write to memory");

    sha512
        .call(
            &mut store,
            &[
                Val::I32(END_OF_STANDARD_DATA as i32),
                Val::I32(text.len() as i32),
                res_offset.into(),
                workspace_offset.into(),
            ],
            &mut result,
        )
        .expect("call to sha512-buf failed");
    assert_eq!(result[0].unwrap_i32(), res_offset);
    assert_eq!(result[1].unwrap_i32(), 64);

    let mut buffer = vec![0u8; result[1].unwrap_i32() as usize];
    memory
        .read(&mut store, result[0].unwrap_i32() as usize, &mut buffer)
        .expect("could not read resulting hash from memory");
    let expected_result =
        Vec::from_hex("83cd8866be238eda447cb0ee94a6bfa6248109346b1ce3c75f8a67d35f3d8ab1697b46703065c094fcc7d3a61acc1e8ee85a4f306f13cc1a7aea7651781199b3").unwrap();
    assert_eq!(&buffer, &expected_result);

    // test with buffer of size 119, the limit between 1 and 2 blocks
    // We're handling length in 8 bytes, so 128-8-1(1 inserted after the message)
    let text = &[0; 119];
    memory
        .write(&mut store, END_OF_STANDARD_DATA as usize, text)
        .expect("Should be able to write to memory");

    sha512
        .call(
            &mut store,
            &[
                Val::I32(END_OF_STANDARD_DATA as i32),
                Val::I32(text.len() as i32),
                res_offset.into(),
                workspace_offset.into(),
            ],
            &mut result,
        )
        .expect("call to sha512-buf failed");
    assert_eq!(result[0].unwrap_i32(), res_offset);
    assert_eq!(result[1].unwrap_i32(), 64);

    let mut buffer = vec![0u8; result[1].unwrap_i32() as usize];
    memory
        .read(&mut store, result[0].unwrap_i32() as usize, &mut buffer)
        .expect("could not read resulting hash from memory");
    let expected_result =
        Vec::from_hex("c2e210f2674a648d9b58683e651f8fca5ce4270c0489773d8e4ffaecd46b22b1d5273697f45275a7c441c9e4ca91a39bdb3e3b7eb74cbdb85266eef8f30ac860").unwrap();
    assert_eq!(&buffer, &expected_result);
}

#[test]
fn sha512_int() {
    let (instance, mut store) = load_stdlib().unwrap();
    let memory = instance
        .get_memory(&mut store, "memory")
        .expect("Could not find memory");

    let sha256 = instance.get_func(&mut store, "stdlib.sha512-int").unwrap();
    let mut result = [Val::I32(0), Val::I32(0)];

    // This algo needs space on the stack,
    // we move the initial value of $stack-pointer
    // to a random one where it wouldn't matter
    let stack_pointer = instance.get_global(&mut store, "stack-pointer").unwrap();
    stack_pointer.set(&mut store, Val::I32(1500)).unwrap();

    // The offset where the result hash will be written to
    let res_offset = 3000i32;
    let workspace_offset = 2048i32;

    // Test on 0xfeedc0dedeadbeefcafed00dcafebabe
    sha256
        .call(
            &mut store,
            &[
                Val::I64(0xcafed00dcafebabe_u64 as i64),
                Val::I64(0xfeedc0dedeadbeef_u64 as i64),
                res_offset.into(),
                workspace_offset.into(),
            ],
            &mut result,
        )
        .expect("call to sha512-int failed");
    assert_eq!(result[0].unwrap_i32(), res_offset);
    assert_eq!(result[1].unwrap_i32(), 64);

    let mut buffer = vec![0u8; result[1].unwrap_i32() as usize];
    memory
        .read(&mut store, result[0].unwrap_i32() as usize, &mut buffer)
        .expect("could not read resulting hash from memory");
    let expected_result =
        Vec::from_hex("83b7d9d929320aa6a6898e4ce1dc11db78a8e4f01e47c379b49b18e3c0c8bfb98af99a758f44d4f4ee845205a4c90d6016e01d470ff95a19f1f1b37284c5afa6").unwrap();
    assert_eq!(&buffer, &expected_result);
}

#[test]
fn utf8_to_string_utf8_valid() {
    let (instance, mut store) = load_stdlib().unwrap();
    let memory = instance
        .get_memory(&mut store, "memory")
        .expect("Could not find memory");

    let convert = instance
        .get_func(&mut store, "stdlib.utf8-to-string-utf8")
        .unwrap();
    let mut result = [Val::I32(0), Val::I32(0), Val::I32(0)];

    let mut check_valid_conversion = |utf8: &str, max_len: i32| {
        let unicodes_result: Vec<_> = utf8.chars().map(|c| c as u32).collect();
        let result_size = unicodes_result.len();

        memory
            .write(&mut store, 1500, utf8.as_bytes())
            .expect("Could not write to memory");

        convert
            .call(
                &mut store,
                &[
                    1500i32.into(),
                    (utf8.len() as i32).into(),
                    3000i32.into(),
                    max_len.into(),
                ],
                &mut result,
            )
            .expect("call to utf8-to-string-utf8 failed");

        assert_eq!(result[0].unwrap_i32(), 1);
        assert_eq!(result[1].unwrap_i32(), 3000);
        assert_eq!(result[2].unwrap_i32(), 4 * result_size as i32);

        let mut buffer = vec![0u8; 4 * result_size];
        memory
            .read(&mut store, 3000, &mut buffer)
            .expect("Could not read from memory");
        let buffer: Vec<_> = buffer
            .chunks_exact(4)
            .map(|c| u32::from_be_bytes(c.try_into().unwrap()))
            .collect();
        assert_eq!(buffer, unicodes_result);
    };

    const CASES: [&str; 13] = [
        // empty string
        "",
        // checks with one byte utf8 chars
        "a",
        "abc",
        // checks with two bytes utf8 chars
        "\u{80}",
        "\u{7ff}",
        "\u{80}\u{90}\u{7ff}",
        // checks with three bytes utf8 chars
        "\u{800}",
        "\u{fff}",
        "\u{800}\u{1000}\u{fff}",
        // check with four bytes utf8 chars
        "\u{10000}",
        "\u{10ffff}",
        "\u{10000}\u{10eeee}\u{10ffff}",
        // mix
        "a\u{80}\u{1000}bc\u{10ffff}",
    ];

    for c in CASES {
        check_valid_conversion(c, c.chars().count() as i32);
    }

    // Tests with bigger max_len
    for c in CASES {
        check_valid_conversion(c, c.chars().count() as i32 + 1);
    }
}

#[test]
fn utf8_to_string_utf8_invalid() {
    let (instance, mut store) = load_stdlib().unwrap();
    let memory = instance
        .get_memory(&mut store, "memory")
        .expect("Could not find memory");

    let convert = instance
        .get_func(&mut store, "stdlib.utf8-to-string-utf8")
        .unwrap();
    let mut result = [Val::I32(0), Val::I32(0), Val::I32(0)];

    let mut check_invalid_conversion = |bytes: &[u8], expected_size: i32| {
        memory
            .write(&mut store, 1500, bytes)
            .expect("Could not write to memory");

        convert
            .call(
                &mut store,
                &[
                    1500i32.into(),
                    (bytes.len() as i32).into(),
                    3000i32.into(),
                    expected_size.into(),
                ],
                &mut result,
            )
            .expect("call to utf8-to-string-utf8 failed");

        assert_eq!(result[0].unwrap_i32(), 0);
    };

    // one byte invalid
    check_invalid_conversion(&[0b10000000], 1);
    // two bytes invalid
    check_invalid_conversion(&[0b1101_0101, 0b1101_0101], 1);
    // three bytes invalid
    check_invalid_conversion(&[0b1110_0101, 0b1101_0101, 0b1011_0101], 1);
    check_invalid_conversion(&[0b1110_0101, 0b1001_0101, 0b1111_0101], 1);
    // four bytes invalid
    check_invalid_conversion(&[0b1111_0111, 0b1100_0000, 0b1010_1010, 0b1011_0101], 1);
    check_invalid_conversion(&[0b1111_0111, 0b1000_0000, 0b1110_1010, 0b1011_0101], 1);
    check_invalid_conversion(&[0b1111_0111, 0b1000_0000, 0b1010_1010, 0b1111_0101], 1);

    // converts a random u32 to its utf8 representation without checking for validity.
    let u32_to_utf8_raw = |code: u32| {
        // adapted from core::char::encode_utf8_raw
        let mut buff = [0; 4];

        // number of bytes needed in utf-8 to represent the code
        // if it was a unicode char
        let len_utf8 = match code {
            c if c < 128 => 1,
            c if c < 2048 => 2,
            c if c < 65536 => 3,
            _ => 4,
        };

        match (len_utf8, &mut buff[..]) {
            (1, [a, ..]) => {
                *a = code as u8;
            }
            (2, [a, b, ..]) => {
                *a = ((code >> 6) & 0x1F) as u8 | 0b1100_0000;
                *b = (code & 0x3F) as u8 | 0b1000_0000;
            }
            (3, [a, b, c, ..]) => {
                *a = ((code >> 12) & 0x0F) as u8 | 0b1110_0000;
                *b = ((code >> 6) & 0x3F) as u8 | 0b1000_0000;
                *c = (code & 0x3F) as u8 | 0b1000_0000;
            }
            (4, [a, b, c, d]) => {
                *a = ((code >> 18) & 0x07) as u8 | 0b1111_0000;
                *b = ((code >> 12) & 0x3F) as u8 | 0b1000_0000;
                *c = ((code >> 6) & 0x3F) as u8 | 0b1000_0000;
                *d = (code & 0x3F) as u8 | 0b1000_0000;
            }
            _ => unreachable!("Cannot create a utf8 with more than 4 bytes"),
        }

        buff[..len_utf8].to_vec()
    };

    // invalid utf-16 surrogate characters
    for n in 0xd800..=0xdfff {
        let surrogate_bytes = u32_to_utf8_raw(n);
        check_invalid_conversion(&surrogate_bytes, 1);
    }

    // invalid too large chars > U+10FFFF (max 21 bits in a 4 bytes utf-8 char)
    for n in ((char::MAX as u32) + 1..=0b1_1111_1111_1111_1111_1111).step_by(10000) {
        let large_chars_bytes = u32_to_utf8_raw(n);
        check_invalid_conversion(&large_chars_bytes, 1);
    }

    // tests with too short max-size
    for s in [
        "a",
        "abc",
        "\u{80}",
        "\u{80}\u{90}\u{7ff}",
        "\u{fff}",
        "\u{800}\u{1000}\u{fff}",
        "\u{10000}",
        "\u{10000}\u{10eeee}\u{10ffff}",
        "a\u{80}\u{1000}bc\u{10ffff}",
    ] {
        check_invalid_conversion(s.as_bytes(), s.chars().count() as i32 - 1);
    }
}

#[test]
fn bsearch_clarity_name() {
    let (instance, mut store) = load_stdlib().unwrap();
    let memory = instance
        .get_memory(&mut store, "memory")
        .expect("Could not find memory");

    let cmp = instance
        .get_func(&mut store, "stdlib.bsearch-clarity-name")
        .unwrap();
    let mut result = [Val::I32(0)];

    let mut check = |a: &[&str], b: &str| {
        let mut list = (a.len() as u32).to_le_bytes().to_vec();
        list.extend(
            a.iter()
                .scan(4 + a.len() as u32 * 5, |state, &name| {
                    let res = state.to_le_bytes();
                    *state += name.len() as u32;
                    Some(res)
                })
                .flatten(),
        );
        list.extend(a.iter().map(|&a| a.len() as u8));
        list.extend(a.iter().flat_map(|&name| name.as_bytes()));

        memory.write(&mut store, 0, &list).unwrap();
        memory.write(&mut store, list.len(), b.as_bytes()).unwrap();

        cmp.call(
            &mut store,
            &[
                Val::I32(0),
                Val::I32(a.len() as i32),
                Val::I32(list.len() as i32),
                Val::I32(b.len() as i32),
            ],
            &mut result,
        )
        .unwrap();

        assert_eq!(
            result[0].unwrap_i32(),
            a.binary_search(&b).map(|i| i as i32).unwrap_or(-1)
        );
    };

    let list_odd = ["Lorem", "amet", "dolor", "ipsum", "sit"];
    for w in list_odd {
        check(&list_odd, w);
    }
    check(&list_odd, "zzzzzzzzzz");
    check(&list_odd, "AAAAAA");
    check(&list_odd, "color");
    check(&list_odd, "concrete");
    check(&list_odd, "elephant");
    check(&list_odd, "leopard");

    let list_even = ["Lorem", "amet", "consectetur", "dolor", "ipsum", "sit"];
    for w in list_even {
        check(&list_even, w);
    }

    check(&list_even, "zzzzzzzzzz");
    check(&list_even, "AAAAAA");
    check(&list_even, "color");
    check(&list_even, "concrete");
    check(&list_even, "elephant");
    check(&list_even, "leopard");
}

#[test]
fn skip_functions() {
    let (instance, mut store) = load_stdlib().unwrap();
    let memory = instance
        .get_memory(&mut store, "memory")
        .expect("Could not find memory");

    let skip = instance
        .get_func(&mut store, "stdlib.skip-unknown-value")
        .unwrap();

    let mut result = vec![Val::I32(0)];

    let mut check = |value: Value| {
        let ser = value.serialize_to_vec().expect("could not serialize value");

        let offset_beg = 3000;
        let offset_end = offset_beg + ser.len() as i32;
        memory
            .write(&mut store, 3000, &ser)
            .expect("could not write serialized value to memory");

        skip.call(
            &mut store,
            &[offset_beg.into(), offset_end.into()],
            &mut result,
        )
        .expect("could not call skipping function");

        assert_eq!(result[0].unwrap_i32(), offset_end);
    };

    check(Value::Int(14568789521235));
    check(Value::UInt(245879632154789));

    check(Value::Sequence(SequenceData::Buffer(BuffData {
        data: vec![],
    })));
    check(Value::Sequence(SequenceData::Buffer(BuffData {
        data: vec![0, 1, 2, 3, 4],
    })));
    check(Value::Sequence(SequenceData::Buffer(BuffData {
        data: vec![0, 1, 2, 3, 4, 5, 6, 7, 8],
    })));

    check(Value::Bool(true));
    check(Value::Bool(false));

    check(Value::Principal(PrincipalData::Standard(
        StandardPrincipalData::new(0, [0; 20]).unwrap(),
    )));

    check(Value::Principal(PrincipalData::Contract(
        QualifiedContractIdentifier {
            issuer: StandardPrincipalData::new(0, [0; 20]).unwrap(),
            name: "abcd".into(),
        },
    )));

    check(Value::Response(ResponseData {
        committed: true,
        data: Box::new(Value::Int(42)),
    }));

    check(Value::Response(ResponseData {
        committed: false,
        data: Box::new(Value::UInt(42)),
    }));

    check(Value::none());

    check(Value::some(Value::UInt(42)).unwrap());

    check(Value::cons_list_unsanitized(vec![Value::Int(1), Value::Int(2), Value::Int(3)]).unwrap());

    check(Value::from(
        TupleData::from_data(vec![
            ("abcd".into(), Value::Int(42)),
            ("defg".into(), Value::Bool(true)),
        ])
        .unwrap(),
    ));

    check(Value::string_ascii_from_bytes("hello, world!".bytes().collect()).unwrap());

    check(Value::string_utf8_from_string_utf8_literal("hello, world!".to_owned()).unwrap());
}
