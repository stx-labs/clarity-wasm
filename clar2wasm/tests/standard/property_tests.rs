use std::cell::RefCell;
use std::ops::DerefMut;

use clar2wasm::linker::load_stdlib;
use clar2wasm::wasm_generator::END_OF_STANDARD_DATA;
use clarity::util::hash::{Hash160, Sha256Sum, Sha512Sum};
use clarity::vm::ClarityName;
use proptest::prelude::any;
use proptest::{prop_assert_eq, proptest};
use wasmtime::Val;

use crate::utils::{
    self, medium_int128, medium_uint128, small_int128, small_uint128, test_buff_comparison,
    test_buff_to_uint, test_on_buffer_hash, test_on_int_hash, test_on_uint_hash, tiny_int128,
    tiny_uint128, FromWasmResult, PropInt, SIGNED_STRATEGIES, UNSIGNED_STRATEGIES,
};

#[test]
fn prop_add_uint() {
    utils::test_export_two_unsigned_args_checked("stdlib.add-uint", |a: u128, b: u128| {
        a.checked_add(b)
    })
}

#[test]
fn prop_add_int() {
    utils::test_export_two_signed_args_checked("stdlib.add-int", |a: i128, b: i128| {
        a.checked_add(b)
    })
}

#[test]
fn prop_sub_uint() {
    utils::test_export_two_unsigned_args_checked("stdlib.sub-uint", |a: u128, b: u128| {
        a.checked_sub(b)
    })
}

#[test]
fn prop_sub_int() {
    utils::test_export_two_signed_args_checked("stdlib.sub-int", |a: i128, b: i128| {
        a.checked_sub(b)
    })
}

#[test]
fn prop_mul_uint() {
    utils::test_export_two_unsigned_args_checked("stdlib.mul-uint", |a: u128, b: u128| {
        a.checked_mul(b)
    })
}

#[test]
fn prop_mul_int() {
    utils::test_export_two_signed_args_checked("stdlib.mul-int", |a: i128, b: i128| {
        a.checked_mul(b)
    })
}

#[test]
fn prop_div_uint() {
    utils::test_export_two_unsigned_args_checked("stdlib.div-uint", |a: u128, b: u128| {
        a.checked_div(b)
    })
}

#[test]
fn prop_div_int() {
    utils::test_export_two_signed_args_checked("stdlib.div-int", |a: i128, b: i128| {
        a.checked_div(b)
    })
}

#[test]
fn prop_mod_uint() {
    utils::test_export_two_unsigned_args_checked("stdlib.mod-uint", |a: u128, b: u128| {
        a.checked_rem(b)
    })
}

#[test]
fn prop_mod_int() {
    utils::test_export_two_signed_args_checked("stdlib.mod-int", |a: i128, b: i128| {
        a.checked_rem(b)
    })
}

#[test]
fn prop_lt_uint() {
    utils::test_export_two_unsigned_args("stdlib.lt-uint", |a: u128, b: u128| a < b)
}

#[test]
fn prop_lt_int() {
    utils::test_export_two_signed_args("stdlib.lt-int", |a: i128, b: i128| a < b);
}

#[test]
fn prop_gt_uint() {
    utils::test_export_two_unsigned_args("stdlib.gt-uint", |a: u128, b: u128| a > b);
}

#[test]
fn prop_gt_int() {
    utils::test_export_two_signed_args("stdlib.gt-int", |a: i128, b: i128| a > b);
}

#[test]
fn prop_le_uint() {
    utils::test_export_two_unsigned_args("stdlib.le-uint", |a: u128, b: u128| a <= b);
}

#[test]
fn prop_le_int() {
    utils::test_export_two_signed_args("stdlib.le-int", |a: i128, b: i128| a <= b);
}

#[test]
fn prop_ge_uint() {
    utils::test_export_two_unsigned_args("stdlib.ge-uint", |a: u128, b: u128| a >= b);
}

#[test]
fn prop_ge_int() {
    utils::test_export_two_signed_args("stdlib.ge-int", |a: i128, b: i128| a >= b);
}

#[test]
fn prop_log2_uint() {
    utils::test_export_one_unsigned_arg_checked("stdlib.log2-uint", |a: u128| {
        a.checked_ilog2().map(|u| u as u128)
    })
}

#[test]
fn prop_log2_int() {
    utils::test_export_one_signed_arg_checked("stdlib.log2-int", |a: i128| {
        a.checked_ilog2().map(|u| u as i128)
    })
}

#[test]
fn prop_sqrti_uint() {
    utils::test_export_one_unsigned_arg("stdlib.sqrti-uint", |a: u128| num_integer::Roots::sqrt(&a))
}

#[test]
fn prop_sqrti_int() {
    utils::test_export_one_signed_arg_checked("stdlib.sqrti-int", |a: i128| {
        (a >= 0).then(|| num_integer::Roots::sqrt(&a))
    })
}

#[test]
fn prop_bit_and_uint() {
    utils::test_export_two_unsigned_args("stdlib.bit-and-uint", |a: u128, b: u128| a & b)
}

#[test]
fn prop_bit_and_int() {
    utils::test_export_two_signed_args("stdlib.bit-and-int", |a: i128, b: i128| a & b)
}

#[test]
fn prop_bit_or_uint() {
    utils::test_export_two_unsigned_args("stdlib.bit-or-uint", |a: u128, b: u128| a | b)
}

#[test]
fn prop_bit_or_int() {
    utils::test_export_two_signed_args("stdlib.bit-or-int", |a: i128, b: i128| a | b)
}

#[test]
fn prop_bit_not_uint() {
    utils::test_export_one_unsigned_arg("stdlib.bit-not-uint", |a: u128| !a)
}

#[test]
fn prop_bit_not_int() {
    utils::test_export_one_signed_arg("stdlib.bit-not-int", |a: i128| !a)
}

#[test]
fn prop_bit_xor_uint() {
    utils::test_export_two_unsigned_args("stdlib.bit-xor-uint", |a: u128, b: u128| a ^ b)
}

#[test]
fn prop_bit_xor_int() {
    utils::test_export_two_signed_args("stdlib.bit-xor-int", |a: i128, b: i128| a ^ b)
}

#[test]
fn prop_bit_shift_left_uint() {
    utils::test_export_two_unsigned_args("stdlib.bit-shift-left-uint", |a: u128, b: u128| {
        a.wrapping_shl((b % 128) as u32)
    })
}

#[test]
fn prop_bit_shift_left_int() {
    // NOTE that the two arguments differ in type
    utils::test_export_two_signed_args("stdlib.bit-shift-left-int", |a: i128, b: u128| {
        a.wrapping_shl((b % 128) as u32)
    })
}

#[test]
fn prop_bit_shift_right_uint() {
    utils::test_export_two_unsigned_args("stdlib.bit-shift-right-uint", |a: u128, b: u128| {
        a.wrapping_shr((b % 128) as u32)
    })
}

#[test]
fn prop_bit_shift_right_int() {
    // NOTE that the two arguments differ in type
    utils::test_export_two_signed_args("stdlib.bit-shift-right-int", |a: i128, b: u128| {
        a.wrapping_shr((b % 128) as u32)
    })
}

#[test]
fn prop_0_pow_uint_something_is_zero() {
    let (instance, store) = load_stdlib().unwrap();
    let store = RefCell::new(store);
    let fun = instance
        .get_func(store.borrow_mut().deref_mut(), "stdlib.pow-uint")
        .unwrap();

    for st_a in UNSIGNED_STRATEGIES {
        proptest! {|(m in st_a())| {
                let mut res = [Val::I64(0), Val::I64(0)];
                let res_slice = u128::relevant_slice(&mut res);

                fun.call(
                    store.borrow_mut().deref_mut(),
                    &[Val::I64(0), Val::I64(0), m.low().into(), m.high().into()],
                    res_slice,
                )
                .unwrap_or_else(|_| panic!("Could not call exported function pow-uint"));
                let wasm_result = u128::from_wasm_result(res_slice);

                prop_assert_eq!(if u128::from(m) == 0 {1} else {0}, wasm_result);
            }
        };
    }
}

#[test]
fn prop_1_pow_uint_something_is_one() {
    let (instance, store) = load_stdlib().unwrap();
    let store = RefCell::new(store);
    let fun = instance
        .get_func(store.borrow_mut().deref_mut(), "stdlib.pow-uint")
        .unwrap();

    for st_a in UNSIGNED_STRATEGIES {
        proptest! {|(m in st_a())| {
                let mut res = [Val::I64(0), Val::I64(0)];
                let res_slice = u128::relevant_slice(&mut res);

                fun.call(
                    store.borrow_mut().deref_mut(),
                    &[Val::I64(1), Val::I64(0), m.low().into(), m.high().into()],
                    res_slice,
                )
                .unwrap_or_else(|_| panic!("Could not call exported function pow-uint"));
                let wasm_result = u128::from_wasm_result(res_slice);

                prop_assert_eq!(1, wasm_result);
            }
        };
    }
}

#[test]
fn prop_something_pow_uint_zero_is_one() {
    let (instance, store) = load_stdlib().unwrap();
    let store = RefCell::new(store);
    let fun = instance
        .get_func(store.borrow_mut().deref_mut(), "stdlib.pow-uint")
        .unwrap();

    for st_a in UNSIGNED_STRATEGIES {
        proptest! {|(m in st_a())| {
                let mut res = [Val::I64(0), Val::I64(0)];
                let res_slice = u128::relevant_slice(&mut res);

                fun.call(
                    store.borrow_mut().deref_mut(),
                    &[m.low().into(), m.high().into(), Val::I64(0), Val::I64(0)],
                    res_slice,
                )
                .unwrap_or_else(|_| panic!("Could not call exported function pow-uint"));
                let wasm_result = u128::from_wasm_result(res_slice);

                prop_assert_eq!(1, wasm_result);
            }
        };
    }
}

#[test]
fn prop_pow_uint() {
    let (instance, store) = load_stdlib().unwrap();
    let store = RefCell::new(store);
    let fun = instance
        .get_func(store.borrow_mut().deref_mut(), "stdlib.pow-uint")
        .unwrap();

    for st_a in UNSIGNED_STRATEGIES {
        for st_b in &[tiny_uint128, small_uint128, medium_uint128] {
            proptest!(|(n in st_a(), m in st_b())| {
                let mut res = [Val::I64(0), Val::I64(0)];

                let call = fun.call(
                    store.borrow_mut().deref_mut(),
                    &[n.low().into(), n.high().into(), m.low().into(), m.high().into()],
                    &mut res,
                );

                match u128::from(n).checked_pow(u128::from(m) as u32) {
                    Some(rust_result) => {
                        call.unwrap_or_else(|_| panic!("call to pow-uint failed"));
                        let wasm_result = u128::from_wasm_result(&res);
                        prop_assert_eq!(rust_result, wasm_result);
                    },
                    None => { call.expect_err("expected error"); }
                }
            });
        }
    }
}

#[test]
fn prop_0_pow_int_something_is_zero() {
    let (instance, store) = load_stdlib().unwrap();
    let store = RefCell::new(store);
    let fun = instance
        .get_func(store.borrow_mut().deref_mut(), "stdlib.pow-int")
        .unwrap();

    for st_a in SIGNED_STRATEGIES {
        proptest! {|(m in st_a())| {
                let mut res = [Val::I64(0), Val::I64(0)];
                let res_slice = i128::relevant_slice(&mut res);

                fun.call(
                    store.borrow_mut().deref_mut(),
                    &[Val::I64(0), Val::I64(0), m.low().into(), m.high().into()],
                    res_slice,
                )
                .unwrap_or_else(|_| panic!("Could not call exported function pow-uint"));
                let wasm_result = i128::from_wasm_result(res_slice);

                prop_assert_eq!(if i128::from(m) == 0 {1} else {0}, wasm_result);
            }
        };
    }
}

#[test]
fn prop_1_pow_int_something_is_one() {
    let (instance, store) = load_stdlib().unwrap();
    let store = RefCell::new(store);
    let fun = instance
        .get_func(store.borrow_mut().deref_mut(), "stdlib.pow-int")
        .unwrap();

    for st_a in SIGNED_STRATEGIES {
        proptest! {|(m in st_a())| {
                let mut res = [Val::I64(0), Val::I64(0)];
                let res_slice = i128::relevant_slice(&mut res);

                fun.call(
                    store.borrow_mut().deref_mut(),
                    &[Val::I64(1), Val::I64(0), m.low().into(), m.high().into()],
                    res_slice,
                )
                .unwrap_or_else(|_| panic!("Could not call exported function pow-uint"));
                let wasm_result = i128::from_wasm_result(res_slice);

                prop_assert_eq!(1, wasm_result);
            }
        };
    }
}

#[test]
fn prop_something_pow_int_zero_is_one() {
    let (instance, store) = load_stdlib().unwrap();
    let store = RefCell::new(store);
    let fun = instance
        .get_func(store.borrow_mut().deref_mut(), "stdlib.pow-int")
        .unwrap();

    for st_a in SIGNED_STRATEGIES {
        proptest! {|(m in st_a())| {
                let mut res = [Val::I64(0), Val::I64(0)];
                let res_slice = i128::relevant_slice(&mut res);

                fun.call(
                    store.borrow_mut().deref_mut(),
                    &[m.low().into(), m.high().into(), Val::I64(0), Val::I64(0)],
                    res_slice,
                )
                .unwrap_or_else(|_| panic!("Could not call exported function pow-uint"));
                let wasm_result = i128::from_wasm_result(res_slice);

                prop_assert_eq!(1, wasm_result);
            }
        };
    }
}

#[test]
fn prop_pow_int() {
    let (instance, store) = load_stdlib().unwrap();
    let store = RefCell::new(store);
    let fun = instance
        .get_func(store.borrow_mut().deref_mut(), "stdlib.pow-int")
        .unwrap();

    for st_a in UNSIGNED_STRATEGIES {
        for st_b in &[tiny_int128, small_int128, medium_int128] {
            proptest!(|(n in st_a(), m in st_b())| {
                let mut res = [Val::I64(0), Val::I64(0)];

                let call = fun.call(
                    store.borrow_mut().deref_mut(),
                    &[n.low().into(), n.high().into(), m.low().into(), m.high().into()],
                    &mut res,
                );

                if ![0i128, 1].contains(&n.into()) && i128::from(m) < 0 {
                    call.expect_err("expected error");
                } else {
                    match i128::from(n).checked_pow(u128::from(m) as u32) {
                        Some(rust_result) => {
                            call.unwrap_or_else(|_| panic!("call to pow-uint failed"));
                            let wasm_result = i128::from_wasm_result(&res);
                            prop_assert_eq!(rust_result, wasm_result);
                        },
                        None => { call.expect_err("expected error"); }
                    }
                }
            });
        }
    }
}

#[test]
fn prop_store_i32_be() {
    let (instance, store) = load_stdlib().unwrap();
    let store = RefCell::new(store);
    let store_i32_be = instance
        .get_func(store.borrow_mut().deref_mut(), "stdlib.store-i32-be")
        .unwrap();

    proptest!(|(val in proptest::num::i32::ANY)| {
        let mut result = [];
        // Write to a random unused place in the memory
        store_i32_be
            .call(
                store.borrow_mut().deref_mut(),
                &[Val::I32(1500), Val::I32(val)],
                &mut result,
            )
            .expect("call to store-i32-be failed");

        let memory = instance
            .get_memory(store.borrow_mut().deref_mut(), "memory")
            .expect("Could not find memory");

        // check value of mememory at offset 1500 with size 4
        let mut buffer = vec![0u8; 4];
        memory
            .read(store.borrow_mut().deref_mut(), 1500, &mut buffer)
            .expect("Could not read value from memory");
        prop_assert_eq!(buffer, val.to_be_bytes());
    });
}

#[test]
fn prop_store_i64_be() {
    let (instance, store) = load_stdlib().unwrap();
    let store = RefCell::new(store);
    let store_i64_be = instance
        .get_func(store.borrow_mut().deref_mut(), "stdlib.store-i64-be")
        .unwrap();

    proptest!(|(val in proptest::num::i64::ANY)| {
        let mut result = [];
        // Write to a random unused place in the memory
        store_i64_be
            .call(
                store.borrow_mut().deref_mut(),
                &[Val::I32(1500), Val::I64(val)],
                &mut result,
            )
            .expect("call to store-i64-be failed");

        let memory = instance
            .get_memory(store.borrow_mut().deref_mut(), "memory")
            .expect("Could not find memory");

        // check value of mememory at offset 1500 with size 4
        let mut buffer = vec![0u8; 8];
        memory
            .read(store.borrow_mut().deref_mut(), 1500, &mut buffer)
            .expect("Could not read value from memory");
        prop_assert_eq!(buffer, val.to_be_bytes());
    });
}

#[test]
fn prop_sha256_buff() {
    test_on_buffer_hash(
        "stdlib.sha256-buf",
        2048,
        END_OF_STANDARD_DATA as usize + 32,
        300,
        END_OF_STANDARD_DATA as i32,
        32,
        2048,
        |buf| Sha256Sum::from_data(buf).as_bytes().to_vec(),
    )
}

#[test]
fn prop_sha256_int_on_signed() {
    test_on_int_hash(
        "stdlib.sha256-int",
        2048,
        END_OF_STANDARD_DATA as i32,
        32,
        2048,
        |n| Sha256Sum::from_data(&n.to_le_bytes()).as_bytes().to_vec(),
    )
}

#[test]
fn prop_sha256_int_on_unsigned() {
    test_on_uint_hash(
        "stdlib.sha256-int",
        2048,
        END_OF_STANDARD_DATA as i32,
        32,
        2048,
        |n| Sha256Sum::from_data(&n.to_le_bytes()).as_bytes().to_vec(),
    )
}

#[test]
fn prop_hash160_buff() {
    test_on_buffer_hash(
        "stdlib.hash160-buf",
        2048,
        END_OF_STANDARD_DATA as usize + 20,
        300,
        END_OF_STANDARD_DATA as i32,
        20,
        2048,
        |buf| Hash160::from_data(buf).as_bytes().to_vec(),
    )
}

#[test]
fn prop_hash160_int_on_signed() {
    test_on_int_hash(
        "stdlib.hash160-int",
        2048,
        END_OF_STANDARD_DATA as i32,
        20,
        2048,
        |n| Hash160::from_data(&n.to_le_bytes()).as_bytes().to_vec(),
    )
}

#[test]
fn prop_hash160_int_on_unsigned() {
    test_on_uint_hash(
        "stdlib.hash160-int",
        2048,
        END_OF_STANDARD_DATA as i32,
        20,
        2048,
        |n| Hash160::from_data(&n.to_le_bytes()).as_bytes().to_vec(),
    )
}

#[test]
fn prop_buff_to_uint_be() {
    test_buff_to_uint("stdlib.buff-to-uint-be", 1500, |b| {
        PropInt::new({
            let mut b = b.to_vec();
            let offset = 16 - b.len();
            b.extend(std::iter::repeat_n(0, offset));
            b.rotate_right(offset);
            u128::from_be_bytes(b.try_into().unwrap())
        })
    })
}

#[test]
fn prop_buff_to_uint_le() {
    test_buff_to_uint("stdlib.buff-to-uint-le", 1500, |b| {
        PropInt::new({
            let mut b = b.to_vec();
            b.extend(std::iter::repeat_n(0, 16 - b.len()));
            u128::from_le_bytes(b.try_into().unwrap())
        })
    })
}

#[test]
fn prop_lt_buff() {
    test_buff_comparison("stdlib.lt-buff", |a, b| a < b)
}

#[test]
fn prop_gt_buff() {
    test_buff_comparison("stdlib.gt-buff", |a, b| a > b)
}

#[test]
fn prop_le_buff() {
    test_buff_comparison("stdlib.le-buff", |a, b| a <= b)
}

#[test]
fn prop_ge_buff() {
    test_buff_comparison("stdlib.ge-buff", |a, b| a >= b)
}

#[test]
fn prop_sha512_buff() {
    test_on_buffer_hash(
        "stdlib.sha512-buf",
        2048,
        END_OF_STANDARD_DATA as usize + 64,
        300,
        END_OF_STANDARD_DATA as i32,
        64,
        2048,
        |buf| Sha512Sum::from_data(buf).as_bytes().to_vec(),
    )
}

#[test]
fn prop_sha512_int_on_signed() {
    test_on_int_hash(
        "stdlib.sha512-int",
        2048,
        END_OF_STANDARD_DATA as i32,
        64,
        2048,
        |n| Sha512Sum::from_data(&n.to_le_bytes()).as_bytes().to_vec(),
    )
}

#[test]
fn prop_sha512_int_on_unsigned() {
    test_on_uint_hash(
        "stdlib.sha512-int",
        2048,
        END_OF_STANDARD_DATA as i32,
        64,
        2048,
        |n| Sha512Sum::from_data(&n.to_le_bytes()).as_bytes().to_vec(),
    )
}

#[test]
fn prop_check_clarity_name() {
    let (instance, store) = load_stdlib().unwrap();
    let store = RefCell::new(store);
    let memory = instance
        .get_memory(store.borrow_mut().deref_mut(), "memory")
        .expect("Could not find memory");

    let chk = instance
        .get_func(store.borrow_mut().deref_mut(), "stdlib.check-clarity-name")
        .unwrap();

    // We cannot use the one from clarity directly because proptest doesn't support boundaries
    let clarity_name_regex = "[a-zA-Z]([a-zA-Z0-9]|[-_!?+<>=/*]){0,127}|[-+=/*]|[<>]=?";

    proptest!(|(name in clarity_name_regex) | {
        memory.write(store.borrow_mut().deref_mut(), 3000, name.as_bytes()).unwrap();

        let mut result = [Val::I32(0)];
        chk.call(store.borrow_mut().deref_mut(), &[Val::I32(3000), Val::I32(name.len() as i32)], &mut result).unwrap();

        let expected = ClarityName::try_from(name).is_ok() as i32;
        prop_assert_eq!(result[0].unwrap_i32(), expected);
    });

    proptest!(|(name in proptest::collection::vec(any::<u8>(), 0..200)) | {
        memory.write(store.borrow_mut().deref_mut(), 3000, &name).unwrap();

        let mut result = [Val::I32(0)];
        chk.call(store.borrow_mut().deref_mut(), &[Val::I32(3000), Val::I32(name.len() as i32)], &mut result).unwrap();

        let expected = match String::from_utf8(name) {
            Ok(s) => ClarityName::try_from(s).is_ok() as i32,
            Err(_) => 0,
        };
        prop_assert_eq!(result[0].unwrap_i32(), expected);
    })
}
