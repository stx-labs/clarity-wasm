use std::cell::RefCell;
use std::ops::{Deref, DerefMut};

use clar2wasm::linker::load_stdlib;
use clar2wasm::wasm_generator::END_OF_STANDARD_DATA;
use hex::ToHex;
use proptest::prelude::*;
use wasmtime::Val;

/// The Property Int type.
/// Used for convenience when pasing 128 bits type to Wasm
/// as a pair of `(i64, i64)`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct PropInt(u128);

impl PropInt {
    /// Creates a new PropInt.
    pub const fn new(n: u128) -> Self {
        Self(n)
    }

    /// Gets the 64 most significant bits.
    pub const fn high(&self) -> i64 {
        (self.0 >> 64) as i64
    }

    /// Gets the 64 least significant bits.
    pub const fn low(&self) -> i64 {
        self.0 as i64
    }
}

impl From<PropInt> for u128 {
    fn from(p: PropInt) -> u128 {
        p.0
    }
}

impl From<PropInt> for i128 {
    fn from(p: PropInt) -> i128 {
        p.0 as i128
    }
}

/// Convenience trait to unify the result handling of different return values
pub(crate) trait FromWasmResult {
    /// Converts a Wasm result to a type.
    fn from_wasm_result(v: &[Val]) -> Self;

    /// Retrieves the useful values in the slice to create the type.
    fn relevant_slice(s: &mut [Val]) -> &mut [Val];
}

impl FromWasmResult for u128 {
    fn from_wasm_result(v: &[Val]) -> Self {
        match v {
            &[Val::I64(lo), Val::I64(hi)] => ((lo as u64) as u128) | (((hi as u64) as u128) << 64),
            _ => panic!("invalid wasm result"),
        }
    }

    fn relevant_slice(s: &mut [Val]) -> &mut [Val] {
        &mut s[..2]
    }
}

impl FromWasmResult for i128 {
    fn from_wasm_result(v: &[Val]) -> Self {
        u128::from_wasm_result(v) as i128
    }

    fn relevant_slice(s: &mut [Val]) -> &mut [Val] {
        &mut s[..2]
    }
}

impl FromWasmResult for bool {
    fn from_wasm_result(v: &[Val]) -> Self {
        match v {
            [Val::I32(0), ..] => false,
            [Val::I32(1), ..] => true,
            _ => panic!("invalid wasm result"),
        }
    }

    fn relevant_slice(s: &mut [Val]) -> &mut [Val] {
        &mut s[..1]
    }
}

macro_rules! propints {
    ($(($name: ident, $range: ty)),+ $(,)?) => {
        $(
            #[doc = std::concat!("Creates a Proptest Strategy for [PropInt] in the range of ", std::stringify!($range), ".")]
            pub(crate) fn $name() -> proptest::strategy::BoxedStrategy<crate::utils::PropInt> {
                any::<$range>().prop_map(|n| crate::utils::PropInt::new(n as u128)).boxed()
            }
        )+
    };
}

propints! {
    // unsigned
    (tiny_uint128, u8),
    (small_uint128, u16),
    (medium_uint128, u32),
    (large_uint128, u64),
    (huge_uint128, u128),
    //signed
    (tiny_int128, i8),
    (small_int128, i16),
    (medium_int128, i32),
    (large_int128, i64),
    (huge_int128, i128),
}

type PropIntStrategy = fn() -> BoxedStrategy<PropInt>;

pub(crate) const UNSIGNED_STRATEGIES: [PropIntStrategy; 5] = [
    tiny_uint128,
    small_uint128,
    medium_uint128,
    large_uint128,
    huge_uint128,
];

pub(crate) const SIGNED_STRATEGIES: [PropIntStrategy; 5] = [
    tiny_int128,
    small_int128,
    medium_int128,
    large_int128,
    huge_int128,
];

/// Test for a two arguments Wasm arithmetic function `name` using a list of PropInt strategies.
/// The result is compared to the output of `closure`.
fn test_export_two_args<N, M, R, C>(strategies: &[PropIntStrategy], name: &str, closure: C)
where
    N: From<PropInt>,
    M: From<PropInt>,
    R: FromWasmResult + PartialEq + std::fmt::Debug,
    C: Fn(N, M) -> R,
{
    let (instance, store) = load_stdlib().unwrap();
    let store = RefCell::new(store);
    let fun = instance
        .get_func(store.borrow_mut().deref_mut(), name)
        .unwrap();

    for st_a in strategies {
        for st_b in strategies {
            proptest!(|(n in st_a(), m in st_b())| {
                let mut res = [Val::I64(0), Val::I64(0)];
                let res_slice = R::relevant_slice(&mut res);

                fun.call(
                    store.borrow_mut().deref_mut(),
                    &[n.low().into(), n.high().into(), m.low().into(), m.high().into()],
                    res_slice,
                ).unwrap_or_else(|_| panic!("Could not call exported function {name}"));

                let rust_result = closure(n.into(), m.into());
                let wasm_result = R::from_wasm_result(res_slice);

                prop_assert_eq!(rust_result, wasm_result);
            });
        }
    }
}

/// Test for a two arguments Wasm arithmetic function `name` for all unsigned PropInt strategies.
/// The result is compared to the output of `closure`.
pub(crate) fn test_export_two_unsigned_args<N, M, R, C>(name: &str, closure: C)
where
    N: From<PropInt>,
    M: From<PropInt>,
    R: FromWasmResult + PartialEq + std::fmt::Debug,
    C: Fn(N, M) -> R,
{
    test_export_two_args(&UNSIGNED_STRATEGIES, name, closure)
}

/// Test for a two arguments Wasm arithmetic function `name` for all signed PropInt strategies.
/// The result is compared to the output of `closure`.
pub(crate) fn test_export_two_signed_args<N, M, R, C>(name: &str, closure: C)
where
    N: From<PropInt>,
    M: From<PropInt>,
    R: FromWasmResult + PartialEq + std::fmt::Debug,
    C: Fn(N, M) -> R,
{
    test_export_two_args(&SIGNED_STRATEGIES, name, closure)
}

/// Test for a two arguments Wasm arithmetic function `name`, which can fail, using a list of PropInt strategies.
/// The result is compared to the output of `closure`.
fn test_export_two_args_checked<N, M, R, C>(strategies: &[PropIntStrategy], name: &str, closure: C)
where
    N: From<PropInt>,
    M: From<PropInt>,
    R: FromWasmResult + PartialEq + std::fmt::Debug,
    C: Fn(N, M) -> Option<R>,
{
    let (instance, store) = load_stdlib().unwrap();
    let store = RefCell::new(store);
    let fun = instance
        .get_func(store.borrow_mut().deref_mut(), name)
        .unwrap();

    for st_a in strategies {
        for st_b in strategies {
            proptest!(|(n in st_a(), m in st_b())| {
                let mut res = [Val::I64(0), Val::I64(0)];

                let call = fun.call(
                    store.borrow_mut().deref_mut(),
                    &[n.low().into(), n.high().into(), m.low().into(), m.high().into()],
                    &mut res,
                );

                match closure(n.into(), m.into()) {
                    Some(rust_result) => {
                        call.unwrap_or_else(|_| panic!("call to {name} failed"));
                        let wasm_result = R::from_wasm_result(&res);
                        prop_assert_eq!(rust_result, wasm_result);
                    },
                    None => { call.expect_err("expected error"); }
                }
            });
        }
    }
}

/// Test for a two arguments Wasm arithmetic function `name`, which can fail, for all unsigned PropInt strategies.
/// The result is compared to the output of `closure`.
pub(crate) fn test_export_two_unsigned_args_checked<N, M, R, C>(name: &str, closure: C)
where
    N: From<PropInt>,
    M: From<PropInt>,
    R: FromWasmResult + PartialEq + std::fmt::Debug,
    C: Fn(N, M) -> Option<R>,
{
    test_export_two_args_checked(&UNSIGNED_STRATEGIES, name, closure)
}

/// Test for a two arguments Wasm arithmetic function `name`, which can fail, for all signed PropInt strategies.
/// The result is compared to the output of `closure`.
pub(crate) fn test_export_two_signed_args_checked<N, M, R, C>(name: &str, closure: C)
where
    N: From<PropInt>,
    M: From<PropInt>,
    R: FromWasmResult + PartialEq + std::fmt::Debug,
    C: Fn(N, M) -> Option<R>,
{
    test_export_two_args_checked(&SIGNED_STRATEGIES, name, closure)
}

/// Test for a one argument Wasm arithmetic function `name` using a list of PropInt strategies.
/// The result is compared to the output of `closure`.
fn test_export_one_arg<N, R, C>(strategies: &[PropIntStrategy], name: &str, closure: C)
where
    N: From<PropInt>,
    R: FromWasmResult + PartialEq + std::fmt::Debug,
    C: Fn(N) -> R,
{
    let (instance, store) = load_stdlib().unwrap();
    let store = RefCell::new(store);
    let fun = instance
        .get_func(store.borrow_mut().deref_mut(), name)
        .unwrap();

    for st in strategies {
        proptest!(|(n in st())| {
            let mut res = [Val::I64(0), Val::I64(0)];
            let res_slice = R::relevant_slice(&mut res);

            fun.call(
                store.borrow_mut().deref_mut(),
                &[n.low().into(), n.high().into()],
                res_slice,
            ).unwrap_or_else(|_| panic!("Could not call exported function {name}"));

            let rust_result = closure(n.into());
            let wasm_result = R::from_wasm_result(res_slice);

            prop_assert_eq!(rust_result, wasm_result);
        });
    }
}

/// Test for a one argument Wasm arithmetic function `name` for all unsigned PropInt strategies.
/// The result is compared to the output of `closure`.
pub(crate) fn test_export_one_unsigned_arg<N, R, C>(name: &str, closure: C)
where
    N: From<PropInt>,
    R: FromWasmResult + PartialEq + std::fmt::Debug,
    C: Fn(N) -> R,
{
    test_export_one_arg(&UNSIGNED_STRATEGIES, name, closure)
}

/// Test for a one argument Wasm arithmetic function `name` for all signed PropInt strategies.
/// The result is compared to the output of `closure`.
pub(crate) fn test_export_one_signed_arg<N, R, C>(name: &str, closure: C)
where
    N: From<PropInt>,
    R: FromWasmResult + PartialEq + std::fmt::Debug,
    C: Fn(N) -> R,
{
    test_export_one_arg(&SIGNED_STRATEGIES, name, closure)
}

/// Test for a one argument Wasm arithmetic function `name`, which can fail, using a list of PropInt strategies.
/// The result is compared to the output of `closure`.
fn test_export_one_arg_checked<N, R, C>(strategies: &[PropIntStrategy], name: &str, closure: C)
where
    N: From<PropInt>,
    R: FromWasmResult + PartialEq + std::fmt::Debug,
    C: Fn(N) -> Option<R>,
{
    let (instance, store) = load_stdlib().unwrap();
    let store = RefCell::new(store);
    let fun = instance
        .get_func(store.borrow_mut().deref_mut(), name)
        .unwrap();

    for st in strategies {
        proptest!(|(n in st())| {
            let mut res = [Val::I64(0), Val::I64(0)];

            let call = fun.call(
                store.borrow_mut().deref_mut(),
                &[n.low().into(), n.high().into()],
                &mut res,
            );

            match closure(n.into()) {
                Some(rust_result) => {
                    call.unwrap_or_else(|_| panic!("call to {name} failed"));
                    let wasm_result = R::from_wasm_result(&res);
                    prop_assert_eq!(rust_result, wasm_result);
                },
                None => { call.expect_err("expected error"); }
            }
        });
    }
}

/// Test for a one argument Wasm arithmetic function `name`, which can fail, for all unsigned PropInt strategies.
/// The result is compared to the output of `closure`.
pub(crate) fn test_export_one_unsigned_arg_checked<N, R, C>(name: &str, closure: C)
where
    N: From<PropInt>,
    R: FromWasmResult + PartialEq + std::fmt::Debug,
    C: Fn(N) -> Option<R>,
{
    test_export_one_arg_checked(&UNSIGNED_STRATEGIES, name, closure)
}

/// Test for a one argument Wasm arithmetic function `name`, which can fail, for all signed PropInt strategies.
/// The result is compared to the output of `closure`.
pub(crate) fn test_export_one_signed_arg_checked<N, R, C>(name: &str, closure: C)
where
    N: From<PropInt>,
    R: FromWasmResult + PartialEq + std::fmt::Debug,
    C: Fn(N) -> Option<R>,
{
    test_export_one_arg_checked(&SIGNED_STRATEGIES, name, closure)
}

/// The Property Buffer type.
/// Used for convenience when dealing with buffers, to read them
/// and write them to memory, and dealing with the pair `(offset, length)`.
#[derive(Clone)]
pub(crate) struct PropBuffer {
    buffer: Vec<u8>,
    offset: usize,
}

impl std::fmt::Debug for PropBuffer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PropBuffer")
            .field(
                "buffer",
                &format!("0x{}", self.buffer.encode_hex::<String>()),
            )
            .field("offset", &self.offset)
            .finish()
    }
}

impl PropBuffer {
    /// Creates a new PropBuffer.
    pub(crate) fn new(buffer: Vec<u8>, offset: usize) -> Self {
        Self { buffer, offset }
    }

    /// Read a buffer from memory at a specified `offset` and `length`
    /// , and create a PropBuffer if the operation is a success.
    pub(crate) fn read_from_memory(
        memory: wasmtime::Memory,
        store: impl wasmtime::AsContext,
        offset: usize,
        length: usize,
    ) -> Option<Self> {
        let mut buffer = vec![0u8; length];
        memory.read(store, offset, &mut buffer).ok()?;
        Some(Self { buffer, offset })
    }

    /// Write a buffer to memory, returning a `(offset, length)` if the
    /// operation is a success.
    pub(crate) fn write_to_memory(
        &self,
        memory: wasmtime::Memory,
        store: impl wasmtime::AsContextMut,
    ) -> Option<(i32, i32)> {
        memory.write(store, self.offset, &self.buffer).ok()?;
        Some((self.offset as i32, self.buffer.len() as i32))
    }
}

impl From<PropBuffer> for Vec<u8> {
    fn from(value: PropBuffer) -> Self {
        value.buffer
    }
}

impl Deref for PropBuffer {
    type Target = Vec<u8>;

    fn deref(&self) -> &Self::Target {
        &self.buffer
    }
}

impl AsRef<[u8]> for PropBuffer {
    fn as_ref(&self) -> &[u8] {
        &self.buffer
    }
}

prop_compose! {
    /// Generates random PropBuffer with given `offset`. The length will be between 1 and `max_length`.
    pub(crate) fn buffer(offset: usize, max_length: usize)
        (buf in proptest::collection::vec(any::<u8>(), 1..max_length))
        -> PropBuffer {
            PropBuffer::new(buf, offset)
        }
}

#[allow(clippy::too_many_arguments)]
/// Tests a Wasm hashing function `func_name` and compares its output to the output of `reference_function`.
/// The buffers tested will be written in memory at offset `data_offset` and can have a length up to `data_max_length`.
/// The output of the Wasm function will be written in memory on `result_offset` with length `result_length`.
/// The stack pointer offset should be set in `stack_pointer`.
pub(crate) fn test_on_buffer_hash(
    func_name: &str,
    stack_pointer: i32,
    data_offset: usize,
    data_max_length: usize,
    result_offset: i32,
    result_length: i32,
    workspace_offset: i32,
    reference_function: impl Fn(&[u8]) -> Vec<u8>,
) {
    debug_assert!(stack_pointer >= 0);
    debug_assert!(result_offset >= 0);
    debug_assert!(stack_pointer >= END_OF_STANDARD_DATA as i32);

    let (instance, store) = load_stdlib().unwrap();
    let store = RefCell::new(store);

    let memory = instance
        .get_memory(store.borrow_mut().deref_mut(), "memory")
        .expect("Could not find memory");

    let sp = instance
        .get_global(store.borrow_mut().deref_mut(), "stack-pointer")
        .expect("Standard does not contain a $stack-pointer global");
    sp.set(store.borrow_mut().deref_mut(), stack_pointer.into())
        .expect("could not set $stack-pointer");

    let fun = instance
        .get_func(store.borrow_mut().deref_mut(), func_name)
        .unwrap_or_else(|| panic!("could not find function {func_name}"));

    proptest!(|(buf in buffer(data_offset, data_max_length))| {
        let expected_result = reference_function(&buf);

        let mut res = [Val::I32(0), Val::I32(0)];

        let (offset, len)  = buf.write_to_memory(memory, store.borrow_mut().deref_mut()).expect("could not write buffer to memory");

        fun.call(
            store.borrow_mut().deref_mut(),
            &[offset.into(), len.into(), result_offset.into(), workspace_offset.into()],
            &mut res
        ).unwrap_or_else(|_| panic!("call to {func_name} failed"));

        assert_eq!(res[0].unwrap_i32(), result_offset);
        assert_eq!(res[1].unwrap_i32(), result_length);

        let wasm_result = PropBuffer::read_from_memory(memory, store.borrow_mut().deref_mut(), result_offset as usize, result_length as usize).expect("could not read result buffer from memory");

        prop_assert_eq!(expected_result, wasm_result.as_ref());
    });
}

/// Tests a Wasm hashing function `func_name` and compares its output to the output of `reference_function`.
/// The integer input will be generated for each strategy passed to the function.
/// The output of the Wasm function will be written in memory on `result_offset` with length `result_length`.
/// The stack pointer offset should be set in `stack_pointer`.
fn test_on_integer_hash(
    strategies: &[PropIntStrategy],
    func_name: &str,
    stack_pointer: i32,
    result_offset: i32,
    result_length: i32,
    workspace_offset: i32,
    reference_function: impl Fn(i128) -> Vec<u8>,
) {
    debug_assert!(result_offset >= 0);
    debug_assert!(stack_pointer >= END_OF_STANDARD_DATA as i32);

    let (instance, store) = load_stdlib().unwrap();
    let store = RefCell::new(store);

    let memory = instance
        .get_memory(store.borrow_mut().deref_mut(), "memory")
        .expect("Could not find memory");

    let sp = instance
        .get_global(store.borrow_mut().deref_mut(), "stack-pointer")
        .expect("Standard does not contain a $stack-pointer global");
    sp.set(store.borrow_mut().deref_mut(), stack_pointer.into())
        .expect("could not set $stack-pointer");

    let fun = instance
        .get_func(store.borrow_mut().deref_mut(), func_name)
        .unwrap_or_else(|| panic!("could not find function {func_name}"));

    for st in strategies {
        proptest!(|(n in st())| {
            let expected_result = reference_function(n.into());

            let mut res = [Val::I32(0), Val::I32(0)];

            fun.call(
                store.borrow_mut().deref_mut(),
                &[n.low().into(), n.high().into(), result_offset.into(), workspace_offset.into()],
                &mut res
            ).unwrap_or_else(|_| panic!("call to {func_name} failed"));
            assert_eq!(res[0].unwrap_i32(), result_offset);
            assert_eq!(res[1].unwrap_i32(), result_length);

            let wasm_result = PropBuffer::read_from_memory(memory, store.borrow_mut().deref_mut(), result_offset as usize, result_length as usize).expect("could not read result buffer from memory");

            prop_assert_eq!(expected_result, wasm_result.as_ref());
        })
    }
}

/// Tests a Wasm hashing function `func_name` and compares its output to the output of `reference_function`.
/// The integer input will be generated from all signed strategies.
/// The output of the Wasm function will be written in memory on `result_offset` with length `result_length`.
/// The stack pointer offset should be set in `stack_pointer`.
pub(crate) fn test_on_int_hash(
    func_name: &str,
    stack_pointer: i32,
    result_offset: i32,
    result_length: i32,
    workspace_offset: i32,
    reference_function: impl Fn(i128) -> Vec<u8>,
) {
    test_on_integer_hash(
        &SIGNED_STRATEGIES,
        func_name,
        stack_pointer,
        result_offset,
        result_length,
        workspace_offset,
        reference_function,
    )
}

/// Tests a Wasm hashing function `func_name` and compares its output to the output of `reference_function`.
/// The integer input will be generated from all unsigned strategies.
/// The output of the Wasm function will be written in memory on `result_offset` with length `result_length`.
/// The stack pointer offset should be set in `stack_pointer`.
pub(crate) fn test_on_uint_hash(
    func_name: &str,
    stack_pointer: i32,
    result_offset: i32,
    result_length: i32,
    workspace_offset: i32,
    reference_function: impl Fn(i128) -> Vec<u8>,
) {
    test_on_integer_hash(
        &UNSIGNED_STRATEGIES,
        func_name,
        stack_pointer,
        result_offset,
        result_length,
        workspace_offset,
        reference_function,
    )
}

pub(crate) fn test_buff_to_uint(
    func_name: &str,
    stack_pointer: i32,
    reference_function: impl Fn(&[u8]) -> PropInt,
) {
    let (instance, store) = load_stdlib().unwrap();
    let store = RefCell::new(store);

    let memory = instance
        .get_memory(store.borrow_mut().deref_mut(), "memory")
        .expect("Could not find memory");

    let buff_to_uint = instance
        .get_func(store.borrow_mut().deref_mut(), func_name)
        .unwrap();

    proptest!(|(buff in buffer(stack_pointer as usize, 16))| {
        let expected_result = reference_function(&buff);

        let mut result = [Val::I64(0), Val::I64(0)];
        let (offset, length) = buff
            .write_to_memory(memory, store.borrow_mut().deref_mut())
            .expect("Could not write to memory");

        buff_to_uint
            .call(
                store.borrow_mut().deref_mut(),
                &[offset.into(), length.into()],
                &mut result,
            )
            .unwrap_or_else(|_| panic!("call to {func_name} failed"));
        prop_assert_eq!(result[0].unwrap_i64(), expected_result.low());
        prop_assert_eq!(result[1].unwrap_i64(), expected_result.high());
    });
}

pub(crate) fn test_buff_comparison(
    func_name: &str,
    reference_function: impl Fn(&[u8], &[u8]) -> bool,
) {
    let (instance, store) = load_stdlib().unwrap();
    let store = RefCell::new(store);

    let memory = instance
        .get_memory(store.borrow_mut().deref_mut(), "memory")
        .expect("Could not find memory");

    let cmp = instance
        .get_func(store.borrow_mut().deref_mut(), func_name)
        .unwrap();

    proptest!(ProptestConfig::with_cases(500), |(buff_a in buffer(1500, 100), buff_b in buffer(2000, 100))| {
        let expected_result = reference_function(&buff_a, &buff_b) as i32;

        let mut result = [Val::I32(0)];
        let (offset_a, length_a) = buff_a
            .write_to_memory(memory, store.borrow_mut().deref_mut())
            .expect("Could not write to memory");
        let (offset_b, length_b) = buff_b
            .write_to_memory(memory, store.borrow_mut().deref_mut())
            .expect("Could not write to memory");
        cmp
            .call(
                store.borrow_mut().deref_mut(),
                &[offset_a.into(), length_a.into(), offset_b.into(), length_b.into()],
                &mut result,
            )
            .unwrap_or_else(|_| panic!("call to {func_name} failed"));
        prop_assert_eq!(result[0].unwrap_i32(), expected_result);
    });

    proptest!(ProptestConfig::with_cases(500), |(buff in buffer(1500, 100))| {
        let expected_result = reference_function(&buff, &buff) as i32;

        let mut result = [Val::I32(0)];
        let (offset_a, length_a) = buff
            .write_to_memory(memory, store.borrow_mut().deref_mut())
            .expect("Could not write to memory");
        let (offset_b, length_b) = buff
            .write_to_memory(memory, store.borrow_mut().deref_mut())
            .expect("Could not write to memory");
        cmp
            .call(
                store.borrow_mut().deref_mut(),
                &[offset_a.into(), length_a.into(), offset_b.into(), length_b.into()],
                &mut result,
            )
            .unwrap_or_else(|_| panic!("call to {func_name} failed"));
        prop_assert_eq!(result[0].unwrap_i32(), expected_result);
    });
}
