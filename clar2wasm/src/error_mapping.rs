use clarity::types::StacksEpochId;
use clarity::vm::costs::CostErrors;
use clarity::vm::errors::{CheckErrors, Error, RuntimeErrorType, ShortReturnType, WasmError};
use clarity::vm::types::ResponseData;
use clarity::vm::{ClarityVersion, Value};
use wasmtime::{AsContextMut, Instance, Trap};

use crate::wasm_utils::{
    read_bytes_from_wasm, read_from_wasm_indirect, read_identifier_from_wasm, signature_from_string,
};

const LOG2_ERROR_MESSAGE: &str = "log2 must be passed a positive integer";
const SQRTI_ERROR_MESSAGE: &str = "sqrti must be passed a positive integer";
const POW_ERROR_MESSAGE: &str = "Power argument to (pow ...) must be a u32 integer";

/// Represents various error conditions that can occur
/// during Clarity contract execution
/// or other Stacks blockchain operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErrorMap {
    /// Indicates that the error is not related to Clarity contract execution.
    NotClarityError = -1,

    /// Represents an arithmetic overflow error in Clarity contract execution.
    /// This occurs when a calculation exceeds the maximum value representable.
    ArithmeticOverflow = 0,

    /// Represents an arithmetic underflow error in Clarity contract execution.
    /// This occurs when a calculation results in a value below the minimum representable value.
    ArithmeticUnderflow = 1,

    /// Indicates an attempt to divide by zero in a Clarity contract.
    DivisionByZero = 2,

    /// Represents an error in calculating the logarithm base 2 in a Clarity contract.
    /// This could occur for negative inputs.
    ArithmeticLog2Error = 3,

    /// Represents an error in calculating the integer square root in a Clarity contract.
    /// This could occur for negative inputs.
    ArithmeticSqrtiError = 4,

    /// Indicates an error in constructing a type, possibly due to invalid parameters.
    BadTypeConstruction = 5,

    /// Represents a deliberate panic in contract execution,
    /// usually triggered by `(unwrap-panic...)` and `(unwrap-err-panic...)`.
    Panic = 6,

    /// Indicates a failure in an assertion that was expected to cause a short return,
    /// usually triggered by `(asserts!...)`.
    ShortReturnAssertionFailure = 7,

    /// Represents an error in exponentiation operations in a Clarity contract.
    /// This could occur for invalid bases or exponents.
    ArithmeticPowError = 8,

    /// Indicates an attempt to use a name that is already in use, possibly for a variable or function.
    NameAlreadyUsed = 9,

    /// Represents a short-return error for an expected value that wraps a Response type.
    /// Usually triggered by `(try!...)`.
    ShortReturnExpectedValueResponse = 10,

    /// Represents a short-return error for an expected value that wraps an Optional type.
    /// Usually triggered by `(try!...)`.
    ShortReturnExpectedValueOptional = 11,

    /// Represents a short-return error for an expected value.
    /// usually triggered by `(unwrap!...)` and `(unwrap-err!...)`.
    ShortReturnExpectedValue = 12,

    /// Indicates an attempt to use a function with the wrong amount of arguments
    ArgumentCountMismatch = 13,

    /// Indicates an attempt to use a function with too few arguments
    ArgumentCountAtLeast = 14,

    /// Indicates an attempt to use a function with too many arguments
    ArgumentCountAtMost = 15,

    /// Indicates a runtime cost overrun
    CostOverrunRuntime = 100,

    /// Indicates a read count cost overrun
    CostOverrunReadCount = 101,

    /// Indicates a read length cost overrun
    CostOverrunReadLength = 102,

    /// Indicates a write count cost overrun
    CostOverrunWriteCount = 103,

    /// Indicates a write length cost overrun
    CostOverrunWriteLength = 104,

    /// A catch-all for errors that are not mapped to specific error codes.
    /// This might be used for unexpected or unclassified errors.
    NotMapped = 99,
}

impl From<i32> for ErrorMap {
    fn from(error_code: i32) -> Self {
        match error_code {
            -1 => ErrorMap::NotClarityError,
            0 => ErrorMap::ArithmeticOverflow,
            1 => ErrorMap::ArithmeticUnderflow,
            2 => ErrorMap::DivisionByZero,
            3 => ErrorMap::ArithmeticLog2Error,
            4 => ErrorMap::ArithmeticSqrtiError,
            5 => ErrorMap::BadTypeConstruction,
            6 => ErrorMap::Panic,
            7 => ErrorMap::ShortReturnAssertionFailure,
            8 => ErrorMap::ArithmeticPowError,
            9 => ErrorMap::NameAlreadyUsed,
            10 => ErrorMap::ShortReturnExpectedValueResponse,
            11 => ErrorMap::ShortReturnExpectedValueOptional,
            12 => ErrorMap::ShortReturnExpectedValue,
            13 => ErrorMap::ArgumentCountMismatch,
            14 => ErrorMap::ArgumentCountAtLeast,
            15 => ErrorMap::ArgumentCountAtMost,
            100 => ErrorMap::CostOverrunRuntime,
            101 => ErrorMap::CostOverrunReadCount,
            102 => ErrorMap::CostOverrunReadLength,
            103 => ErrorMap::CostOverrunWriteCount,
            104 => ErrorMap::CostOverrunWriteLength,
            _ => ErrorMap::NotMapped,
        }
    }
}

pub(crate) fn resolve_error(
    e: wasmtime::Error,
    instance: Instance,
    mut store: impl AsContextMut,
    epoch_id: &StacksEpochId,
    clarity_version: &ClarityVersion,
) -> Error {
    if let Some(vm_error) = e.root_cause().downcast_ref::<Error>() {
        // SAFETY:
        //
        // This unsafe operation returns the value of a location pointed by `*mut T`.
        //
        // The purpose of this code is to take the ownership of the `vm_error` value
        // since clarity::vm::errors::Error is not a Clonable type.
        //
        // Converting a `&T` (vm_error) to a `*mut T` doesn't cause any issues here
        // because the reference is not borrowed elsewhere.
        //
        // The replaced `T` value is deallocated after the operation. Therefore, the chosen `T`
        // is a dummy value, solely to satisfy the signature of the replace function
        // and not cause harm when it is deallocated.
        //
        // Specifically, Error::Wasm(WasmError::ModuleNotFound) was selected as the placeholder value.
        return unsafe {
            core::ptr::replace(
                (vm_error as *const Error) as *mut Error,
                Error::Wasm(WasmError::ModuleNotFound),
            )
        };
    }

    if let Some(vm_error) = e.root_cause().downcast_ref::<CheckErrors>() {
        // SAFETY:
        //
        // This unsafe operation returns the value of a location pointed by `*mut T`.
        //
        // The purpose of this code is to take the ownership of the `vm_error` value
        // since clarity::vm::errors::Error is not a Clonable type.
        //
        // Converting a `&T` (vm_error) to a `*mut T` doesn't cause any issues here
        // because the reference is not borrowed elsewhere.
        //
        // The replaced `T` value is deallocated after the operation. Therefore, the chosen `T`
        // is a dummy value, solely to satisfy the signature of the replace function
        // and not cause harm when it is deallocated.
        //
        // Specifically, CheckErrors::ExpectedName was selected as the placeholder value.
        return unsafe {
            let err = core::ptr::replace(
                (vm_error as *const CheckErrors) as *mut CheckErrors,
                CheckErrors::ExpectedName,
            );

            <CheckErrors as std::convert::Into<Error>>::into(err)
        };
    }

    // Check if the error is caused by
    // an unreachable Wasm trap.
    //
    // In this case, runtime errors are handled
    // by being mapped to the corresponding ClarityWasm Errors.
    if let Some(Trap::UnreachableCodeReached) = e.root_cause().downcast_ref::<Trap>() {
        return from_runtime_error_code(instance, &mut store, e, epoch_id, clarity_version);
    }

    // All other errors are treated as general runtime errors.
    Error::Wasm(WasmError::Runtime(e))
}

/// Converts a WebAssembly runtime error code into a Clarity `Error`.
///
/// This function interprets an error code from a WebAssembly runtime execution and
/// translates it into an appropriate Clarity error type. It handles various categories
/// of errors including arithmetic errors, short returns, and other runtime issues.
///
/// # Returns
///
/// Returns a Clarity `Error` that corresponds to the runtime error encountered during
/// WebAssembly execution.
///
fn from_runtime_error_code(
    instance: Instance,
    mut store: impl AsContextMut,
    e: wasmtime::Error,
    epoch_id: &StacksEpochId,
    clarity_version: &ClarityVersion,
) -> Error {
    let runtime_error_code = get_global_i32(&instance, &mut store, "runtime-error-code");

    match ErrorMap::from(runtime_error_code) {
        ErrorMap::NotClarityError => Error::Wasm(WasmError::Runtime(e)),
        ErrorMap::ArithmeticOverflow => {
            Error::Runtime(RuntimeErrorType::ArithmeticOverflow, Some(Vec::new()))
        }
        ErrorMap::ArithmeticUnderflow => {
            Error::Runtime(RuntimeErrorType::ArithmeticUnderflow, Some(Vec::new()))
        }
        ErrorMap::DivisionByZero => {
            Error::Runtime(RuntimeErrorType::DivisionByZero, Some(Vec::new()))
        }
        ErrorMap::ArithmeticLog2Error => Error::Runtime(
            RuntimeErrorType::Arithmetic(LOG2_ERROR_MESSAGE.into()),
            Some(Vec::new()),
        ),
        ErrorMap::ArithmeticSqrtiError => Error::Runtime(
            RuntimeErrorType::Arithmetic(SQRTI_ERROR_MESSAGE.into()),
            Some(Vec::new()),
        ),
        ErrorMap::BadTypeConstruction => {
            Error::Runtime(RuntimeErrorType::BadTypeConstruction, Some(Vec::new()))
        }
        ErrorMap::Panic => {
            // TODO: see issue: #531
            // This RuntimeErrorType::UnwrapFailure need to have a proper context.
            Error::Runtime(RuntimeErrorType::UnwrapFailure, Some(Vec::new()))
        }
        ErrorMap::ShortReturnAssertionFailure => {
            let clarity_val = short_return_value(&instance, &mut store, epoch_id, clarity_version);
            Error::ShortReturn(ShortReturnType::AssertionFailed(Box::new(clarity_val)))
        }
        ErrorMap::ArithmeticPowError => Error::Runtime(
            RuntimeErrorType::Arithmetic(POW_ERROR_MESSAGE.into()),
            Some(Vec::new()),
        ),
        ErrorMap::NameAlreadyUsed => {
            let runtime_error_arg_offset =
                get_global_i32(&instance, &mut store, "runtime-error-arg-offset");
            let runtime_error_arg_len =
                get_global_i32(&instance, &mut store, "runtime-error-arg-len");

            let memory = instance
                .get_memory(&mut store, "memory")
                .unwrap_or_else(|| panic!("Could not find wasm instance memory"));
            let arg_name = read_identifier_from_wasm(
                memory,
                &mut store,
                runtime_error_arg_offset,
                runtime_error_arg_len,
            )
            .unwrap_or_else(|e| panic!("Could not recover arg_name: {e}"));

            Error::Unchecked(CheckErrors::NameAlreadyUsed(arg_name))
        }
        ErrorMap::ShortReturnExpectedValueResponse => {
            let clarity_val = short_return_value(&instance, &mut store, epoch_id, clarity_version);
            Error::ShortReturn(ShortReturnType::ExpectedValue(Box::new(Value::Response(
                ResponseData {
                    committed: false,
                    data: Box::new(clarity_val),
                },
            ))))
        }
        ErrorMap::ShortReturnExpectedValueOptional => {
            Error::ShortReturn(ShortReturnType::ExpectedValue(Box::new(Value::Optional(
                clarity::vm::types::OptionalData { data: None },
            ))))
        }
        ErrorMap::ShortReturnExpectedValue => {
            let clarity_val = short_return_value(&instance, &mut store, epoch_id, clarity_version);
            Error::ShortReturn(ShortReturnType::ExpectedValue(Box::new(clarity_val)))
        }
        ErrorMap::ArgumentCountMismatch => {
            let (expected, got) = get_runtime_error_arg_lengths(&instance, &mut store);
            Error::Unchecked(CheckErrors::IncorrectArgumentCount(expected, got))
        }
        ErrorMap::ArgumentCountAtLeast => {
            let (expected, got) = get_runtime_error_arg_lengths(&instance, &mut store);
            Error::Unchecked(CheckErrors::RequiresAtLeastArguments(expected, got))
        }
        ErrorMap::ArgumentCountAtMost => {
            let (expected, got) = get_runtime_error_arg_lengths(&instance, &mut store);
            Error::Unchecked(CheckErrors::RequiresAtMostArguments(expected, got))
        }
        ErrorMap::CostOverrunRuntime => Error::from(CostErrors::CostOverflow),
        ErrorMap::CostOverrunReadCount => Error::from(CostErrors::CostOverflow),
        ErrorMap::CostOverrunReadLength => Error::from(CostErrors::CostOverflow),
        ErrorMap::CostOverrunWriteCount => Error::from(CostErrors::CostOverflow),
        ErrorMap::CostOverrunWriteLength => Error::from(CostErrors::CostOverflow),
        _ => panic!("Runtime error code {runtime_error_code} not supported"),
    }
}

/// Retrieves the value of a 32-bit integer global variable from a WebAssembly instance.
///
/// This function attempts to fetch a global variable by name from the provided WebAssembly
/// instance and return its value as an `i32`. It's designed to simplify the process of
/// reading global variables in WebAssembly modules.
///
/// # Returns
///
/// Returns the value of the global variable as an `i32`.
///
fn get_global_i32(instance: &Instance, store: &mut impl AsContextMut, name: &str) -> i32 {
    instance
        .get_global(&mut *store, name)
        .and_then(|glob| glob.get(store).i32())
        .unwrap_or_else(|| panic!("Could not find ${name} global with i32 value"))
}

/// Retrieves the expected and actual argument counts from a byte-encoded string.
///
/// This function interprets a string as a sequence of bytes, where the first 4 bytes
/// represent the expected number of arguments, and the bytes at positions 16 to 19
/// represent the actual number of arguments received. It converts these byte sequences
/// into `usize` values and returns them as a tuple.
///
/// # Returns
///
/// A tuple `(expected, got)` where:
/// - `expected` is the number of arguments expected.
/// - `got` is the number of arguments actually received.
fn extract_expected_and_got(bytes: &[u8]) -> (usize, usize) {
    // Assuming the first 4 bytes represent the expected value
    let expected = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]) as usize;

    // Assuming the next 4 bytes represent the got value
    let got = u32::from_le_bytes([bytes[4], bytes[5], bytes[6], bytes[7]]) as usize;

    (expected, got)
}

/// Retrieves and deserializes a Clarity value from WebAssembly memory in the context of a short return.
///
/// This function is used to extract a Clarity value that has been stored in WebAssembly memory
/// as part of a short return operation. It reads necessary metadata from global variables,
/// deserializes the type information, and then reads and deserializes the actual value.
///
/// # Returns
///
/// Returns a deserialized Clarity `Value` representing the short return value.
///
fn short_return_value(
    instance: &Instance,
    store: &mut impl AsContextMut,
    epoch_id: &StacksEpochId,
    clarity_version: &ClarityVersion,
) -> Value {
    let val_offset = get_global_i32(instance, store, "runtime-error-value-offset");
    let type_ser_offset = get_global_i32(instance, store, "runtime-error-type-ser-offset");
    let type_ser_len = get_global_i32(instance, store, "runtime-error-type-ser-len");

    let memory = instance
        .get_memory(&mut *store, "memory")
        .unwrap_or_else(|| panic!("Could not find wasm instance memory"));

    let type_ser_str = read_identifier_from_wasm(memory, store, type_ser_offset, type_ser_len)
        .unwrap_or_else(|e| panic!("Could not recover stringified type: {e}"));

    let value_ty = signature_from_string(&type_ser_str, *clarity_version, *epoch_id)
        .unwrap_or_else(|e| panic!("Could not recover thrown value: {e}"));

    read_from_wasm_indirect(memory, store, &value_ty, val_offset, *epoch_id)
        .unwrap_or_else(|e| panic!("Could not read thrown value from memory: {e}"))
}

/// Retrieves the argument lengths from the runtime error global variables.
///
/// This function reads the global variables `runtime-error-arg-offset` and `runtime-error-arg-len`
/// from the WebAssembly instance and constructs a string representing the argument lengths.
///
/// # Returns
///
/// A string representing the argument lengths.
fn get_runtime_error_arg_lengths(
    instance: &Instance,
    store: &mut impl AsContextMut,
) -> (usize, usize) {
    let runtime_error_arg_offset = get_global_i32(instance, store, "runtime-error-arg-offset");
    let runtime_error_arg_len = get_global_i32(instance, store, "runtime-error-arg-len");

    let memory = instance
        .get_memory(&mut *store, "memory")
        .unwrap_or_else(|| panic!("Could not find wasm instance memory"));
    let arg_lengths = read_bytes_from_wasm(
        memory,
        store,
        runtime_error_arg_offset,
        runtime_error_arg_len,
    )
    .unwrap_or_else(|e| panic!("Could not recover arg_lengths: {e}"));

    extract_expected_and_got(&arg_lengths)
}
