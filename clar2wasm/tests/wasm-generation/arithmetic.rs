use clar2wasm::tools::{crosscheck_compare_only, crosscheck_compare_only_with_expected_error};
use clarity::vm::errors::{RuntimeError, VmExecutionError};
use proptest::proptest;

use crate::{int, uint};

const ONE_VALUE_OPS: [&str; 2] = ["sqrti", "log2"];
const TWO_VALUE_OPS: [&str; 2] = ["pow", "mod"];
const MULTI_VALUE_OPS: [&str; 4] = ["+", "-", "*", "/"];

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn crossprop_one_value_int(v1 in int()) {
        for op in &ONE_VALUE_OPS {
            crosscheck_compare_only_with_expected_error(
                &format!("({op} {v1})"),
                |e| matches!(e, VmExecutionError::Runtime(RuntimeError::Arithmetic(_), _))
            )
        }
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn crossprop_one_value_uint(v1 in uint()) {
        for op in &ONE_VALUE_OPS {
            crosscheck_compare_only(
                &format!("({op} {v1})")
            )
        }
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn crossprop_two_value_int(v1 in int(), v2 in int()) {
        for op in &TWO_VALUE_OPS {
            crosscheck_compare_only_with_expected_error(
                &format!("({op} {v1} {v2})"),
                |e| matches!(e,
                    VmExecutionError::Runtime(
                        RuntimeError::ArithmeticOverflow | RuntimeError::Arithmetic(_),
                        _)))
        }
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn crossprop_two_value_uint(v1 in uint(), v2 in uint()) {
        for op in &TWO_VALUE_OPS {
            crosscheck_compare_only_with_expected_error(
                &format!("({op} {v1} {v2})"),
                |e| matches!(e,
                    VmExecutionError::Runtime(
                        RuntimeError::ArithmeticOverflow |
                        RuntimeError::Arithmetic(_),
                        _)))
        }
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn crossprop_multi_value_int(values in proptest::collection::vec(int(), 1..=10)) {
        for op in &MULTI_VALUE_OPS {
            let values_str = values.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(" ");
            crosscheck_compare_only_with_expected_error(
                &format!("({op} {values_str})"),
                |e| matches!(e, VmExecutionError::Runtime(
                    RuntimeError::ArithmeticOverflow |
                    RuntimeError::ArithmeticUnderflow, _))
            )
        }
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn crossprop_multi_value_uint(v1 in uint(), v2 in uint()) {
        for op in &MULTI_VALUE_OPS {
            crosscheck_compare_only_with_expected_error(
                &format!("({op} {v1} {v2})"),
                |e| matches!(e, VmExecutionError::Runtime(
                    RuntimeError::ArithmeticOverflow |
                    RuntimeError::ArithmeticUnderflow, _))
            )
        }
    }
}
