use clar2wasm::tools::crosscheck;
use clarity::vm::errors::{RuntimeError, VmExecutionError as Error};
use clarity::vm::Value;
use proptest::arbitrary::any;
use proptest::proptest;

use crate::PropValue;

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn crosscheck_noop_to_uint(val in any::<i128>()) {
        let snippet = format!("(to-uint {})", PropValue(Value::Int(val)));

        crosscheck(
            &snippet,
            match val.try_into() {
                Ok(v) => Ok(Some(Value::UInt(v))),
                Err(_) => Err(Error::Runtime(
                    RuntimeError::ArithmeticUnderflow,
                    Some(Vec::new()),
                )),
            }
        )
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn crosscheck_noop_to_int(val in any::<u128>()) {
        let snippet = format!("(to-int {})", PropValue(Value::UInt(val)));

        crosscheck(
            &snippet,
            match val.try_into() {
                Ok(v) => Ok(Some(Value::Int(v))),
                Err(_) => Err(Error::Runtime(
                    RuntimeError::ArithmeticOverflow,
                    Some(Vec::new()),
                )),
            }
        )
    }
}
