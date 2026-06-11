use clar2wasm::tools::crosscheck;
use clarity::vm::types::TupleData;
use clarity::vm::{ClarityName, Value};
use proptest::prelude::*;

use crate::PropValue;

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn subsequent_func_calls_dont_erase_previous_results(
        result1 in PropValue::any(),
        result2 in PropValue::any(),
    ) {
        let snippet = format!(
            r#"
                (define-private (foo) {result1})
                (define-private (bar) {result2})

                {{ foo: (foo), bar: (bar) }}
            "#
        );

        let expected = Value::from(
            TupleData::from_data(vec![
                (ClarityName::from_literal("foo"), result1.into()),
                (ClarityName::from_literal("bar"), result2.into()),
            ])
            .unwrap(),
        );

        crosscheck(&snippet, Ok(Some(expected)));
    }
}
