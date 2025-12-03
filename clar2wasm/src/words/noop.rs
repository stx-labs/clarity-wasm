use clarity::vm::types::TypeSignature;
use clarity::vm::{ClarityName, SymbolicExpression};

use super::{ComplexWord, SimpleWord, Word};
use crate::check_args;
use crate::cost::WordCharge;
use crate::wasm_generator::{GeneratorError, WasmGenerator};
use crate::wasm_utils::{check_argument_count, ArgumentCountCheck};

// Functions below are considered no-op's because they are instructions that does nothing
// or has no effect when executed.
// They only affect the types and not the values.

#[derive(Debug)]
pub struct ToInt;

impl Word for ToInt {
    fn name(&self) -> ClarityName {
        "to-int".into()
    }
}

impl SimpleWord for ToInt {
    fn visit(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _arg_types: &[TypeSignature],
        _return_type: &TypeSignature,
    ) -> Result<(), GeneratorError> {
        self.charge(generator, builder, 0)?;

        let helper_func = generator.func_by_name("stdlib.to-int");
        builder.call(helper_func);

        Ok(())
    }
}

#[derive(Debug)]
pub struct ToUint;

impl Word for ToUint {
    fn name(&self) -> ClarityName {
        "to-uint".into()
    }
}

impl SimpleWord for ToUint {
    fn visit(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _arg_types: &[TypeSignature],
        _return_type: &TypeSignature,
    ) -> Result<(), GeneratorError> {
        self.charge(generator, builder, 0)?;

        let helper_func = generator.func_by_name("stdlib.to-uint");
        builder.call(helper_func);

        Ok(())
    }
}

#[derive(Debug)]
pub struct ContractOf;

impl Word for ContractOf {
    fn name(&self) -> ClarityName {
        "contract-of".into()
    }
}

impl ComplexWord for ContractOf {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 1, args.len(), ArgumentCountCheck::Exact);

        self.charge(generator, builder, 0)?;

        generator.traverse_args(builder, args)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use clarity::vm::errors::{RuntimeError, VmExecutionError as Error};
    use clarity::vm::types::{PrincipalData, QualifiedContractIdentifier};
    use clarity::vm::Value;

    use crate::tools::{crosscheck, evaluate, TestEnvironment};

    #[test]
    fn to_int_out_of_range() {
        crosscheck(
            "(to-int u170141183460469231731687303715884105728)",
            Err(Error::Runtime(
                RuntimeError::ArithmeticOverflow,
                Some(Vec::new()),
            )),
        )
    }

    #[test]
    fn to_int_max_on_range() {
        crosscheck(
            "(to-int u170141183460469231731687303715884105727)",
            Ok(Some(Value::Int(170141183460469231731687303715884105727))),
        )
    }

    #[test]
    fn to_int_zero() {
        crosscheck("(to-int u0)", Ok(Some(Value::Int(0))));
    }

    #[test]
    fn to_int() {
        crosscheck("(to-int u42)", Ok(Some(Value::Int(42))));
    }

    #[test]
    fn to_uint_negative() {
        crosscheck(
            "(to-uint -31)",
            Err(Error::Runtime(
                RuntimeError::ArithmeticUnderflow,
                Some(Vec::new()),
            )),
        )
    }

    #[test]
    fn to_uint() {
        crosscheck("(to-uint 767)", Ok(Some(Value::UInt(767))));
    }

    #[test]
    fn to_uint_zero() {
        crosscheck("(to-uint 0)", Ok(Some(Value::UInt(0))));
    }

    #[test]
    fn contract_of() {
        let mut env = TestEnvironment::default();
        let _ = env.init_contract_with_snippet(
            "clar2wasm-trait",
            r#"
(define-trait clar2wasm-trait
  ((add (int int) (response int int))))
(define-public (add (a int) (b int))
  (ok (+ a b)))
"#,
        );

        let val = env.init_contract_with_snippet(
            "contract-of",
            r#"
(use-trait clar2wasm-trait .clar2wasm-trait.clar2wasm-trait)
(define-public (test-contract-of (t <clar2wasm-trait>))
    (ok (contract-of t))) ;; Test subject: contract-of usage
(test-contract-of .clar2wasm-trait)
"#,
        );

        assert_eq!(
            val.unwrap(),
            Some(
                Value::okay(Value::Principal(PrincipalData::Contract(
                    QualifiedContractIdentifier::parse(
                        "S1G2081040G2081040G2081040G208105NK8PE5.clar2wasm-trait"
                    )
                    .unwrap()
                )))
                .unwrap()
            )
        );
    }

    #[test]
    fn test_to_int_oob() {
        crosscheck(
            "
(define-public (test-to-int-out-of-boundary)
  (ok (to-int u170141183460469231731687303715884105728)))
(test-to-int-out-of-boundary)
    ",
            Err(Error::Runtime(
                RuntimeError::ArithmeticOverflow,
                Some(Vec::new()),
            )),
        );
    }

    #[test]
    fn test_to_uint_err() {
        crosscheck(
            "
(define-public (test-to-uint-error)
    (ok (to-uint -47)))
(test-to-uint-error)
    ",
            Err(Error::Runtime(
                RuntimeError::ArithmeticUnderflow,
                Some(Vec::new()),
            )),
        );
    }

    #[test]
    fn test_to_int() {
        crosscheck(
            "
(to-int u42)
    ",
            Ok(Some(Value::Int(42))),
        );
    }

    #[test]
    fn test_to_uint() {
        crosscheck(
            "
(to-uint 767)
    ",
            Ok(Some(Value::UInt(767))),
        );
    }

    #[test]
    fn test_to_int_limit() {
        crosscheck(
            "
(to-int u170141183460469231731687303715884105727)
    ",
            Ok(Some(Value::Int(170141183460469231731687303715884105727))),
        );
    }

    #[test]
    fn test_contract_of_no_args() {
        let result = evaluate("(contract-of)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 1 arguments, got 0"));
    }

    #[test]
    fn test_contract_of_more_than_one_arg() {
        let result = evaluate("(contract-of 21 21)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 1 arguments, got 2"));
    }
}
