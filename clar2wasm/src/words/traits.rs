use clarity::vm::{ClarityName, SymbolicExpression, SymbolicExpressionType};

use super::{ComplexWord, Word};
use crate::check_args;
use crate::wasm_generator::{ArgumentsExt, GeneratorError, WasmGenerator};
use crate::wasm_utils::{check_argument_count, ArgumentCountCheck};

#[derive(Debug)]
pub struct DefineTrait;

impl Word for DefineTrait {
    fn name(&self) -> ClarityName {
        "define-trait".into()
    }
}

impl ComplexWord for DefineTrait {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_argument_count(generator, builder, 2, args.len(), ArgumentCountCheck::Exact)?;

        let name = args.get_name(0)?;
        // Making sure if name is not reserved
        if generator.is_reserved_name(name) {
            return Err(GeneratorError::InternalError(format!(
                "Name already used {name:?}"
            )));
        }

        // Store the identifier as a string literal in the memory
        let (name_offset, name_length) = generator.add_string_literal(name)?;

        // Push the name onto the data stack
        builder
            .i32_const(name_offset as i32)
            .i32_const(name_length as i32);

        builder.call(
            generator
                .module
                .funcs
                .by_name("stdlib.define_trait")
                .ok_or_else(|| {
                    GeneratorError::InternalError("stdlib.define_trait not found".to_owned())
                })?,
        );
        Ok(())
    }
}

#[derive(Debug)]
pub struct UseTrait;

impl Word for UseTrait {
    fn name(&self) -> ClarityName {
        "use-trait".into()
    }
}

impl ComplexWord for UseTrait {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_argument_count(generator, builder, 2, args.len(), ArgumentCountCheck::Exact)?;

        // We simply add the trait to the memory so that contract-call?
        // can retrieve a correct function return type at call.
        let trait_id = args
            .get_expr(1)?
            .match_field()
            .ok_or_else(|| {
                GeneratorError::TypeError(
                    "use-trait second argument should be the imported trait".to_owned(),
                )
            })?
            .clone();

        let offset_len = generator.add_trait_identifier(&trait_id)?;
        generator.used_traits.insert(trait_id, offset_len);

        Ok(())
    }
}

#[derive(Debug)]
pub struct ImplTrait;

impl Word for ImplTrait {
    fn name(&self) -> ClarityName {
        "impl-trait".into()
    }
}

impl ComplexWord for ImplTrait {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 1, args.len(), ArgumentCountCheck::Exact);

        let trait_identifier = match &args.get_expr(0)?.expr {
            SymbolicExpressionType::Field(trait_identifier) => trait_identifier,
            _ => {
                return Err(GeneratorError::TypeError(
                    "Expected trait identifier".into(),
                ))
            }
        };

        // Store the trait identifier as a string literal in the memory
        let (trait_offset, trait_length) =
            generator.add_string_literal(&trait_identifier.to_string())?;

        // Push the name onto the data stack
        builder
            .i32_const(trait_offset as i32)
            .i32_const(trait_length as i32);

        builder.call(
            generator
                .module
                .funcs
                .by_name("stdlib.impl_trait")
                .ok_or_else(|| {
                    GeneratorError::InternalError("stdlib.impl_trait not found".to_owned())
                })?,
        );
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use clarity::types::StacksEpochId;
    use clarity::vm::types::{
        CallableData, QualifiedContractIdentifier, StandardPrincipalData, TraitIdentifier,
    };
    use clarity::vm::Value;

    use crate::tools::{
        crosscheck, crosscheck_expect_failure, crosscheck_multi_contract, TestEnvironment,
    };

    //
    // Module with tests that should only be executed
    // when running Clarity::V1.
    //
    #[cfg(feature = "test-clarity-v1")]
    mod clarity_v1 {
        use super::*;
        use crate::tools::crosscheck_with_epoch;

        #[test]
        fn validate_define_trait_epoch() {
            // Epoch20
            crosscheck_with_epoch(
                "(define-trait index-of? ((func (int) (response int int))))",
                Ok(None),
                StacksEpochId::Epoch20,
            );

            crosscheck_expect_failure("(define-trait index-of? ((func (int) (response int int))))");
        }
    }

    #[test]
    fn define_trait_eval() {
        // Just validate that it doesn't crash
        crosscheck("(define-trait my-trait ())", Ok(None))
    }

    #[test]
    fn define_trait_check_context() {
        let mut env = TestEnvironment::default();
        let val = env
            .init_contract_with_snippet(
                "token-trait",
                r#"
(define-trait token-trait
    ((transfer? (principal principal uint) (response uint uint))
        (get-balance (principal) (response uint uint))))
             "#,
            )
            .unwrap();

        assert!(val.is_none());
        let contract_context = env.get_contract_context("token-trait").unwrap();
        let token_trait = contract_context
            .lookup_trait_definition("token-trait")
            .unwrap();
        assert_eq!(token_trait.len(), 2);
    }

    #[test]
    fn use_trait_eval() {
        let mut env = TestEnvironment::default();
        env.init_contract_with_snippet(
            "my-trait",
            r#"
(define-trait my-trait
    ((add (int int) (response int int))))
             "#,
        )
        .expect("Failed to init contract.");
        let val = env
            .init_contract_with_snippet("use-token", "(use-trait the-trait .my-trait.my-trait)")
            .expect("Failed to init contract.");

        assert!(val.is_none());
    }

    #[test]
    fn use_trait_call() {
        let mut env = TestEnvironment::default();
        env.init_contract_with_snippet(
            "my-trait",
            r#"
(define-trait my-trait
  ((add (int int) (response int int))))
(define-public (add (a int) (b int))
  (ok (+ a b))
)
            "#,
        )
        .expect("Failed to init contract.");
        let val = env
            .init_contract_with_snippet(
                "use-trait",
                r#"
(use-trait the-trait .my-trait.my-trait)
(define-private (foo (adder <the-trait>) (a int) (b int))
    (contract-call? adder add a b)
)
(foo .my-trait 1 2)
            "#,
            )
            .expect("Failed to init contract.");

        assert_eq!(val.unwrap(), Value::okay(Value::Int(3)).unwrap());
    }

    #[test]
    fn impl_trait_eval() {
        let mut env = TestEnvironment::default();
        env.init_contract_with_snippet(
            "my-trait",
            r#"
(define-trait my-trait
  ((add (int int) (response int int))))
            "#,
        )
        .expect("Failed to init contract.");
        let val = env
            .init_contract_with_snippet(
                "impl-trait",
                r#"
(impl-trait .my-trait.my-trait)
(define-public (add (a int) (b int))
  (ok (+ a b))
)
            "#,
            )
            .expect("Failed to init contract.");

        assert!(val.is_none());

        let contract_context = env.get_contract_context("impl-trait").unwrap();
        assert!(contract_context
            .implemented_traits
            .contains(&TraitIdentifier::new(
                StandardPrincipalData::transient(),
                "my-trait".into(),
                "my-trait".into(),
            )));
    }

    #[test]
    fn trait_list() {
        // NOTE: this also tests `print` of `Callable`
        let first_contract_name = "my-trait-contract".into();
        let first_snippet = r#"
(define-trait my-trait
  ((add (int int) (response int int))))
(define-public (add (a int) (b int))
  (ok (+ a b))
)
            "#;

        let second_contract_name = "use-trait".into();
        let second_snippet = r#"
(use-trait the-trait .my-trait-contract.my-trait)
(define-private (foo (adder <the-trait>))
    (print (list adder adder))
)
(foo .my-trait-contract)
            "#;

        let contract_id = QualifiedContractIdentifier {
            issuer: StandardPrincipalData::transient(),
            name: "my-trait-contract".into(),
        };
        crosscheck_multi_contract(
            &[
                (first_contract_name, first_snippet),
                (second_contract_name, second_snippet),
            ],
            Ok(Some(
                Value::cons_list(
                    (0..2)
                        .map(|_| {
                            Value::CallableContract(CallableData {
                                contract_identifier: contract_id.clone(),
                                trait_identifier: Some(TraitIdentifier {
                                    name: "my-trait".into(),
                                    contract_identifier: contract_id.clone(),
                                }),
                            })
                        })
                        .collect(),
                    &StacksEpochId::latest(),
                )
                .unwrap(),
            )),
        );
    }

    #[test]
    fn validate_define_trait() {
        // Reserved keyword
        crosscheck_expect_failure("(define-trait map ((func (int) (response int int))))");

        // Custom trait token name
        crosscheck(
            "(define-trait a ((func (int) (response int int))))",
            Ok(None),
        );

        // Custom trait name duplicate
        let snippet = r#"
          (define-trait a ((func (int) (response int int))))
          (define-trait a ((func (int) (response int int))))
        "#;
        crosscheck_expect_failure(snippet);
    }
}
