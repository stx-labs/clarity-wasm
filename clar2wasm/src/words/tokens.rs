use clarity::vm::types::{TypeSignature, TypeSignatureExt};
use clarity::vm::{ClarityName, SymbolicExpression};

use super::{ComplexWord, Word};
use crate::check_args;
use crate::cost::WordCharge;
use crate::wasm_generator::{ArgumentsExt, GeneratorError, WasmGenerator};
use crate::wasm_utils::{check_argument_count, ArgumentCountCheck};

#[derive(Debug)]
pub struct DefineFungibleToken;

impl Word for DefineFungibleToken {
    fn name(&self) -> ClarityName {
        "define-fungible-token".into()
    }
}

impl ComplexWord for DefineFungibleToken {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(
            generator,
            builder,
            1,
            args.len(),
            ArgumentCountCheck::AtLeast
        );
        check_args!(
            generator,
            builder,
            2,
            args.len(),
            ArgumentCountCheck::AtMost
        );

        let name = args.get_name(0)?;
        // Making sure if name is not reserved
        if generator.is_reserved_name(name) {
            return Err(GeneratorError::InternalError(format!(
                "Name already used {name:?}"
            )));
        }

        let supply = args.get(1);

        // Store the identifier as a string literal in the memory
        let (name_offset, name_length) = generator.add_string_literal(name)?;

        // Push the name onto the data stack
        builder
            .i32_const(name_offset as i32)
            .i32_const(name_length as i32);

        // Push the supply to the stack, as an optional uint
        // (first i32 indicates some/none)
        if let Some(supply) = supply {
            builder.i32_const(1);
            generator.traverse_expr(builder, supply)?;
        } else {
            builder.i32_const(0).i64_const(0).i64_const(0);
        }

        builder.call(generator.func_by_name("stdlib.define_ft"));
        Ok(())
    }
}

#[derive(Debug)]
pub struct BurnFungibleToken;

impl Word for BurnFungibleToken {
    fn name(&self) -> ClarityName {
        "ft-burn?".into()
    }
}

impl ComplexWord for BurnFungibleToken {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 3, args.len(), ArgumentCountCheck::Exact);

        self.charge(generator, builder, 0)?;

        let token = args.get_name(0)?;
        let amount = args.get_expr(1)?;
        let sender = args.get_expr(2)?;

        // Push the token name onto the stack
        let (id_offset, id_length) = generator.add_string_literal(token)?;
        builder
            .i32_const(id_offset as i32)
            .i32_const(id_length as i32);

        // Push the amount and sender onto the stack
        generator.traverse_expr(builder, amount)?;
        generator.traverse_expr(builder, sender)?;

        // Call the host interface function `ft_burn`
        builder.call(generator.func_by_name("stdlib.ft_burn"));

        Ok(())
    }
}

#[derive(Debug)]
pub struct TransferFungibleToken;

impl Word for TransferFungibleToken {
    fn name(&self) -> ClarityName {
        "ft-transfer?".into()
    }
}

impl ComplexWord for TransferFungibleToken {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 4, args.len(), ArgumentCountCheck::Exact);

        self.charge(generator, builder, 0)?;

        let token = args.get_name(0)?;
        let amount = args.get_expr(1)?;
        let sender = args.get_expr(2)?;
        let recipient = args.get_expr(3)?;

        // Push the token name onto the stack
        let (id_offset, id_length) = generator.add_string_literal(token)?;
        builder
            .i32_const(id_offset as i32)
            .i32_const(id_length as i32);

        // Push the amount, sender, and recipient onto the stack
        generator.traverse_expr(builder, amount)?;
        generator.traverse_expr(builder, sender)?;
        generator.traverse_expr(builder, recipient)?;

        // Call the host interface function `ft_transfer`
        builder.call(generator.func_by_name("stdlib.ft_transfer"));

        Ok(())
    }
}

#[derive(Debug)]
pub struct MintFungibleToken;

impl Word for MintFungibleToken {
    fn name(&self) -> ClarityName {
        "ft-mint?".into()
    }
}

impl ComplexWord for MintFungibleToken {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 3, args.len(), ArgumentCountCheck::Exact);

        self.charge(generator, builder, 0)?;

        let token = args.get_name(0)?;
        let amount = args.get_expr(1)?;
        let recipient = args.get_expr(2)?;

        let (id_offset, id_length) = generator.add_string_literal(token)?;
        builder
            .i32_const(id_offset as i32)
            .i32_const(id_length as i32);

        // Push the amount and recipient onto the stack
        generator.traverse_expr(builder, amount)?;
        generator.traverse_expr(builder, recipient)?;

        // Call the host interface function `ft_mint`
        builder.call(generator.func_by_name("stdlib.ft_mint"));

        Ok(())
    }
}

#[derive(Debug)]
pub struct GetSupplyOfFungibleToken;

impl Word for GetSupplyOfFungibleToken {
    fn name(&self) -> ClarityName {
        "ft-get-supply".into()
    }
}

impl ComplexWord for GetSupplyOfFungibleToken {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 1, args.len(), ArgumentCountCheck::Exact);

        self.charge(generator, builder, 0)?;

        let token = args.get_name(0)?;

        let (id_offset, id_length) = generator.add_string_literal(token)?;
        builder
            .i32_const(id_offset as i32)
            .i32_const(id_length as i32);

        builder.call(generator.func_by_name("stdlib.ft_get_supply"));

        Ok(())
    }
}

#[derive(Debug)]
pub struct GetBalanceOfFungibleToken;

impl Word for GetBalanceOfFungibleToken {
    fn name(&self) -> ClarityName {
        "ft-get-balance".into()
    }
}

impl ComplexWord for GetBalanceOfFungibleToken {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 2, args.len(), ArgumentCountCheck::Exact);

        self.charge(generator, builder, 0)?;

        let token = args.get_name(0)?;
        let owner = args.get_expr(1)?;

        // Push the token name onto the stack
        let (id_offset, id_length) = generator.add_string_literal(token)?;
        builder
            .i32_const(id_offset as i32)
            .i32_const(id_length as i32);

        // Push the owner onto the stack
        generator.traverse_expr(builder, owner)?;

        // Call the host interface function `ft_get_balance`
        builder.call(generator.func_by_name("stdlib.ft_get_balance"));

        Ok(())
    }
}

//////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug)]
pub struct DefineNonFungibleToken;

impl Word for DefineNonFungibleToken {
    fn name(&self) -> ClarityName {
        "define-non-fungible-token".into()
    }
}

impl ComplexWord for DefineNonFungibleToken {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 2, args.len(), ArgumentCountCheck::Exact);

        let name = args.get_name(0)?;
        // Making sure if name is not reserved
        if generator.is_reserved_name(name) {
            return Err(GeneratorError::InternalError(format!(
                "Name already used {name:?}"
            )));
        }

        // we will save the NFT type for reuse with the nft-x functions
        // (a wrong NFT type is an issue only with Clarity1, but it doesn't
        // hurt to use it with all Clarity versions)
        let nft_type = TypeSignature::parse_type_repr(
            generator.contract_analysis.epoch,
            args.get_expr(1)?,
            &mut (),
        )
        .map_err(|e| GeneratorError::TypeError(e.to_string()))?;
        generator.nft_types.insert(name.clone(), nft_type);

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
                .by_name("stdlib.define_nft")
                .ok_or_else(|| {
                    GeneratorError::InternalError("stdlib.define_nft not found".to_owned())
                })?,
        );
        Ok(())
    }
}

#[derive(Debug)]
pub struct BurnNonFungibleToken;

impl Word for BurnNonFungibleToken {
    fn name(&self) -> ClarityName {
        "nft-burn?".into()
    }
}

impl ComplexWord for BurnNonFungibleToken {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 3, args.len(), ArgumentCountCheck::Exact);

        let token = args.get_name(0)?;
        let identifier = args.get_expr(1)?;
        let sender = args.get_expr(2)?;

        // Push the token name onto the stack
        let (id_offset, id_length) = generator.add_string_literal(token)?;
        builder
            .i32_const(id_offset as i32)
            .i32_const(id_length as i32);

        self.charge(generator, builder, id_length)?;

        // Push the identifier onto the stack
        let identifier_ty = generator.nft_types.get(token).cloned().ok_or_else(|| {
            GeneratorError::TypeError("Usage of nft-burn? on an unknown nft token".to_owned())
        })?;
        generator.set_expr_type(identifier, identifier_ty.clone())?;
        generator.traverse_expr(builder, identifier)?;

        // Allocate space on the stack for the identifier
        let (id_offset, id_size) =
            generator.create_call_stack_local(builder, &identifier_ty, true, false);

        // Write the identifier to the stack (since the host needs to handle generic types)
        generator.write_to_memory(builder, id_offset, 0, &identifier_ty)?;

        // Push the offset and size to the data stack
        builder.local_get(id_offset).i32_const(id_size);

        // Push the sender onto the stack
        generator.traverse_expr(builder, sender)?;

        // Call the host interface function `nft_burn`
        builder.call(generator.func_by_name("stdlib.nft_burn"));

        Ok(())
    }
}

#[derive(Debug)]
pub struct TransferNonFungibleToken;

impl Word for TransferNonFungibleToken {
    fn name(&self) -> ClarityName {
        "nft-transfer?".into()
    }
}

impl ComplexWord for TransferNonFungibleToken {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 4, args.len(), ArgumentCountCheck::Exact);

        let token = args.get_name(0)?;
        let identifier = args.get_expr(1)?;
        let sender = args.get_expr(2)?;
        let recipient = args.get_expr(3)?;

        // Push the token name onto the stack
        let (id_offset, id_length) = generator.add_string_literal(token)?;
        builder
            .i32_const(id_offset as i32)
            .i32_const(id_length as i32);

        self.charge(generator, builder, id_length)?;

        // Push the identifier onto the stack
        let identifier_ty = generator.nft_types.get(token).cloned().ok_or_else(|| {
            GeneratorError::TypeError("Usage of nft-transfer? on an unknown nft token".to_owned())
        })?;
        generator.set_expr_type(identifier, identifier_ty.clone())?;
        generator.traverse_expr(builder, identifier)?;

        // Allocate space on the stack for the identifier
        let (id_offset, id_size) =
            generator.create_call_stack_local(builder, &identifier_ty, true, false);

        // Write the identifier to the stack (since the host needs to handle generic types)
        generator.write_to_memory(builder, id_offset, 0, &identifier_ty)?;

        // Push the offset and size to the data stack
        builder.local_get(id_offset).i32_const(id_size);

        // Push the sender onto the stack
        generator.traverse_expr(builder, sender)?;

        // Push the recipient onto the stack
        generator.traverse_expr(builder, recipient)?;

        // Call the host interface function `nft_transfer`
        builder.call(generator.func_by_name("stdlib.nft_transfer"));

        Ok(())
    }
}

#[derive(Debug)]
pub struct MintNonFungibleToken;

impl Word for MintNonFungibleToken {
    fn name(&self) -> ClarityName {
        "nft-mint?".into()
    }
}

impl ComplexWord for MintNonFungibleToken {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 3, args.len(), ArgumentCountCheck::Exact);

        let token = args.get_name(0)?;
        let identifier = args.get_expr(1)?;
        let recipient = args.get_expr(2)?;

        // Push the token name onto the stack
        let (id_offset, id_length) = generator.add_string_literal(token)?;
        builder
            .i32_const(id_offset as i32)
            .i32_const(id_length as i32);

        self.charge(generator, builder, id_length)?;

        // Push the identifier onto the stack
        let identifier_ty = generator.nft_types.get(token).cloned().ok_or_else(|| {
            GeneratorError::TypeError("Usage of nft-mint? on an unknown nft token".to_owned())
        })?;
        generator.set_expr_type(identifier, identifier_ty.clone())?;
        generator.traverse_expr(builder, identifier)?;

        // Allocate space on the stack for the identifier
        let (id_offset, id_size) =
            generator.create_call_stack_local(builder, &identifier_ty, true, false);

        // Write the identifier to the stack (since the host needs to handle generic types)
        generator.write_to_memory(builder, id_offset, 0, &identifier_ty)?;

        // Push the offset and size to the data stack
        builder.local_get(id_offset).i32_const(id_size);

        // Push the recipient onto the stack
        generator.traverse_expr(builder, recipient)?;

        // Call the host interface function `nft_mint`
        builder.call(generator.func_by_name("stdlib.nft_mint"));

        Ok(())
    }
}

#[derive(Debug)]
pub struct GetOwnerOfNonFungibleToken;

impl Word for GetOwnerOfNonFungibleToken {
    fn name(&self) -> ClarityName {
        "nft-get-owner?".into()
    }
}

impl ComplexWord for GetOwnerOfNonFungibleToken {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut walrus::InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError> {
        check_args!(generator, builder, 2, args.len(), ArgumentCountCheck::Exact);

        let token = args.get_name(0)?;
        let identifier = args.get_expr(1)?;

        // Push the token name onto the stack
        let (id_offset, id_length) = generator.add_string_literal(token)?;
        builder
            .i32_const(id_offset as i32)
            .i32_const(id_length as i32);

        self.charge(generator, builder, id_length)?;

        // Push the identifier onto the stack
        let identifier_ty = generator.nft_types.get(token).cloned().ok_or_else(|| {
            GeneratorError::TypeError("Usage of nft-get-owner? on an unknown nft token".to_owned())
        })?;
        generator.set_expr_type(identifier, identifier_ty.clone())?;
        generator.traverse_expr(builder, identifier)?;

        // Allocate space on the stack for the identifier
        let (id_offset, id_size) =
            generator.create_call_stack_local(builder, &identifier_ty, true, false);

        // Write the identifier to the stack (since the host needs to handle generic types)
        generator.write_to_memory(builder, id_offset, 0, &identifier_ty)?;

        // Push the offset and size to the data stack
        builder.local_get(id_offset).i32_const(id_size);

        // Reserve stack space for the return value, a principal
        let return_offset;
        let return_size;
        (return_offset, return_size) =
            generator.create_call_stack_local(builder, &TypeSignature::PrincipalType, false, true);

        // Push the offset and size to the data stack
        builder.local_get(return_offset).i32_const(return_size);

        // Call the host interface function `nft_get_owner`
        builder.call(generator.func_by_name("stdlib.nft_get_owner"));

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use clarity::vm::types::{PrincipalData, TupleData};
    use clarity::vm::Value;

    use crate::tools::{crosscheck, crosscheck_expect_failure, evaluate};

    //
    // Module with tests that should only be executed
    // when running Clarity::V1.
    //
    #[cfg(feature = "test-clarity-v1")]
    mod clarity_v1 {
        use clarity::types::StacksEpochId;

        use super::*;
        use crate::tools::crosscheck_with_epoch;

        #[test]
        fn validate_define_fungible_tokens_epoch() {
            // Epoch20
            crosscheck_with_epoch(
                "(define-fungible-token index-of? u100)",
                Ok(None),
                StacksEpochId::Epoch20,
            );

            crosscheck_expect_failure("(define-fungible-token index-of? u100)");
        }

        #[test]
        fn validate_define_non_fungible_tokens_epoch() {
            // Epoch20
            crosscheck_with_epoch(
                "(define-non-fungible-token index-of? (buff 50))",
                Ok(None),
                StacksEpochId::Epoch20,
            );

            crosscheck_expect_failure("(define-non-fungible-token index-of? (buff 50))");
        }
    }

    #[test]
    fn define_fungible_tokens_less_than_one_arg() {
        let result = evaluate("(define-fungible-token)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting >= 1 arguments, got 0"));
    }

    #[test]
    fn define_fungible_tokens_more_than_two_args() {
        let result = evaluate("(define-fungible-token some-token u100 u1)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 1 arguments, got 3"));
    }

    #[test]
    fn ft_burn_less_than_three_args() {
        let result = evaluate("(ft-burn? bar u100)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 3 arguments, got 2"));
    }

    #[test]
    fn ft_burn_more_than_three_args() {
        let result = evaluate("(ft-burn? bar u100 tx-sender 0x12345678)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 3 arguments, got 4"));
    }

    #[test]
    fn ft_transfer_less_than_four_args() {
        let result = evaluate("(ft-transfer? bar u100 tx-sender)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 4 arguments, got 3"));
    }

    #[test]
    fn ft_transfer_more_than_four_args() {
        let result = evaluate("(ft-transfer? bar u100 tx-sender tx-recipient 0x12345678)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 4 arguments, got 5"));
    }

    #[test]
    fn ft_mint_less_than_three_args() {
        let result = evaluate("(ft-mint? bar u100)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 3 arguments, got 2"));
    }

    #[test]
    fn ft_mint_more_than_three_args() {
        let result = evaluate("(ft-mint? bar u100 tx-sender 0x12345678)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 3 arguments, got 4"));
    }

    #[test]
    fn ft_get_supply_less_than_one_arg() {
        let result = evaluate("(ft-get-supply)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 1 arguments, got 0"));
    }

    #[test]
    fn ft_get_supply_more_than_one_arg() {
        let result = evaluate("(ft-get-supply bar u100)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 1 arguments, got 2"));
    }

    #[test]
    fn ft_get_balance_less_than_two_args() {
        let result = evaluate("(ft-get-balance bar)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 1"));
    }

    #[test]
    fn ft_get_balance_more_than_two_args() {
        let result = evaluate("(ft-get-balance bar u100 tx-sender)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 3"));
    }

    #[test]
    fn define_non_fungible_tokens_less_than_two_args() {
        let result = evaluate("(define-non-fungible-token)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 0"));
    }

    #[test]
    fn define_non_fungible_tokens_more_than_two_args() {
        let result = evaluate("(define-non-fungible-token bar (buff 50) u100)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 3"));
    }

    #[test]
    fn nft_burn_less_than_three_args() {
        let result = evaluate("(nft-burn? bar u100)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 3 arguments, got 2"));
    }

    #[test]
    fn nft_burn_more_than_three_args() {
        let result = evaluate("(nft-burn? bar u100 tx-sender 0x12345678)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 3 arguments, got 4"));
    }

    #[test]
    fn nft_transfer_less_than_four_args() {
        let result = evaluate("(nft-transfer? bar u100 tx-sender)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 4 arguments, got 3"));
    }

    #[test]
    fn nft_transfer_more_than_four_args() {
        let result = evaluate("(nft-transfer? bar u100 tx-sender tx-recipient 0x12345678)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 4 arguments, got 5"));
    }

    #[test]
    fn nft_mint_less_than_three_args() {
        let result = evaluate("(nft-mint? bar u100)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 3 arguments, got 2"));
    }

    #[test]
    fn nft_mint_more_than_three_args() {
        let result = evaluate("(nft-mint? bar u100 tx-sender 0x12345678)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 3 arguments, got 4"));
    }

    #[test]
    fn nft_get_owner_less_than_two_args() {
        let result = evaluate("(nft-get-owner? bar)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 1"));
    }

    #[test]
    fn nft_get_owner_more_than_two_args() {
        let result = evaluate("(nft-get-owner? bar u100 tx-sender)");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expecting 2 arguments, got 3"));
    }
    #[test]
    fn bar_mint_too_many() {
        crosscheck_expect_failure("(ft-mint? bar u1000001 tx-sender)");
    }

    #[test]
    fn bar_mint_too_many_2() {
        const ERR: &str = r#"
          (define-public (bar-mint-too-many-2)
            (begin
              (unwrap-panic (ft-mint? bar u5555555 tx-sender))
              (ft-mint? bar u5555555 'ST1PQHQKV0RJXZFY1DGX8MNSNYVE3VGZJSRTPGZGM)))
          (bar-mint-too-many-2)
        "#;

        crosscheck_expect_failure(ERR);
    }

    #[test]
    fn validate_define_fungible_tokens() {
        // Reserved keyword
        crosscheck_expect_failure("(define-fungible-token map u100)");

        // Custom fungible token name
        crosscheck("(define-fungible-token a u100)", Ok(None));

        // Custom fungible token name duplicate
        crosscheck_expect_failure("(define-fungible-token a u100) (define-fungible-token a u100)");
    }

    #[test]
    fn validate_define_non_fungible_tokens() {
        // Reserved keyword
        crosscheck_expect_failure("(define-non-fungible-token map (buff 50))");

        // Custom nft name
        crosscheck("(define-non-fungible-token a (buff 50))", Ok(None));

        // Custom nft name duplicate
        crosscheck_expect_failure(
            "(define-non-fungible-token a (buff 50)) (define-non-fungible-token a (buff 50))",
        );
    }

    #[test]
    fn validate_nft_functions_with_optionals() {
        // from [issue #515](https://github.com/stacks-network/clarity-wasm/issues/515)
        let snippet = r#"
            (define-non-fungible-token stackaroo {JCJHgKArcQrz: (string-utf8 30),YMZJ: (optional (buff 25)),ev: (buff 48),ms: int,})
            {
                mint: (nft-mint? stackaroo (tuple (JCJHgKArcQrz u"h\u{FEFF}=q:Uc:\u{F9BBB}\u{9}B3'\u{70CED}\u{A}W%\u{202E}{:\u{6CEA1}'\u{3ACDD}\u{E7000}Ul$\u{FB}\u{468}R") (YMZJ none) (ev 0xfe6c9e104fbf8259c4d35cfc9047ebe3db0e4eccaa4eafad5959ccebc1b3730c463f778200fe3e87c25678322a073956) (ms -112969277120374636135691771896584435906)) 'SS5V2M24Z6WSK5PWMPTNQZNRKE15NKE5KV9PG69J),
                owner: (nft-get-owner? stackaroo (tuple (JCJHgKArcQrz u"h\u{FEFF}=q:Uc:\u{F9BBB}\u{9}B3'\u{70CED}\u{A}W%\u{202E}{:\u{6CEA1}'\u{3ACDD}\u{E7000}Ul$\u{FB}\u{468}R") (YMZJ none) (ev 0xfe6c9e104fbf8259c4d35cfc9047ebe3db0e4eccaa4eafad5959ccebc1b3730c463f778200fe3e87c25678322a073956) (ms -112969277120374636135691771896584435906))),
            }
        "#;

        let expected = Value::from(
            TupleData::from_data(vec![
                ("mint".into(), Value::okay_true()),
                (
                    "owner".into(),
                    Value::some(Value::Principal(
                        PrincipalData::parse_standard_principal(
                            "SS5V2M24Z6WSK5PWMPTNQZNRKE15NKE5KV9PG69J",
                        )
                        .unwrap()
                        .into(),
                    ))
                    .unwrap(),
                ),
            ])
            .unwrap(),
        );

        crosscheck(snippet, Ok(Some(expected)));
    }
}
