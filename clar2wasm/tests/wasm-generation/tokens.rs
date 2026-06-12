use clar2wasm::tools::crosscheck;
use clarity::vm::types::signatures::TypeSignature::PrincipalType;
use clarity::vm::types::TupleData;
use clarity::vm::{ClarityName, Value};
use proptest::prelude::*;

use crate::{PropValue, TypePrinter};

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn nft_mint_get_owner(
        nft in PropValue::any(),
        owner in PropValue::from_type(PrincipalType),
    ) {
        let snippet = format!(r#"
            (define-non-fungible-token stackaroo {})
            {{
                mint: (nft-mint? stackaroo {nft} {owner}),
                owner: (nft-get-owner? stackaroo {nft}),
            }}
        "#, nft.type_string());

        let expected = Value::from(
            TupleData::from_data(vec![
                (
                    ClarityName::from_literal("mint"),
                    Value::okay_true(),
                ),
                (
                    ClarityName::from_literal("owner"),
                    Value::some(owner.into()).unwrap(),
                ),
            ])
            .unwrap(),
        );

        crosscheck(&snippet, Ok(Some(expected)));
    }

    #[test]
    fn nft_mint_transfer_owner(
        nft in PropValue::any(),
        owner1 in PropValue::from_type(PrincipalType),
        owner2 in PropValue::from_type(PrincipalType),
    ) {
        let snippet = format!(r#"
            (define-non-fungible-token stackaroo {})
            {{
                a-mint: (nft-mint? stackaroo {nft} {owner1}),
                b-transfer: (nft-transfer? stackaroo {nft} {owner1} {owner2}),
                c-owner: (nft-get-owner? stackaroo {nft}),
            }}
        "#, nft.type_string());

        let expected = Value::from(
            TupleData::from_data(vec![
                (
                    ClarityName::from_literal("a-mint"),
                    Value::okay_true(),
                ),
                (
                    ClarityName::from_literal("b-transfer"),
                    Value::okay_true(),
                ),
                (
                    ClarityName::from_literal("c-owner"),
                    Value::some(owner2.into()).unwrap(),
                ),
            ])
            .unwrap(),
        );

        crosscheck(&snippet, Ok(Some(expected)));
    }

    #[test]
    fn nft_mint_burn_get_owner(
        nft in PropValue::any(),
        owner in PropValue::from_type(PrincipalType),
    ) {
        let snippet = format!(r#"
            (define-non-fungible-token stackaroo {})
            {{
                a-mint: (nft-mint? stackaroo {nft} {owner}),
                b-burn: (nft-burn? stackaroo {nft} {owner}),
                c-owner: (nft-get-owner? stackaroo {nft}),
            }}
        "#, nft.type_string());

        let expected = Value::from(
            TupleData::from_data(vec![
                (
                    ClarityName::from_literal("a-mint"),
                    Value::okay_true(),
                ),
                (
                    ClarityName::from_literal("b-burn"),
                    Value::okay_true(),
                ),
                (
                    ClarityName::from_literal("c-owner"),
                    Value::none(),
                ),
            ])
            .unwrap(),
        );

        crosscheck(&snippet, Ok(Some(expected)));
    }
}

proptest! {
    #![proptest_config(super::runtime_config())]

    #[test]
    fn ft_mint_balance(
        total_supply in any::<u128>(),
        recipient in PropValue::from_type(PrincipalType),
    ) {
        let snippet = format!(r#"
            (define-fungible-token stackaroo u{total_supply})
            {{
                a-mint: (ft-mint? stackaroo u{total_supply} {recipient}),
                b-balance: (ft-get-balance stackaroo {recipient}),
            }}
        "#);

        let expected = Value::from(
            TupleData::from_data(vec![
                (
                    ClarityName::from_literal("a-mint"),
                    Value::okay_true(),
                ),
                (
                    ClarityName::from_literal("b-balance"),
                    Value::UInt(total_supply),
                ),
            ])
            .unwrap(),
        );

        crosscheck(&snippet, Ok(Some(expected)));
    }

    #[test]
    fn ft_mint_burn(
        total_supply in any::<u128>(),
        recipient in PropValue::from_type(PrincipalType),
    ) {
        let snippet = format!(r#"
            (define-fungible-token stackaroo u{total_supply})
            {{
                a-mint: (ft-mint? stackaroo u{total_supply} {recipient}),
                b-burn: (ft-burn? stackaroo u{total_supply} {recipient}),
                c-balance: (ft-get-balance stackaroo {recipient}),
            }}
        "#);

        let expected = Value::from(
            TupleData::from_data(vec![
                (
                    ClarityName::from_literal("a-mint"),
                    Value::okay_true(),
                ),
                (
                    ClarityName::from_literal("b-burn"),
                    Value::okay_true(),
                ),
                (
                    ClarityName::from_literal("c-balance"),
                    Value::UInt(0),
                ),
            ])
            .unwrap(),
        );

        crosscheck(&snippet, Ok(Some(expected)));
    }

    #[test]
    fn ft_mint_mint_supply_transfer_balance(
        total_supply in any::<u128>(),
        sender in PropValue::from_type(PrincipalType),
        recipient in PropValue::from_type(PrincipalType),
    ) {
        let mint_supply = total_supply / 2;

        let snippet = format!(r#"
            (define-fungible-token stackaroo u{total_supply})
            {{
                a-mint1: (ft-mint? stackaroo u{mint_supply} {sender}),
                b-mint2: (ft-mint? stackaroo u{mint_supply} {recipient}),
                c-supply: (ft-get-supply stackaroo),
                d-transfer: (ft-transfer? stackaroo u{mint_supply} {sender} {recipient}),
                e-balance-sender: (ft-get-balance stackaroo {sender}),
                f-balance-recipient: (ft-get-balance stackaroo {recipient}),
            }}
        "#);

        let expected = Value::from(
            TupleData::from_data(vec![
                (
                    ClarityName::from_literal("a-mint1"),
                    Value::okay_true(),
                ),
                (
                    ClarityName::from_literal("b-mint2"),
                    Value::okay_true(),
                ),
                (
                    ClarityName::from_literal("c-supply"),
                    Value::UInt(mint_supply * 2),
                ),
                (
                    ClarityName::from_literal("d-transfer"),
                    Value::okay_true(),
                ),
                (
                    ClarityName::from_literal("e-balance-sender"),
                    Value::UInt(0),
                ),
                (
                    ClarityName::from_literal("f-balance-recipient"),
                    Value::UInt(mint_supply * 2),
                ),
            ])
            .unwrap(),
        );

        crosscheck(&snippet, Ok(Some(expected)));
    }
}
