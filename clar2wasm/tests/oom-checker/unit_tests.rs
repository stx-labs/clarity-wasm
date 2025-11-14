use clar2wasm::tools::{interpret, TestEnvironment};
use clarity::vm::types::{PrincipalData, TypeSignature};
use clarity::vm::Value;

use crate::{
    crosscheck_oom, crosscheck_oom_with_env, crosscheck_oom_with_non_literal_args, list_of,
};

#[test]
fn principal_of_oom() {
    crosscheck_oom(
        "(principal-of? 0x03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba7786110)",
        Ok(Some(
            Value::okay(
                PrincipalData::parse("ST1AW6EKPGT61SQ9FNVDS17RKNWT8ZP582VF9HSCP")
                    .unwrap()
                    .into(),
            )
            .unwrap(),
        )),
    )
}

#[test]
fn list_oom() {
    crosscheck_oom(
        "(list 1 2 3)",
        Ok(Some(
            Value::cons_list_unsanitized(vec![Value::Int(1), Value::Int(2), Value::Int(3)])
                .unwrap(),
        )),
    );
}

#[test]
fn append_oom() {
    crosscheck_oom_with_non_literal_args(
        "(append (list 1 2 3) 4)",
        &[list_of(TypeSignature::IntType, 3)],
        Ok(Some(
            Value::cons_list_unsanitized(vec![
                Value::Int(1),
                Value::Int(2),
                Value::Int(3),
                Value::Int(4),
            ])
            .unwrap(),
        )),
    );
}

#[test]
fn concat_oom() {
    crosscheck_oom_with_non_literal_args(
        "(concat (list 1 2 3) (list 4 5))",
        &[
            list_of(TypeSignature::IntType, 3),
            list_of(TypeSignature::IntType, 2),
        ],
        Ok(Some(
            Value::cons_list_unsanitized(vec![
                Value::Int(1),
                Value::Int(2),
                Value::Int(3),
                Value::Int(4),
                Value::Int(5),
            ])
            .unwrap(),
        )),
    );
}

#[test]
fn map_oom() {
    crosscheck_oom_with_non_literal_args(
        "(define-private (foo (b bool)) (if b u1 u0)) (map foo (list true true false))",
        &[list_of(TypeSignature::BoolType, 3)],
        Ok(Some(
            Value::cons_list_unsanitized(vec![Value::UInt(1), Value::UInt(1), Value::UInt(0)])
                .unwrap(),
        )),
    )
}

#[test]
fn map_with_allocation_oom() {
    let snippet = "
            (define-private (foo (a (list 100 (buff 79))) (b (buff 79)))
                (append a b)
            )

            (map foo
                (list
                    (list
                        0x7d008ba1f4ed1955af2b67c290f7875aac0014b5d271a69e9b3b7c1d569599eb1d44673f4a63bdc33cc903933bf4c08cfd9ed861fe53767db39c6faf6e1c156433295e75bb24bed21180fdfeb8ce9d
                    )
                    (list
                        0x4baa30e193557d264bf9221b85f1c6bc0785df4af8dac870c8a2f9c67b112a5d7cb747a95f96c828553586e8abf2961a5c8a4e10597e7571b7158d0194de9d561feb634adf6c91887e71dc2a0d978c
                    )
                )
                (list
                    0x51ababa90b38940b6700791bf48329ee7bea78e9d0b59cc597a35b6681a53ddacb76efbc62fdb00cc50f13b0230494d6d3f91be7f8569831a5d546d485261188b0e1787d8fcb1cfb519c22b7f98577
                    0x4e76293871093c0cb1182ebf3affbafb8dbb445e7183a97758190116b557f8e63fef3c758752e6e11d0caec4dce3f3abcaeb650558959f120299ccd0a06e17d9444f42bc9f7801bc13941687d84e33
                )
            )
    ";
    let args_types = &[
        list_of(
            list_of(
                TypeSignature::SequenceType(clarity_types::types::SequenceSubtype::BufferType(
                    4u32.try_into().unwrap(),
                )),
                1,
            ),
            1,
        ),
        list_of(
            TypeSignature::SequenceType(clarity_types::types::SequenceSubtype::BufferType(
                4u32.try_into().unwrap(),
            )),
            1,
        ),
    ];
    let expected = interpret("(list (list 0x7d008ba1f4ed1955af2b67c290f7875aac0014b5d271a69e9b3b7c1d569599eb1d44673f4a63bdc33cc903933bf4c08cfd9ed861fe53767db39c6faf6e1c156433295e75bb24bed21180fdfeb8ce9d 0x51ababa90b38940b6700791bf48329ee7bea78e9d0b59cc597a35b6681a53ddacb76efbc62fdb00cc50f13b0230494d6d3f91be7f8569831a5d546d485261188b0e1787d8fcb1cfb519c22b7f98577) (list 0x4baa30e193557d264bf9221b85f1c6bc0785df4af8dac870c8a2f9c67b112a5d7cb747a95f96c828553586e8abf2961a5c8a4e10597e7571b7158d0194de9d561feb634adf6c91887e71dc2a0d978c 0x4e76293871093c0cb1182ebf3affbafb8dbb445e7183a97758190116b557f8e63fef3c758752e6e11d0caec4dce3f3abcaeb650558959f120299ccd0a06e17d9444f42bc9f7801bc13941687d84e33))");
    crosscheck_oom_with_non_literal_args(snippet, args_types, expected);
}

#[test]
fn fold_oom() {
    let snippet = r#"
(define-private (concat-buff (a (buff 1)) (b (buff 3)))
  (unwrap-panic (as-max-len? (concat a b) u3)))
(fold concat-buff 0x010203 0x)
    "#;
    crosscheck_oom(snippet, Ok(Some(Value::buff_from(vec![3, 2, 1]).unwrap())));
}

#[test]
fn get_block_info_burnchain_header_hash_oom() {
    let mut env = TestEnvironment::new(
        clarity::types::StacksEpochId::Epoch25,
        clarity::vm::ClarityVersion::Clarity2,
    );
    env.advance_chain_tip(1);

    crosscheck_oom_with_env(
        "(get-block-info? burnchain-header-hash u0)",
        Ok(Some(
            Value::some(Value::buff_from(vec![0; 32]).unwrap()).unwrap(),
        )),
        env,
    );
}

#[test]
fn get_block_info_id_header_hash_oom() {
    let mut env = TestEnvironment::new(
        clarity::types::StacksEpochId::Epoch25,
        clarity::vm::ClarityVersion::Clarity2,
    );
    env.advance_chain_tip(1);

    crosscheck_oom_with_env(
        "(get-block-info? id-header-hash u0)",
        Ok(Some(
            Value::some(
                // same result as in get_block_info_header_hash() test
                Value::buff_from(vec![
                    181, 224, 118, 171, 118, 9, 199, 248, 199, 99, 181, 197, 113, 208, 122, 234,
                    128, 176, 107, 65, 69, 34, 49, 177, 67, 115, 112, 244, 150, 78, 214, 110,
                ])
                .unwrap(),
            )
            .unwrap(),
        )),
        env,
    );
}

#[test]
fn get_block_info_header_hash_oom() {
    let mut env = TestEnvironment::new(
        clarity::types::StacksEpochId::Epoch25,
        clarity::vm::ClarityVersion::Clarity2,
    );
    env.advance_chain_tip(1);

    crosscheck_oom_with_env(
        "(get-block-info? header-hash u0)",
        Ok(Some(
            Value::some(Value::buff_from(vec![0; 32]).unwrap()).unwrap(),
        )),
        env,
    );
}

#[test]
fn get_block_info_miner_address_oom() {
    let mut env = TestEnvironment::new(
        clarity::types::StacksEpochId::Epoch25,
        clarity::vm::ClarityVersion::Clarity2,
    );
    env.advance_chain_tip(1);

    crosscheck_oom_with_env(
        "(get-block-info? miner-address u0)",
        Ok(Some(
            Value::some(Value::Principal(
                PrincipalData::parse("ST000000000000000000002AMW42H").unwrap(),
            ))
            .unwrap(),
        )),
        env,
    );
}

#[test]
fn get_burn_block_info_header_hash_oom() {
    let mut env = TestEnvironment::new(
        clarity::types::StacksEpochId::Epoch25,
        clarity::vm::ClarityVersion::Clarity2,
    );
    env.advance_chain_tip(1);

    crosscheck_oom_with_env(
        "(get-burn-block-info? header-hash u0)",
        Ok(Some(
            Value::some(Value::buff_from(vec![0; 32]).unwrap()).unwrap(),
        )),
        env,
    );
}

#[test]
fn get_burn_block_info_pox_addrs_oom() {
    let mut env = TestEnvironment::new(
        clarity::types::StacksEpochId::Epoch25,
        clarity::vm::ClarityVersion::Clarity2,
    );
    env.advance_chain_tip(1);

    crosscheck_oom_with_env(
        "(get-burn-block-info? pox-addrs u0)",
        Ok(Some(
            Value::some(
                clarity::vm::types::TupleData::from_data(vec![
                    (
                        "addrs".into(),
                        Value::cons_list_unsanitized(vec![
                            clarity::vm::types::TupleData::from_data(vec![
                                (
                                    "hashbytes".into(),
                                    Value::buff_from([0; 32].to_vec()).unwrap(),
                                ),
                                ("version".into(), Value::buff_from_byte(0)),
                            ])
                            .unwrap()
                            .into(),
                        ])
                        .unwrap(),
                    ),
                    ("payout".into(), Value::UInt(0)),
                ])
                .unwrap()
                .into(),
            )
            .unwrap(),
        )),
        env,
    );
}

#[test]
fn data_var_oom() {
    crosscheck_oom(
        r#"
        (define-data-var n (buff 1) 0x)
        (var-set n 0x42)
        (var-get n)
    "#,
        Ok(Some(Value::buff_from_byte(0x42))),
    );
}

#[test]
fn secp256k1_recover_oom() {
    crosscheck_oom(
        "(secp256k1-recover? 0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04 0x8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a1301)",
        Ok(Some(Value::okay(Value::buff_from(vec![3, 173, 184, 222, 75, 251, 101, 219, 44, 253, 97, 32, 213, 92, 101, 38, 174, 156, 82, 230, 117, 219, 126, 71, 48, 134, 54, 83, 75, 167, 120, 97, 16]).unwrap()).unwrap())),
    );
}

#[cfg(not(feature = "test-clarity-v1"))]
#[cfg(test)]
mod clarity_v2_v3 {
    use clarity::vm::types::{PrincipalData, TypeSignature};
    use clarity::vm::Value;

    use crate::{crosscheck_oom, crosscheck_oom_with_non_literal_args, list_of};

    #[test]
    fn principal_construct_oom() {
        crosscheck_oom(
            "(principal-construct? 0x1a 0xfa6bf38ed557fe417333710d6033e9419391a320)",
            Ok(Some(
                Value::okay(
                    PrincipalData::parse("ST3X6QWWETNBZWGBK6DRGTR1KX50S74D3425Q1TPK")
                        .unwrap()
                        .into(),
                )
                .unwrap(),
            )),
        )
    }

    #[test]
    fn replace_at_oom() {
        crosscheck_oom_with_non_literal_args(
            "(replace-at? (list 1 2 3) u0 42)",
            &[list_of(TypeSignature::IntType, 3)],
            Ok(Some(
                Value::some(
                    Value::cons_list_unsanitized(vec![
                        Value::Int(42),
                        Value::Int(2),
                        Value::Int(3),
                    ])
                    .unwrap(),
                )
                .unwrap(),
            )),
        );
    }

    #[test]
    fn int_to_ascii_oom_negative() {
        crosscheck_oom(
            "(int-to-ascii -42)",
            Ok(Some(
                Value::string_ascii_from_bytes(b"-42".to_vec()).unwrap(),
            )),
        );
    }

    #[test]
    fn int_to_utf8_oom_negative() {
        crosscheck_oom(
            "(int-to-utf8 -42)",
            Ok(Some(
                Value::string_utf8_from_bytes(b"-42".to_vec()).unwrap(),
            )),
        );
    }

    #[test]
    fn int_to_ascii_oom() {
        crosscheck_oom(
            "(int-to-ascii 42)",
            Ok(Some(
                Value::string_ascii_from_bytes(b"42".to_vec()).unwrap(),
            )),
        );
    }

    #[test]
    fn int_to_utf8_oom() {
        crosscheck_oom(
            "(int-to-utf8 42)",
            Ok(Some(Value::string_utf8_from_bytes(b"42".to_vec()).unwrap())),
        );
    }

    #[test]
    fn unsigned_value_int_to_ascii_oom() {
        crosscheck_oom(
            "(int-to-ascii u42)",
            Ok(Some(
                Value::string_ascii_from_bytes(b"42".to_vec()).unwrap(),
            )),
        );
    }

    #[test]
    fn unsigned_value_int_to_utf8_oom() {
        crosscheck_oom(
            "(int-to-utf8 u42)",
            Ok(Some(Value::string_utf8_from_bytes(b"42".to_vec()).unwrap())),
        );
    }
}
