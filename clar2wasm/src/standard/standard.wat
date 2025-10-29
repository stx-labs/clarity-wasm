;; This module contains a standard library for Clarity, defining Clarity's
;; builtins, to be called from the generated Wasm code.
(module
    (type (;0;) (func (param i32)))
    (type (;1;) (func (param $a_lo i64) (param $a_hi i64) (param $b_lo i64) (param $b_hi i64) (result i64 i64)))
    (type (;2;) (func (param $a_lo i64) (param $a_hi i64) (param $b_lo i64) (param $b_hi i64) (result i64 i64 i64 i64)))
    (type (;3;) (func (param i64 i64) (result i64 i64)))
    (type (;4;) (func (param i32 i32 i32) (result i32)))
    (type (;5;) (func (param $a_lo i64) (param $a_hi i64) (param $b_lo i64) (param $b_hi i64) (result i32)))
    (type (;6;) (func (param $offset i32) (param $length i32) (param $offset-result i32) (result i32 i32)))
    (type (;7;) (func (param $lo i64) (param $hi i64) (param $offset-result i32) (result i32 i32)))
    (type (;8;) (func (param $bool_in i32) (result i32)))
    (type (;9;) (func (param $offset_a i32) (param $length_a i32) (param $offset_b i32) (param $length_b i32) (result i32)))

    ;; Importing Clarity functions that are not natively available in WebAssembly.
    ;; Functions imported for host interface.
    (import "clarity" "define_function" (func $stdlib.define_function (param $kind i32)
                                                               (param $name_offset i32)
                                                               (param $name_length i32)))
    (import "clarity" "define_variable" (func $stdlib.define_variable (param $name_offset i32)
                                                               (param $name_length i32)
                                                               (param $initial_value_offset i32)
                                                               (param $initial_value_length i32)))
    (import "clarity" "define_ft" (func $stdlib.define_ft (param $name_offset i32)
                                                   (param $name_length i32)
                                                   (param $supply_indicator i32)
                                                   (param $supply_lo i64)
                                                   (param $supply_hi i64)))
    (import "clarity" "define_nft" (func $stdlib.define_nft (param $name_offset i32)
                                                     (param $name_length i32)))
    (import "clarity" "define_map" (func $stdlib.define_map (param $name_offset i32)
                                                     (param $name_length i32)))
    (import "clarity" "define_trait" (func $stdlib.define_trait (param $name_offset i32)
                                                         (param $name_length i32)))
    (import "clarity" "impl_trait" (func $stdlib.impl_trait (param $trait_offset i32)
                                                     (param $trait_length i32)))

    (import "clarity" "get_variable" (func $stdlib.get_variable (param $name_offset i32)
                                                         (param $name_length i32)
                                                         (param $return_offset i32)
                                                         (param $return_length i32)))
    (import "clarity" "set_variable" (func $stdlib.set_variable (param $name_offset i32)
                                                         (param $name_length i32)
                                                         (param $value_offset i32)
                                                         (param $value_length i32)))
    (import "clarity" "print" (func $stdlib.print (param $value_offset i32)
                                                  (param $value_length i32)
                                                  (param $serialized_ty_offset i32)
                                                  (param $serialized_ty_length i32)))
    (import "clarity" "enter_as_contract" (func $stdlib.enter_as_contract))
    (import "clarity" "exit_as_contract" (func $stdlib.exit_as_contract))
    (import "clarity" "enter_at_block" (func $stdlib.enter_at_block (param $block_hash_offset i32)
                                                             (param $block_hash_length i32)))
    (import "clarity" "exit_at_block" (func $stdlib.exit_at_block))
    (import "clarity" "stx_get_balance" (func $stdlib.stx_get_balance (param $principal_offset i32)
                                                               (param $principal_length i32)
                                                               (result i64 i64)))
    (import "clarity" "stx_account" (func $stdlib.stx_account (param $principal_offset i32)
                                                       (param $principal_length i32)
                                                       (result i64 i64 i64 i64 i64 i64)))
    (import "clarity" "stx_burn" (func $stdlib.stx_burn (param $amount_lo i64)
                                                 (param $amount_hi i64)
                                                 (param $principal_offset i32)
                                                 (param $principal_length i32)
                                                 (result i32 i32 i64 i64)))
    (import "clarity" "stx_transfer" (func $stdlib.stx_transfer (param $amount_lo i64)
                                                         (param $amount_hi i64)
                                                         (param $sender_offset i32)
                                                         (param $sender_length i32)
                                                         (param $recipient_offset i32)
                                                         (param $recipient_length i32)
                                                         (param $memo_offset i32)
                                                         (param $memo_length i32)
                                                         (result i32 i32 i64 i64)))

    (import "clarity" "ft_get_supply" (func $stdlib.ft_get_supply (param $name_offset i32)
                                                           (param $name_length i32)
                                                           (result i64 i64)))
    (import "clarity" "ft_get_balance" (func $stdlib.ft_get_balance (param $name_offset i32)
                                                             (param $name_length i32)
                                                             (param $owner_offset i32)
                                                             (param $owner_length i32)
                                                             (result i64 i64)))
    (import "clarity" "ft_burn" (func $stdlib.ft_burn (param $name_offset i32)
                                               (param $name_length i32)
                                               (param $amount_lo i64)
                                               (param $amount_hi i64)
                                               (param $sender_offset i32)
                                               (param $sender_length i32)
                                               (result i32 i32 i64 i64)))
    (import "clarity" "ft_mint" (func $stdlib.ft_mint (param $name_offset i32)
                                               (param $name_length i32)
                                               (param $amount_lo i64)
                                               (param $amount_hi i64)
                                               (param $sender_offset i32)
                                               (param $sender_length i32)
                                               (result i32 i32 i64 i64)))
    (import "clarity" "ft_transfer" (func $stdlib.ft_transfer (param $name_offset i32)
                                                       (param $name_length i32)
                                                       (param $amount_lo i64)
                                                       (param $amount_hi i64)
                                                       (param $sender_offset i32)
                                                       (param $sender_length i32)
                                                       (param $recipient_offset i32)
                                                       (param $recipient_length i32)
                                                       (result i32 i32 i64 i64)))
    (import "clarity" "nft_get_owner" (func $stdlib.nft_get_owner (param $name_offset i32)
                                                           (param $name_length i32)
                                                           (param $asset_offset i32)
                                                           (param $asset_length i32)
                                                           (param $return_offset i32)
                                                           (param $return_length i32)
                                                           (result i32 i32 i32)))
    (import "clarity" "nft_burn" (func $stdlib.nft_burn (param $name_offset i32)
                                                 (param $name_length i32)
                                                 (param $asset_offset i32)
                                                 (param $asset_length i32)
                                                 (param $sender_offset i32)
                                                 (param $sender_length i32)
                                                 (result i32 i32 i64 i64)))
    (import "clarity" "nft_mint" (func $stdlib.nft_mint (param $name_offset i32)
                                                 (param $name_length i32)
                                                 (param $asset_offset i32)
                                                 (param $asset_length i32)
                                                 (param $recipient_offset i32)
                                                 (param $recipient_length i32)
                                                 (result i32 i32 i64 i64)))
    (import "clarity" "nft_transfer" (func $stdlib.nft_transfer (param $name_offset i32)
                                                         (param $name_length i32)
                                                         (param $asset_offset i32)
                                                         (param $asset_length i32)
                                                         (param $sender_offset i32)
                                                         (param $sender_length i32)
                                                         (param $recipient_offset i32)
                                                         (param $recipient_length i32)
                                                         (result i32 i32 i64 i64)))
    (import "clarity" "map_get" (func $stdlib.map_get (param $name_offset i32)
                                               (param $name_length i32)
                                               (param $key_offset i32)
                                               (param $key_length i32)
                                               (param $return_offset i32)
                                               (param $return_length i32)))
    (import "clarity" "map_set" (func $stdlib.map_set (param $name_offset i32)
                                               (param $name_length i32)
                                               (param $key_offset i32)
                                               (param $key_length i32)
                                               (param $value_offset i32)
                                               (param $value_length i32)
                                               (result i32)))
    (import "clarity" "map_insert" (func $stdlib.map_insert (param $name_offset i32)
                                                     (param $name_length i32)
                                                     (param $key_offset i32)
                                                     (param $key_length i32)
                                                     (param $value_offset i32)
                                                     (param $value_length i32)
                                                     (result i32)))
    (import "clarity" "map_delete" (func $stdlib.map_delete (param $name_offset i32)
                                                     (param $name_length i32)
                                                     (param $key_offset i32)
                                                     (param $key_length i32)
                                                     (result i32)))
    (import "clarity" "get_block_info_time_property" (func $stdlib.get_block_info_time_property (param $height_lo i64)
                                                             (param $height_hi i64)
                                                             (param $return_offset i32)
                                                             (param $return_length i32)))
    (import "clarity" "get_block_info_vrf_seed_property" (func $stdlib.get_block_info_vrf_seed_property (param $height_lo i64)
                                                             (param $height_hi i64)
                                                             (param $return_offset i32)
                                                             (param $return_length i32)))
    (import "clarity" "get_block_info_header_hash_property" (func $stdlib.get_block_info_header_hash_property (param $height_lo i64)
                                                             (param $height_hi i64)
                                                             (param $return_offset i32)
                                                             (param $return_length i32)))
    (import "clarity" "get_block_info_burnchain_header_hash_property" (func $stdlib.get_block_info_burnchain_header_hash_property (param $height_lo i64)
                                                             (param $height_hi i64)
                                                             (param $return_offset i32)
                                                             (param $return_length i32)))
    (import "clarity" "get_block_info_identity_header_hash_property" (func $stdlib.get_block_info_identity_header_hash_property (param $height_lo i64)
                                                             (param $height_hi i64)
                                                             (param $return_offset i32)
                                                             (param $return_length i32)))
    (import "clarity" "get_block_info_miner_address_property" (func $stdlib.get_block_info_miner_address_property (param $height_lo i64)
                                                             (param $height_hi i64)
                                                             (param $return_offset i32)
                                                             (param $return_length i32)))
    (import "clarity" "get_block_info_miner_spend_winner_property" (func $stdlib.get_block_info_miner_spend_winner_property (param $height_lo i64)
                                                             (param $height_hi i64)
                                                             (param $return_offset i32)
                                                             (param $return_length i32)))
    (import "clarity" "get_block_info_miner_spend_total_property" (func $stdlib.get_block_info_miner_spend_total_property (param $height_lo i64)
                                                             (param $height_hi i64)
                                                             (param $return_offset i32)
                                                             (param $return_length i32)))
    (import "clarity" "get_block_info_block_reward_property" (func $stdlib.get_block_info_block_reward_property (param $height_lo i64)
                                                             (param $height_hi i64)
                                                             (param $return_offset i32)
                                                             (param $return_length i32)))
    (import "clarity" "get_burn_block_info_header_hash_property" (func $stdlib.get_burn_block_info_header_hash_property (param $height_lo i64)
                                                             (param $height_hi i64)
                                                             (param $return_offset i32)
                                                             (param $return_length i32)))
    (import "clarity" "get_burn_block_info_pox_addrs_property" (func $stdlib.get_burn_block_info_pox_addrs_property (param $height_lo i64)
                                                             (param $height_hi i64)
                                                             (param $return_offset i32)
                                                             (param $return_length i32)))
    (import "clarity" "get_stacks_block_info_time_property" (func $stdlib.get_stacks_block_info_time_property (param $height_lo i64)
                                                             (param $height_hi i64)
                                                             (param $return_offset i32)
                                                             (param $return_length i32)))
    (import "clarity" "get_stacks_block_info_header_hash_property" (func $stdlib.get_stacks_block_info_header_hash_property (param $height_lo i64)
                                                             (param $height_hi i64)
                                                             (param $return_offset i32)
                                                             (param $return_length i32)))
    (import "clarity" "get_stacks_block_info_identity_header_hash_property" (func $stdlib.get_stacks_block_info_identity_header_hash_property (param $height_lo i64)
                                                             (param $height_hi i64)
                                                             (param $return_offset i32)
                                                             (param $return_length i32)))
    (import "clarity" "get_tenure_info_burnchain_header_hash_property" (func $stdlib.get_tenure_info_burnchain_header_hash_property (param $height_lo i64)
                                                             (param $height_hi i64)
                                                             (param $return_offset i32)
                                                             (param $return_length i32)))
    (import "clarity" "get_tenure_info_miner_address_property" (func $stdlib.get_tenure_info_miner_address_property (param $height_lo i64)
                                                             (param $height_hi i64)
                                                             (param $return_offset i32)
                                                             (param $return_length i32)))
    (import "clarity" "get_tenure_info_time_property" (func $stdlib.get_tenure_info_time_property (param $height_lo i64)
                                                             (param $height_hi i64)
                                                             (param $return_offset i32)
                                                             (param $return_length i32)))
    (import "clarity" "get_tenure_info_vrf_seed_property" (func $stdlib.get_tenure_info_vrf_seed_property (param $height_lo i64)
                                                             (param $height_hi i64)
                                                             (param $return_offset i32)
                                                             (param $return_length i32)))
    (import "clarity" "get_tenure_info_block_reward_property" (func $stdlib.get_tenure_info_block_reward_property (param $height_lo i64)
                                                             (param $height_hi i64)
                                                             (param $return_offset i32)
                                                             (param $return_length i32)))
    (import "clarity" "get_tenure_info_miner_spend_total_property" (func $stdlib.get_tenure_info_miner_spend_total_property (param $height_lo i64)
                                                             (param $height_hi i64)
                                                             (param $return_offset i32)
                                                             (param $return_length i32)))
    (import "clarity" "get_tenure_info_miner_spend_winner_property" (func $stdlib.get_tenure_info_miner_spend_winner_property (param $height_lo i64)
                                                             (param $height_hi i64)
                                                             (param $return_offset i32)
                                                             (param $return_length i32)))
    (import "clarity" "contract_call" (func $stdlib.contract_call (param $trait_id_offset i32)
                                                           (param $trait_id_len i32)
                                                           (param $contract_id_offset i32)
                                                           (param $contract_id_length i32)
                                                           (param $function_name_offset i32)
                                                           (param $function_name_length i32)
                                                           (param $arguments_offset i32)
                                                           (param $arguments_length i32)
                                                           (param $return_offset i32)
                                                           (param $return_length i32)))

    (import "clarity" "begin_public_call" (func $stdlib.begin_public_call))
    (import "clarity" "begin_read_only_call" (func $stdlib.begin_read_only_call))
    (import "clarity" "commit_call" (func $stdlib.commit_call))
    (import "clarity" "roll_back_call" (func $stdlib.roll_back_call))

    (import "clarity" "keccak256" (func $stdlib.keccak256 (param $buffer_offset i32)
                                                   (param $buffer_length i32)
                                                   (param $result_offset i32)
                                                   (param $result_length i32)
                                                   (result i32 i32)))
    (import "clarity" "sha512_256" (func $stdlib.sha512_256 (param $buffer_offset i32)
                                                     (param $buffer_length i32)
                                                     (param $result_offset i32)
                                                     (param $result_length i32)
                                                     (result i32 i32)))
    (import "clarity" "secp256k1_recover" (func $stdlib.secp256k1_recover (param $msg_offset i32)
                                                                   (param $msg_length i32)
                                                                   (param $sig_offset i32)
                                                                   (param $sig_length i32)
                                                                   (param $result_offset i32)
                                                                   (param $result_length i32)))
    (import "clarity" "secp256k1_verify" (func $stdlib.secp256k1_verify (param $msg_offset i32)
                                                                 (param $msg_length i32)
                                                                 (param $sig_offset i32)
                                                                 (param $sig_length i32)
                                                                 (param $pk_offset i32)
                                                                 (param $pk_length i32)
                                                                 (result i32)))
    (import "clarity" "principal_of" (func $stdlib.principal_of (param $key_offset i32)
                                                                (param $key_length i32)
                                                                (param $principal_offset i32)
                                                                (result i32 i32 i32 i64 i64)))

    (import "clarity" "tx_sender" (func $stdlib.tx_sender (param $return_offset i32)
                                                   (param $return_length i32)
                                                   (result i32 i32)))
    (import "clarity" "contract_caller" (func $stdlib.contract_caller (param $return_offset i32)
                                                               (param $return_length i32)
                                                               (result i32 i32)))
    (import "clarity" "tx_sponsor" (func $stdlib.tx_sponsor (param $return_offset i32)
                                                     (param $return_length i32)
                                                     (result i32 i32 i32)))
    (import "clarity" "block_height" (func $stdlib.block_height (result i64 i64)))
    (import "clarity" "stacks_block_height" (func $stdlib.stacks_block_height (result i64 i64)))
    (import "clarity" "tenure_height" (func $stdlib.tenure_height (result i64 i64)))
    (import "clarity" "burn_block_height" (func $stdlib.burn_block_height (result i64 i64)))
    (import "clarity" "stx_liquid_supply" (func $stdlib.stx_liquid_supply (result i64 i64)))
    (import "clarity" "save_constant"
        (func $stdlib.save_constant
            (param $name_offset i32)
            (param $name_length i32)
            (param $value_offset i32)
            (param $value_length i32)))

    (import "clarity" "load_constant"
        (func $stdlib.load_constant
            (param $name_offset i32)
            (param $name_length i32)
            (param $value_offset i32)
            (param $value_length i32)))
    (import "clarity" "skip_list" (func $skip-list (param $offset i32) (param $offset_end i32) (result i32)))

    ;; TODO: these three funcs below could be hard-coded at compile-time.
    (import "clarity" "is_in_regtest" (func $stdlib.is_in_regtest (result i32)))
    (import "clarity" "is_in_mainnet" (func $stdlib.is_in_mainnet (result i32)))
    (import "clarity" "chain_id" (func $stdlib.chain_id (result i64 i64)))

    ;; Useful for debugging, just prints the value
    (import "" "log" (func $log (param $value i64)))

    ;; Useful for debugging, just prints a message
    (import "" "debug_msg" (func $debug_msg (param $value i32)))

    ;; TODO: These are not defined, but instead during compilation, because otherwise we *must* link
    ;;       them in, and the test suite will fail due to some of the runtime code being in
    ;;      `stacks-core`
    ;;
    ;; ;; Cost tracking globals
    ;; (import "clarity" "cost-runtime" (global $cost-runtime (mut i64)))
    ;; (import "clarity" "cost-read-count" (global $cost-read-count (mut i64)))
    ;; (import "clarity" "cost-read-length" (global $cost-read-length (mut i64)))
    ;; (import "clarity" "cost-write-count" (global $cost-write-count (mut i64)))
    ;; (import "clarity" "cost-write-length" (global $cost-write-length (mut i64)))

    ;; Global definitions
    (global $stack-pointer (mut i32) (i32.const 0))
    (global $runtime-error-code (mut i32) (i32.const -1))
    (global $runtime-error-arg-offset (mut i32) (i32.const -1))
    (global $runtime-error-arg-len (mut i32) (i32.const -1))
    (global $runtime-error-value-offset (mut i32) (i32.const -1))
    (global $runtime-error-type-ser-offset (mut i32) (i32.const -1))
    (global $runtime-error-type-ser-len (mut i32) (i32.const -1))

    ;; (sha256) initial hash values: first 32 bits of the fractional parts of the square roots of the first 8 primes 2..19
    (data (i32.const 0) "\67\e6\09\6a\85\ae\67\bb\72\f3\6e\3c\3a\f5\4f\a5\7f\52\0e\51\8c\68\05\9b\ab\d9\83\1f\19\cd\e0\5b")

    ;; (sha256) K constants: first 32 bits of the fractional parts of the cube roots of the first 64 primes 2..311
    (data (i32.const 32) "\98\2f\8a\42\91\44\37\71\cf\fb\c0\b5\a5\db\b5\e9\5b\c2\56\39\f1\11\f1\59\a4\82\3f\92\d5\5e\1c\ab\98\aa\07\d8\01\5b\83\12\be\85\31\24\c3\7d\0c\55\74\5d\be\72\fe\b1\de\80\a7\06\dc\9b\74\f1\9b\c1\c1\69\9b\e4\86\47\be\ef\c6\9d\c1\0f\cc\a1\0c\24\6f\2c\e9\2d\aa\84\74\4a\dc\a9\b0\5c\da\88\f9\76\52\51\3e\98\6d\c6\31\a8\c8\27\03\b0\c7\7f\59\bf\f3\0b\e0\c6\47\91\a7\d5\51\63\ca\06\67\29\29\14\85\0a\b7\27\38\21\1b\2e\fc\6d\2c\4d\13\0d\38\53\54\73\0a\65\bb\0a\6a\76\2e\c9\c2\81\85\2c\72\92\a1\e8\bf\a2\4b\66\1a\a8\70\8b\4b\c2\a3\51\6c\c7\19\e8\92\d1\24\06\99\d6\85\35\0e\f4\70\a0\6a\10\16\c1\a4\19\08\6c\37\1e\4c\77\48\27\b5\bc\b0\34\b3\0c\1c\39\4a\aa\d8\4e\4f\ca\9c\5b\f3\6f\2e\68\ee\82\8f\74\6f\63\a5\78\14\78\c8\84\08\02\c7\8c\fa\ff\be\90\eb\6c\50\a4\f7\a3\f9\be\f2\78\71\c6")

    ;; (hash-160) selection of message word (r)
    (data (i32.const 288) "\00\01\02\03\04\05\06\07\08\09\0a\0b\0c\0d\0e\0f\07\04\0d\01\0a\06\0f\03\0c\00\09\05\02\0e\0b\08\03\0a\0e\04\09\0f\08\01\02\07\00\06\0d\0b\05\0c\01\09\0b\0a\00\08\0c\04\0d\03\07\0f\0e\05\06\02\04\00\05\09\07\0c\02\0a\0e\01\03\08\0b\06\0f\0d")

    ;; (hash-160) selection of message word (r')
    (data (i32.const 368) "\05\0e\07\00\09\02\0b\04\0d\06\0f\08\01\0a\03\0c\06\0b\03\07\00\0d\05\0a\0e\0f\08\0c\04\09\01\02\0f\05\01\03\07\0e\06\09\0b\08\0c\02\0a\00\04\0d\08\06\04\01\03\0b\0f\00\05\0c\02\0d\09\07\0a\0e\0c\0f\0a\04\01\05\08\07\06\02\0d\0e\00\03\09\0b")

    ;; (hash-160) rotate-left amount (s)
    (data (i32.const 448) "\0b\0e\0f\0c\05\08\07\09\0b\0d\0e\0f\06\07\09\08\07\06\08\0d\0b\09\07\0f\07\0c\0f\09\0b\07\0d\0c\0b\0d\06\07\0e\09\0d\0f\0e\08\0d\06\05\0c\07\05\0b\0c\0e\0f\0e\0f\09\08\09\0e\05\06\08\06\05\0c\09\0f\05\0b\06\08\0d\0c\05\0c\0d\0e\0b\08\05\06")

    ;; (hash-160) rotate-left amount (s')
    (data (i32.const 528) "\08\09\09\0b\0d\0f\0f\05\07\07\08\0b\0e\0e\0c\06\09\0d\0f\07\0c\08\09\0b\07\07\0c\07\06\0f\0d\0b\09\07\0f\0b\08\06\06\0e\0c\0d\05\0e\0d\0d\07\05\0f\05\08\0b\0e\0e\06\0e\06\09\0c\09\0c\05\0f\08\08\05\0c\09\0c\05\0e\06\08\0d\06\05\0f\0d\0b\0b")

    ;; (hash-160) K constants
    (data (i32.const 608) "\00\00\00\00\99\79\82\5a\a1\eb\d9\6e\dc\bc\1b\8f\4e\fd\53\a9")

    ;; (hash-160) K' constants
    (data (i32.const 628) "\e6\8b\a2\50\24\d1\4d\5c\f3\3e\70\6d\e9\76\6d\7a\00\00\00\00")

    ;; sha512 initial values (64 bytes)
    (data (i32.const 648) "\08\c9\bc\f3\67\e6\09\6a\3b\a7\ca\84\85\ae\67\bb\2b\f8\94\fe\72\f3\6e\3c\f1\36\1d\5f\3a\f5\4f\a5\d1\82\e6\ad\7f\52\0e\51\1f\6c\3e\2b\8c\68\05\9b\6b\bd\41\fb\ab\d9\83\1f\79\21\7e\13\19\cd\e0\5b")

    ;; sha512 K constants
    (data (i32.const 712) "\22\ae\28\d7\98\2f\8a\42\cd\65\ef\23\91\44\37\71\2f\3b\4d\ec\cf\fb\c0\b5\bc\db\89\81\a5\db\b5\e9\38\b5\48\f3\5b\c2\56\39\19\d0\05\b6\f1\11\f1\59\9b\4f\19\af\a4\82\3f\92\18\81\6d\da\d5\5e\1c\ab\42\02\03\a3\98\aa\07\d8\be\6f\70\45\01\5b\83\12\8c\b2\e4\4e\be\85\31\24\e2\b4\ff\d5\c3\7d\0c\55\6f\89\7b\f2\74\5d\be\72\b1\96\16\3b\fe\b1\de\80\35\12\c7\25\a7\06\dc\9b\94\26\69\cf\74\f1\9b\c1\d2\4a\f1\9e\c1\69\9b\e4\e3\25\4f\38\86\47\be\ef\b5\d5\8c\8b\c6\9d\c1\0f\65\9c\ac\77\cc\a1\0c\24\75\02\2b\59\6f\2c\e9\2d\83\e4\a6\6e\aa\84\74\4a\d4\fb\41\bd\dc\a9\b0\5c\b5\53\11\83\da\88\f9\76\ab\df\66\ee\52\51\3e\98\10\32\b4\2d\6d\c6\31\a8\3f\21\fb\98\c8\27\03\b0\e4\0e\ef\be\c7\7f\59\bf\c2\8f\a8\3d\f3\0b\e0\c6\25\a7\0a\93\47\91\a7\d5\6f\82\03\e0\51\63\ca\06\70\6e\0e\0a\67\29\29\14\fc\2f\d2\46\85\0a\b7\27\26\c9\26\5c\38\21\1b\2e\ed\2a\c4\5a\fc\6d\2c\4d\df\b3\95\9d\13\0d\38\53\de\63\af\8b\54\73\0a\65\a8\b2\77\3c\bb\0a\6a\76\e6\ae\ed\47\2e\c9\c2\81\3b\35\82\14\85\2c\72\92\64\03\f1\4c\a1\e8\bf\a2\01\30\42\bc\4b\66\1a\a8\91\97\f8\d0\70\8b\4b\c2\30\be\54\06\a3\51\6c\c7\18\52\ef\d6\19\e8\92\d1\10\a9\65\55\24\06\99\d6\2a\20\71\57\85\35\0e\f4\b8\d1\bb\32\70\a0\6a\10\c8\d0\d2\b8\16\c1\a4\19\53\ab\41\51\08\6c\37\1e\99\eb\8e\df\4c\77\48\27\a8\48\9b\e1\b5\bc\b0\34\63\5a\c9\c5\b3\0c\1c\39\cb\8a\41\e3\4a\aa\d8\4e\73\e3\63\77\4f\ca\9c\5b\a3\b8\b2\d6\f3\6f\2e\68\fc\b2\ef\5d\ee\82\8f\74\60\2f\17\43\6f\63\a5\78\72\ab\f0\a1\14\78\c8\84\ec\39\64\1a\08\02\c7\8c\28\1e\63\23\fa\ff\be\90\e9\bd\82\de\eb\6c\50\a4\15\79\c6\b2\f7\a3\f9\be\2b\53\72\e3\f2\78\71\c6\9c\61\26\ea\ce\3e\27\ca\07\c2\c0\21\c7\b8\86\d1\1e\eb\e0\cd\d6\7d\da\ea\78\d1\6e\ee\7f\4f\7d\f5\ba\6f\17\72\aa\67\f0\06\a6\98\c8\a2\c5\7d\63\0a\ae\0d\f9\be\04\98\3f\11\1b\47\1c\13\35\0b\71\1b\84\7d\04\23\f5\77\db\28\93\24\c7\40\7b\ab\ca\32\bc\be\c9\15\0a\be\9e\3c\4c\0d\10\9c\c4\67\1d\43\b6\42\3e\cb\be\d4\c5\4c\2a\7e\65\fc\9c\29\7f\59\ec\fa\d6\3a\ab\6f\cb\5f\17\58\47\4a\8c\19\44\6c")

    ;; table that contains the 5 hash160 functions used during compression
    (table 20 funcref)
    ;; table that contains the 5 hash160 functions used during compression (index 0 to 4)
    (type $hash160-compress-function (func (param i32 i32 i32 i32) (result i32)))
    (elem (i32.const 0) $hash160-f1 $hash160-f2 $hash160-f3 $hash160-f4 $hash160-f5)
    ;; table that contains the skip functions for tuple deserialization (index 5 to 19)
    (type $skip-function (func (param i32 i32) (result i32)))
    (elem (i32.const 5) $skip-int128 $skip-int128 $skip-buffer $skip-boolean-or-none $skip-boolean-or-none $skip-principal $skip-contract $skip-some-ok-err $skip-some-ok-err $skip-boolean-or-none $skip-some-ok-err $skip-list $skip-tuple $skip-string-ascii $skip-string-utf8)

    ;; The error code is one of:
        ;; 0: overflow
        ;; 1: underflow
        ;; 2: divide by zero
        ;; 3: log of a number <= 0
        ;; 4: expected a non-negative number
        ;; 5: buffer to integer expects a buffer length <= 16
        ;; 6: panic
        ;; 7: short return
        ;; 100: runtime cost overrun
        ;; 101: read count cost overrun
        ;; 102: read length cost overrun
        ;; 103: write count cost overrun
        ;; 104: write length cost overrun
    (func $stdlib.runtime-error (param $error_code i32)
        (global.set $runtime-error-code (local.get $error_code))

        (unreachable)
    )

    ;; This function can be used to add either signed or unsigned integers
    (func $stdlib.add-int128 (param $a_lo i64) (param $a_hi i64) (param $b_lo i64) (param $b_hi i64) (result i64 i64)
        ;; Add the lower 64 bits
        (local.tee $b_lo (i64.add (local.get $a_lo) (local.get $b_lo))) ;; $b_lo now contains the result lower bits

        ;; Add the upper 64 bits, accounting for any carry from the lower bits
        (i64.add
            (i64.extend_i32_u (i64.gt_u (local.get $a_lo) (local.get $b_lo)))   ;; carry
            (i64.add (local.get $a_hi) (local.get $b_hi)))                      ;; upper 64 bits
    )

    (func $stdlib.add-int (param $a_lo i64) (param $a_hi i64) (param $b_lo i64) (param $b_hi i64) (result i64 i64)
        (local $sum_hi i64)
        (local $sum_lo i64)

        (local.get $a_lo)
        (local.get $a_hi)
        (local.get $b_lo)
        (local.get $b_hi)
        (call $stdlib.add-int128)

        (local.set $sum_hi)
        (local.set $sum_lo)

        ;; Check for overflow and underflow
        (if (i64.eq (i64.shr_s (local.get $a_hi) (i64.const 63)) (i64.shr_s (local.get $b_hi) (i64.const 63))) ;; if a and b have the same sign
            (then
                (if (i64.ne (i64.shr_s (local.get $a_hi) (i64.const 63)) (i64.shr_s (local.get $sum_hi) (i64.const 63))) ;; and the result has a different sign
                    (then (call $stdlib.runtime-error (i32.const 0)))
                )
            )
        )

        ;; Return the result
        (return (local.get $sum_lo) (local.get $sum_hi))
    )

    (func $stdlib.add-uint (param $a_lo i64) (param $a_hi i64) (param $b_lo i64) (param $b_hi i64) (result i64 i64)
        (call $stdlib.add-int128 (local.get $a_lo) (local.get $a_hi) (local.get $b_lo) (local.get $b_hi))
        (local.set $a_hi) ;; storing the result in place of first operand
        (local.set $a_lo)

        ;; overflow condition: sum (a) < operand (b)
        (if (call $stdlib.lt-uint (local.get $a_lo) (local.get $a_hi) (local.get $b_lo) (local.get $b_hi))
            (then (call $stdlib.runtime-error (i32.const 0)))
        )

        (local.get $a_lo) (local.get $a_hi)
    )

    ;; This function can be used to subtract either signed or unsigned integers
    (func $stdlib.sub-int128 (param $a_lo i64) (param $a_hi i64) (param $b_lo i64) (param $b_hi i64) (result i64 i64)
        (local $borrow i64)
        (local $diff_lo i64)
        (local $diff_hi i64)

        ;; Calculate borrow
        (local.set $borrow (i64.extend_i32_u (i64.lt_u (local.get $a_lo) (local.get $b_lo))))

        ;; Calculate diff_lo
        (local.set $diff_lo (i64.sub (local.get $a_lo) (local.get $b_lo)))

        ;; Calculate diff_hi
        (local.set $diff_hi (i64.sub (i64.sub (local.get $a_hi) (local.get $b_hi)) (local.get $borrow)))

        ;; Return the result
        (return (local.get $diff_lo) (local.get $diff_hi))
    )

    (func $stdlib.sub-int (param $a_lo i64) (param $a_hi i64) (param $b_lo i64) (param $b_hi i64) (result i64 i64)
        (local $diff_hi i64)
        (local $diff_lo i64)

        (local.get $a_lo)
        (local.get $a_hi)
        (local.get $b_lo)
        (local.get $b_hi)
        (call $stdlib.sub-int128)

        (local.set $diff_hi)
        (local.set $diff_lo)

        ;; Check for overflow and underflow
        (if (i64.ne (i64.shr_s (local.get $a_hi) (i64.const 63)) (i64.shr_s (local.get $b_hi) (i64.const 63))) ;; if a and b have different signs
            (then
                (if (i64.ne (i64.shr_s (local.get $a_hi) (i64.const 63)) (i64.shr_s (local.get $diff_hi) (i64.const 63))) ;; and the result has a different sign from a
                    (then (call $stdlib.runtime-error (i32.const 1)))
                )
            )
        )

        ;; Return the result
        (return (local.get $diff_lo) (local.get $diff_hi))
    )

    (func $stdlib.sub-uint (param $a_lo i64) (param $a_hi i64) (param $b_lo i64) (param $b_hi i64) (result i64 i64)
        (local $diff_hi i64)
        (local $diff_lo i64)

        (local.get $a_lo)
        (local.get $a_hi)
        (local.get $b_lo)
        (local.get $b_hi)
        (call $stdlib.sub-int128)

        (local.set $diff_hi)
        (local.set $diff_lo)

        ;; Check for underflow
        (if (i64.gt_u (local.get $diff_hi) (local.get $a_hi))
            (then (call $stdlib.runtime-error (i32.const 1)))
        )

        ;; Return the result
        (return (local.get $diff_lo) (local.get $diff_hi))
    )

    (func $stdlib.mul-int128 (param $a_lo i64) (param $a_hi i64) (param $b_lo i64) (param $b_hi i64) (result i64 i64)
    ;; Adaptation of Hacker's Delight, chapter 8
    ;; u1 <- $a_lo & 0xffffffff; v1 <- $b_lo & 0xffffffff
    ;; u2 <- $a_lo >> 32; v2 <- $b_lo >> 32
    ;; t1 <- v1 * u1
    ;; t2 <- (u2 * v1) + (t1 >> 32)
    ;; t3 <- (u1 * v2) + (t2 & 0xffffffff)
    ;; $res_lo <- (t3 << 32) | (t1 & 0xffffffff)
    ;; $res_hi <- ($a_lo * b_hi) + ($a_hi * b_lo) + (v2 * u2) + (t2 >> 32) + (t3 >> 32)
        (local $u2 i64) (local $v2 i64) (local $t1 i64) (local $t2 i64) (local $t3 i64)

        ;;;;;;;;;;;;;;;;;;;;;;;;;;;; res_lo ;;;;;;;;;;;;;;;;;;;;;;;;;;;;
        (local.tee $t1
            (i64.mul
                ;; $v2 contains u1 temporarily
                (local.tee $v2 (i64.and (local.get $a_lo) (i64.const 0xffffffff)))
                ;; $u2 contains v1 temporarily
                (local.tee $u2 (i64.and (local.get $b_lo) (i64.const 0xffffffff)))
            )
        )
        (i64.shr_u (i64.const 32))              ;; (t1 >> 32)
        (i64.mul                                ;; (u2 * v1)
            (local.get $u2) ;; contains v1 at that point
            (local.tee $u2 (i64.shr_u (local.get $a_lo) (i64.const 32)))
        )
        (local.tee $t2 (i64.add))               ;; (u2 * v1) + (t1 >> 32)
        (i64.and (i64.const 0xffffffff))        ;; (t2 & 0xffffffff)
        (i64.mul                                ;; (u1 * v2)
            (local.get $v2) ;; contains u1 at that point
            (local.tee $v2 (i64.shr_u (local.get $b_lo) (i64.const 32)))
        )
        (local.tee $t3 (i64.add))               ;; (u1 * v2) + (t2 & 0xffffffff)
        (i64.shl (i64.const 32))                ;; (t3 << 32)
        (i64.and (local.get $t1) (i64.const 0xffffffff))
        i64.or                                  ;; (t2 << 32) | (t1 & 0xffffffff)

        ;;;;;;;;;;;;;;;;;;;;;;;;;;;; res_hi ;;;;;;;;;;;;;;;;;;;;;;;;;;;;
        (i64.mul (local.get $a_lo) (local.get $b_hi))
        (i64.add (i64.mul (local.get $a_hi) (local.get $b_lo)))
        (i64.add (i64.mul (local.get $v2) (local.get $u2)))
        (i64.add (i64.shr_u (local.get $t2) (i64.const 32)))
        (i64.add (i64.shr_u (local.get $t3) (i64.const 32)))
    )

    (func $stdlib.mul-uint (param $a_lo i64) (param $a_hi i64) (param $b_lo i64) (param $b_hi i64) (result i64 i64)
        (local $tmp i32)

        (local.set $tmp  ;; tmp contains the sum of number of leading zeros of arguments
            (i32.add
                (call $clz-int128 (local.get $a_lo) (local.get $a_hi))
                (call $clz-int128 (local.get $b_lo) (local.get $b_hi))
            )
        )

        (if (i32.ge_u (local.get $tmp) (i32.const 128))
            (then
                ;; product cannot overflow if the sum of leading zeros is >= 128
                (return (call $stdlib.mul-int128 (local.get $a_lo) (local.get $a_hi) (local.get $b_lo) (local.get $b_hi)))
            )
        )

        (if (i32.le_u (local.get $tmp) (i32.const 126))
            (then
                ;; product will overflow if the sum of leading zeros is <= 126
                (call $stdlib.runtime-error (i32.const 0))
            )
        )

        ;; Other case might overflow. We compute (a * b/2) and check if result > 2**127
        ;;    -> if yes, overflow
        ;;    -> if not, we double the product, and add a one more time if b was odd

        ;; tmp is 1 if b was odd else 0
        (local.set $tmp (i32.wrap_i64 (i64.and (local.get $b_lo) (i64.const 1))))

        ;; b / 2
        (i64.or
            (i64.shl (local.get $b_hi) (i64.const 63))
            (i64.shr_u (local.get $b_lo) (i64.const 1))
        )
        (i64.shr_u (local.get $b_hi) (i64.const 1))

        ;; a * b/2
        (call $stdlib.mul-int128 (local.get $a_lo) (local.get $a_hi))
        ;; b contains the result from now on
        (local.set $b_hi)
        (local.set $b_lo)

        ;; if result/2 > 2**127 overflow
        (if (i64.lt_s (local.get $b_hi) (i64.const 0))
            (then (call $stdlib.runtime-error (i32.const 0)))
        )

        ;; res *= 2, meaning res <<= 1
        (local.set $b_hi
            (i64.or
                (i64.shl (local.get $b_hi) (i64.const 1))
                (i64.shr_u (local.get $b_lo) (i64.const 63))
            )
        )
        (local.set $b_lo (i64.shl (local.get $b_lo) (i64.const 1)))

        ;; if b is odd ($tmp), we add a
        (if (local.get $tmp)
            (then
                (call $stdlib.add-uint (local.get $b_lo) (local.get $b_hi) (local.get $a_lo) (local.get $a_hi))
                (local.set $b_hi)
                (local.set $b_lo)
            )
        )
        (local.get $b_lo) (local.get $b_hi)
    )

    (func $stdlib.mul-int (param $a_lo i64) (param $a_hi i64) (param $b_lo i64) (param $b_hi i64) (result i64 i64)
        (local $sign i32)

        ;; this is a shortcut for a multiplication by 1.
        ;; also, it prevents us from dealing with the infamous abs(i128::MIN), and
        ;; the only operation that would work on that number would be (i128::MIN * 1)
        (if (i64.eqz (i64.or (local.get $a_hi) (i64.xor (local.get $a_lo) (i64.const 1))))
            (then (return (local.get $b_lo) (local.get $b_hi)))
        )
        (if (i64.eqz (i64.or (local.get $b_hi) (i64.xor (local.get $b_lo) (i64.const 1))))
            (then (return (local.get $a_lo) (local.get $a_hi)))
        )

        ;; take the absolute value of the operands, and compute the expected sign in 3 steps:
        ;; 1. Absolute value of a
        ;; NOTE: the absolute value algorithm was generated from
        ;;       `fn abs(a: i128) -> i128 { a.abs() }`
        (select
            (i64.sub (i64.const 0) (local.get $a_lo))
            (local.get $a_lo)
            (local.tee $sign (i64.lt_s (local.get $a_hi) (i64.const 0))) ;; sign is the sign bit of a
        )
        (select
            (i64.sub (i64.const 0) (i64.add (local.get $a_hi) (i64.extend_i32_u (i64.ne (local.get $a_lo) (i64.const 0)))))
            (local.get $a_hi)
            (local.get $sign)
        )
        ;; 2. Absolute value of b
        (select
            (i64.sub (i64.const 0) (local.get $b_lo))
            (local.get $b_lo)
            (local.tee $sign (i64.lt_s (local.get $b_hi) (i64.const 0))) ;; sign is sign bit of b now
        )
        (select
            (i64.sub (i64.const 0) (i64.add (local.get $b_hi) (i64.extend_i32_u (i64.ne (local.get $b_lo) (i64.const 0)))))
            (local.get $b_hi)
            (local.get $sign)
        )
        ;; 3. Compute expected sign
        (local.set $sign
            (i32.xor
                (i64.lt_s (local.get $a_hi) (i64.const 0)) ;; sign of a
                (local.get $sign) ;; sign is sign of b
            )
        )

        (call $stdlib.mul-uint)
        (local.set $a_hi)
        (local.set $a_lo)

        ;; Sign bit should be 0, otherwise there is an overflow
        (if (i64.lt_s (local.get $a_hi) (i64.const 0))
            (then (call $stdlib.runtime-error (i32.const 0)))
        )

        ;; Return the result and adapt with sign bit
        (select
            (i64.sub (i64.const 0) (local.get $a_lo))
            (local.get $a_lo)
            (local.get $sign)
        )
        (select
            (i64.sub (i64.const 0) (i64.add (local.get $a_hi) (i64.extend_i32_u (i64.ne (local.get $a_lo) (i64.const 0)))))
            (local.get $a_hi)
            (local.get $sign)
        )
    )

    (func $stdlib.div-int128 (param $dividend_lo i64) (param $dividend_hi i64) (param $divisor_lo i64) (param $divisor_hi i64) (result i64 i64 i64 i64)
        (local $quotient_hi i64)
        (local $quotient_lo i64)
        (local $remainder_hi i64)
        (local $remainder_lo i64)
        (local $current_bit i64)

        ;; Check for division by 0
        (if (i64.eqz (i64.or (local.get $divisor_hi) (local.get $divisor_lo)))
            (then (call $stdlib.runtime-error (i32.const 2)))
        )

        ;; Long division algorithm
        ;; Initialize the quotient and remainder to 0
        (local.set $quotient_hi (i64.const 0))
        (local.set $quotient_lo (i64.const 0))
        (local.set $remainder_hi (i64.const 0))
        (local.set $remainder_lo (i64.const 0))
        ;; (local.set $remainder_hi (local.get $dividend_hi))
        ;; (local.set $remainder_lo (local.get $dividend_lo))

        ;; Use current_bit to loop over the bits of the dividend
        (local.set $current_bit (i64.const 127))

        (loop $div_loop
            ;; Shift the remainder left by one bit,
            ;; filling the least significant bit with the next bit of the dividend
            (local.set $remainder_hi (i64.or
                (i64.shl (local.get $remainder_hi) (i64.const 1))
                (i64.shr_u (local.get $remainder_lo) (i64.const 63))))
            (local.set $remainder_lo (i64.or
                (i64.shl (local.get $remainder_lo) (i64.const 1))
                (i64.shr_u (local.get $dividend_hi) (i64.const 63))))

            ;; Shift the dividend left by one bit
            (local.set $dividend_hi (i64.or
                (i64.shl (local.get $dividend_hi) (i64.const 1))
                (i64.shr_u (local.get $dividend_lo) (i64.const 63))))
            (local.set $dividend_lo (i64.shl (local.get $dividend_lo) (i64.const 1)))

            ;; If the remainder is greater than or equal to the divisor,
            (if (i32.or (i64.gt_u (local.get $remainder_hi) (local.get $divisor_hi))
                        (i32.and (i64.eq (local.get $remainder_hi) (local.get $divisor_hi))
                                 (i64.ge_u (local.get $remainder_lo) (local.get $divisor_lo))))
                (then
                    ;; Subtract the divisor from the remainder
                    (call $stdlib.sub-int128 (local.get $remainder_lo) (local.get $remainder_hi) (local.get $divisor_lo) (local.get $divisor_hi))
                    (local.set $remainder_hi)
                    (local.set $remainder_lo)

                    ;; and set the current bit of the quotient to 1
                    (if (i64.lt_u (local.get $current_bit) (i64.const 64))
                        (then
                            (local.set $quotient_lo (i64.or (local.get $quotient_lo)
                                (i64.shl (i64.const 1) (local.get $current_bit))))
                        )
                        (else
                            (local.set $quotient_hi (i64.or (local.get $quotient_hi)
                                (i64.shl (i64.const 1) (i64.sub (local.get $current_bit) (i64.const 64)))))
                        )
                    )
                )
            )

            ;; Decrement the current bit and loop until all bits have been processed
            (local.set $current_bit (i64.sub (local.get $current_bit) (i64.const 1)))
            (br_if $div_loop (i64.ge_s (local.get $current_bit) (i64.const 0)))
        )

        ;; Return the quotient and the remainder
        (return (local.get $quotient_lo) (local.get $quotient_hi) (local.get $remainder_lo) (local.get $remainder_hi))
    )

    (func $stdlib.div-uint (param $dividend_lo i64) (param $dividend_hi i64) (param $divisor_lo i64) (param $divisor_hi i64) (result i64 i64)
        (local $quotient_hi i64)
        (local $quotient_lo i64)
        (local $remainder_hi i64)
        (local $remainder_lo i64)

        (call $stdlib.div-int128 (local.get $dividend_lo) (local.get $dividend_hi) (local.get $divisor_lo) (local.get $divisor_hi))
        (local.set $remainder_hi)
        (local.set $remainder_lo)
        (local.set $quotient_hi)
        (local.set $quotient_lo)

        (return (local.get $quotient_lo) (local.get $quotient_hi))
    )

    (func $stdlib.div-int (param $dividend_lo i64) (param $dividend_hi i64) (param $divisor_lo i64) (param $divisor_hi i64) (result i64 i64)
        (local $quotient_hi i64)
        (local $quotient_lo i64)
        (local $remainder_hi i64)
        (local $remainder_lo i64)
        (local $sign_dividend i64)
        (local $sign_divisor i64)
        (local $expected_sign i64)

        ;; overflow if i128::MIN / -1
        (if
            (i32.and
                (i32.and (i64.eqz (local.get $dividend_lo)) (i64.eq (local.get $dividend_hi) (i64.const 0x8000000000000000)))
                (i64.eq (i64.and (local.get $divisor_lo) (local.get $divisor_hi)) (i64.const -1))
            )
            (then (call $stdlib.runtime-error (i32.const 0)))
        )

        ;; Compute the expected sign of the result
        (local.set $sign_dividend (i64.shr_s (local.get $dividend_hi) (i64.const 63)))
        (local.set $sign_divisor (i64.shr_s (local.get $divisor_hi) (i64.const 63)))
        (local.set $expected_sign (i64.xor (local.get $sign_dividend) (local.get $sign_divisor)))

        ;; Perform the division using the absolute values of the operands
        (if (i32.wrap_i64 (local.get $sign_dividend))
            (then
                (call $stdlib.sub-int128 (i64.const 0) (i64.const 0) (local.get $dividend_lo) (local.get $dividend_hi))
                (local.set $dividend_hi)
                (local.set $dividend_lo)
            )
        )
        (if (i32.wrap_i64 (local.get $sign_divisor))
            (then
                (call $stdlib.sub-int128 (i64.const 0) (i64.const 0) (local.get $divisor_lo) (local.get $divisor_hi))
                (local.set $divisor_hi)
                (local.set $divisor_lo)
            )
        )

        (call $stdlib.div-int128 (local.get $dividend_lo) (local.get $dividend_hi) (local.get $divisor_lo) (local.get $divisor_hi))
        (local.set $remainder_hi)
        (local.set $remainder_lo)
        (local.set $quotient_hi)
        (local.set $quotient_lo)

        ;; If the result should be negative, negate it
        (if (i32.wrap_i64 (local.get $expected_sign))
            (then
                (call $stdlib.sub-int128 (i64.const 0) (i64.const 0) (local.get $quotient_lo) (local.get $quotient_hi))
                (local.set $quotient_hi)
                (local.set $quotient_lo)
            )
        )

        (return (local.get $quotient_lo) (local.get $quotient_hi))
    )

    (func $stdlib.mod-uint (param $dividend_lo i64) (param $dividend_hi i64) (param $divisor_lo i64) (param $divisor_hi i64) (result i64 i64)
        (local $quotient_hi i64)
        (local $quotient_lo i64)
        (local $remainder_hi i64)
        (local $remainder_lo i64)

        (call $stdlib.div-int128 (local.get $dividend_lo) (local.get $dividend_hi) (local.get $divisor_lo) (local.get $divisor_hi))
        (local.set $remainder_hi)
        (local.set $remainder_lo)
        (local.set $quotient_hi)
        (local.set $quotient_lo)

        (return (local.get $remainder_lo) (local.get $remainder_hi))
    )

    (func $stdlib.mod-int (param $dividend_lo i64) (param $dividend_hi i64) (param $divisor_lo i64) (param $divisor_hi i64) (result i64 i64)
        (local $quotient_hi i64)
        (local $quotient_lo i64)
        (local $remainder_hi i64)
        (local $remainder_lo i64)
        (local $sign_dividend i64)
        (local $sign_divisor i64)
        (local $expected_sign i64)

        ;; Compute the expected sign of the result
        (local.set $sign_dividend (i64.shr_s (local.get $dividend_hi) (i64.const 63)))
        (local.set $sign_divisor (i64.shr_s (local.get $divisor_hi) (i64.const 63)))
        (local.set $expected_sign (i64.xor (local.get $sign_dividend) (local.get $sign_divisor)))

        ;; Perform the division using the absolute values of the operands
        (if (i32.wrap_i64 (local.get $sign_dividend))
            (then
                (call $stdlib.sub-int128 (i64.const 0) (i64.const 0) (local.get $dividend_lo) (local.get $dividend_hi))
                (local.set $dividend_hi)
                (local.set $dividend_lo)
            )
        )
        (if (i32.wrap_i64 (local.get $sign_divisor))
            (then
                (call $stdlib.sub-int128 (i64.const 0) (i64.const 0) (local.get $divisor_lo) (local.get $divisor_hi))
                (local.set $divisor_hi)
                (local.set $divisor_lo)
            )
        )

        (call $stdlib.div-int128 (local.get $dividend_lo) (local.get $dividend_hi) (local.get $divisor_lo) (local.get $divisor_hi))
        (local.set $remainder_hi)
        (local.set $remainder_lo)
        (local.set $quotient_hi)
        (local.set $quotient_lo)

        ;; If the result should be negative, negate it
        (if (i32.wrap_i64 (local.get $sign_dividend))
            (then
                (call $stdlib.sub-int128 (i64.const 0) (i64.const 0) (local.get $remainder_lo) (local.get $remainder_hi))
                (local.set $remainder_hi)
                (local.set $remainder_lo)
            )
        )

        (return (local.get $remainder_lo) (local.get $remainder_hi))
    )

    (func $stdlib.lt-uint (param $a_lo i64) (param $a_hi i64) (param $b_lo i64) (param $b_hi i64) (result i32)
        (select
            (i64.lt_u (local.get $a_lo) (local.get $b_lo))
            (i64.lt_u (local.get $a_hi) (local.get $b_hi))
            (i64.eq (local.get $a_hi) (local.get $b_hi))
        )
    )

    (func $stdlib.gt-uint (param $a_lo i64) (param $a_hi i64) (param $b_lo i64) (param $b_hi i64) (result i32)
        (select
            (i64.gt_u (local.get $a_lo) (local.get $b_lo))
            (i64.gt_u (local.get $a_hi) (local.get $b_hi))
            (i64.eq (local.get $a_hi) (local.get $b_hi))
        )
    )

    (func $stdlib.le-uint (param $a_lo i64) (param $a_hi i64) (param $b_lo i64) (param $b_hi i64) (result i32)
        (select
            (i64.le_u (local.get $a_lo) (local.get $b_lo))
            (i64.le_u (local.get $a_hi) (local.get $b_hi))
            (i64.eq (local.get $a_hi) (local.get $b_hi))
        )
    )

    (func $stdlib.ge-uint (param $a_lo i64) (param $a_hi i64) (param $b_lo i64) (param $b_hi i64) (result i32)
        (select
            (i64.ge_u (local.get $a_lo) (local.get $b_lo))
            (i64.ge_u (local.get $a_hi) (local.get $b_hi))
            (i64.eq (local.get $a_hi) (local.get $b_hi))
        )
    )

    (func $stdlib.lt-int (param $a_lo i64) (param $a_hi i64) (param $b_lo i64) (param $b_hi i64) (result i32)
        (select
            (i64.lt_u (local.get $a_lo) (local.get $b_lo))
            (i64.lt_s (local.get $a_hi) (local.get $b_hi))
            (i64.eq (local.get $a_hi) (local.get $b_hi))
        )
    )

    (func $stdlib.gt-int (param $a_lo i64) (param $a_hi i64) (param $b_lo i64) (param $b_hi i64) (result i32)
        (select
            (i64.gt_u (local.get $a_lo) (local.get $b_lo))
            (i64.gt_s (local.get $a_hi) (local.get $b_hi))
            (i64.eq (local.get $a_hi) (local.get $b_hi))
        )
    )

    (func $stdlib.le-int (param $a_lo i64) (param $a_hi i64) (param $b_lo i64) (param $b_hi i64) (result i32)
        (select
            (i64.le_u (local.get $a_lo) (local.get $b_lo))
            (i64.le_s (local.get $a_hi) (local.get $b_hi))
            (i64.eq (local.get $a_hi) (local.get $b_hi))
        )
    )

    (func $stdlib.ge-int (param $a_lo i64) (param $a_hi i64) (param $b_lo i64) (param $b_hi i64) (result i32)
        (select
            (i64.ge_u (local.get $a_lo) (local.get $b_lo))
            (i64.ge_s (local.get $a_hi) (local.get $b_hi))
            (i64.eq (local.get $a_hi) (local.get $b_hi))
        )
    )

    (func $stdlib.lt-buff (param $offset_a i32) (param $length_a i32) (param $offset_b i32) (param $length_b i32) (result i32)
        (local $i i32) (local $sub i32)
        ;; pseudo-code:
        ;; let i = min(length_a, length_b)
        ;; while i != 0 {
        ;;   if ((sub = a[offset_a] - b[offset_b]) == 0) {
        ;;     offset_a += 1; offset_b += 1; i -= 1;
        ;;   } else { break }
        ;; }
        ;; return (sub != 0) ? (sub < 0) : (length_a < length_b)
        (block $done
            ;; we can skip the comparison loop if $i (min length) is 0
            (br_if $done
                (i32.eqz
                    (local.tee $i
                        ;; no i32.min in Wasm...
                        (select
                            (local.get $length_a)
                            (local.get $length_b)
                            (i32.lt_u (local.get $length_a) (local.get $length_b))
                        )
                    )
                )
            )
            (loop $loop
                (if
                    (i32.eqz
                        ;; $sub will be 0 if both are equal, otherwise its sign indicates which is smaller
                        (local.tee $sub
                            (i32.sub (i32.load8_u (local.get $offset_a)) (i32.load8_u (local.get $offset_b)))
                        )
                    )
                    (then
                        (local.set $offset_a (i32.add (local.get $offset_a) (i32.const 1)))
                        (local.set $offset_b (i32.add (local.get $offset_b) (i32.const 1)))
                        (br_if $loop (local.tee $i (i32.sub (local.get $i) (i32.const 1))))
                    )
                )
            )
        )
        ;; if sub is 0, it means that for the min length of both buffers, both are equals
        ;;   - in this case, the result is the comparison of the lengths
        ;;   - otherwise $sub < 0
        (select
            (i32.lt_s (local.get $sub) (i32.const 0))
            (i32.lt_u (local.get $length_a) (local.get $length_b))
            (local.get $sub)
        )
    )

    (func $stdlib.gt-buff (param $offset_a i32) (param $length_a i32) (param $offset_b i32) (param $length_b i32) (result i32)
        (local $i i32) (local $sub i32)
        ;; same algorithm as $stdlib.lt-buff
        (block $done
            (br_if $done
                (i32.eqz
                    (local.tee $i
                        (select
                            (local.get $length_a)
                            (local.get $length_b)
                            (i32.lt_u (local.get $length_a) (local.get $length_b))
                        )
                    )
                )
            )
            (loop $loop
                (if
                    (i32.eqz
                        (local.tee $sub
                            (i32.sub (i32.load8_u (local.get $offset_a)) (i32.load8_u (local.get $offset_b)))
                        )
                    )
                    (then
                        (local.set $offset_a (i32.add (local.get $offset_a) (i32.const 1)))
                        (local.set $offset_b (i32.add (local.get $offset_b) (i32.const 1)))
                        (br_if $loop (local.tee $i (i32.sub (local.get $i) (i32.const 1))))
                    )
                )
            )
        )
        (select
            (i32.gt_s (local.get $sub) (i32.const 0))
            (i32.gt_u (local.get $length_a) (local.get $length_b))
            (local.get $sub)
        )
    )

    (func $stdlib.le-buff (param $offset_a i32) (param $length_a i32) (param $offset_b i32) (param $length_b i32) (result i32)
        (local $i i32) (local $sub i32)
        ;; same algorithm as $stdlib.lt-buff
        (block $done
            (br_if $done
                (i32.eqz
                    (local.tee $i
                        (select
                            (local.get $length_a)
                            (local.get $length_b)
                            (i32.lt_u (local.get $length_a) (local.get $length_b))
                        )
                    )
                )
            )
            (loop $loop
                (if
                    (i32.eqz
                        (local.tee $sub
                            (i32.sub (i32.load8_u (local.get $offset_a)) (i32.load8_u (local.get $offset_b)))
                        )
                    )
                    (then
                        (local.set $offset_a (i32.add (local.get $offset_a) (i32.const 1)))
                        (local.set $offset_b (i32.add (local.get $offset_b) (i32.const 1)))
                        (br_if $loop (local.tee $i (i32.sub (local.get $i) (i32.const 1))))
                    )
                )
            )
        )
        (select
            (i32.le_s (local.get $sub) (i32.const 0))
            (i32.le_u (local.get $length_a) (local.get $length_b))
            (local.get $sub)
        )
    )

    (func $stdlib.ge-buff (param $offset_a i32) (param $length_a i32) (param $offset_b i32) (param $length_b i32) (result i32)
        (local $i i32) (local $sub i32)
        ;; same algorithm as $stdlib.lt-buff
        (block $done
            (br_if $done
                (i32.eqz
                    (local.tee $i
                        (select
                            (local.get $length_a)
                            (local.get $length_b)
                            (i32.lt_u (local.get $length_a) (local.get $length_b))
                        )
                    )
                )
            )
            (loop $loop
                (if
                    (i32.eqz
                        (local.tee $sub
                            (i32.sub (i32.load8_u (local.get $offset_a)) (i32.load8_u (local.get $offset_b)))
                        )
                    )
                    (then
                        (local.set $offset_a (i32.add (local.get $offset_a) (i32.const 1)))
                        (local.set $offset_b (i32.add (local.get $offset_b) (i32.const 1)))
                        (br_if $loop (local.tee $i (i32.sub (local.get $i) (i32.const 1))))
                    )
                )
            )
        )
        (select
            (i32.ge_s (local.get $sub) (i32.const 0))
            (i32.ge_u (local.get $length_a) (local.get $length_b))
            (local.get $sub)
        )
    )

    (func $log2 (param $lo i64) (param $hi i64) (result i64)
        (select
            (i64.xor (i64.clz (local.get $lo)) (i64.const 63))
            (i64.xor (i64.clz (local.get $hi)) (i64.const 127))
            (i64.eqz (local.get $hi))
        )
    )

    (func $stdlib.log2-uint (param $lo i64) (param $hi i64) (result i64 i64)
        (if (i64.eqz (i64.or (local.get $hi) (local.get $lo)))
            (then (call $stdlib.runtime-error (i32.const 3)))
        )
        (call $log2 (local.get $lo) (local.get $hi))
        (i64.const 0)
    )

    (func $stdlib.log2-int (param $lo i64) (param $hi i64) (result i64 i64)
        (if (call $stdlib.le-int (local.get $lo) (local.get $hi) (i64.const 0) (i64.const 0))
            (then (call $stdlib.runtime-error (i32.const 3)))
        )
        (call $log2 (local.get $lo) (local.get $hi))
        (i64.const 0)
    )

    (func $stdlib.sqrti-uint (param $lo i64) (param $hi i64) (result i64 i64)
        ;; https://en.wikipedia.org/wiki/Methods_of_computing_square_roots#Binary_numeral_system_(base_2)
        (local $d_lo i64) (local $d_hi i64)
        (local $c_lo i64) (local $c_hi i64)
        (local $tmp_lo i64) (local $tmp_hi i64)

        (if (i64.eqz (i64.or (local.get $lo) (local.get $hi)))
            (then (return (i64.const 0) (i64.const 0)))
        )

        (local.set $c_lo (i64.const 0))
        (local.set $c_hi (i64.const 0))

        ;; computing d
        (if (i64.eqz (local.get $hi))
            (then
                ;; since we know $d_hi will be 0, we can use it as tmp value during computation
                (local.set $d_hi (i64.const 0x4000000000000000))
                (loop $loop_lo
                    (local.set $d_hi
                        (i64.shr_u
                            (local.tee $d_lo (local.get $d_hi))
                            (i64.const 2)
                        )
                    )
                    (br_if $loop_lo (i64.lt_u (local.get $lo) (local.get $d_lo)))
                )
                (local.set $d_hi (i64.const 0))
            )
            (else
                ;; since we know $d_lo will be 0, we can use it as tmp value during computation
                (local.set $d_lo (i64.const 0x4000000000000000))
                (loop $loop_hi
                    (local.set $d_lo
                        (i64.shr_u
                            (local.tee $d_hi (local.get $d_lo))
                            (i64.const 2)
                        )
                    )
                    (br_if $loop_hi (i64.lt_u (local.get $hi) (local.get $d_hi)))
                )
                (local.set $d_lo (i64.const 0))
            )
        )

        (loop $loop_res
            ;; tmp = c + d
            (call $stdlib.add-int128 (local.get $c_lo) (local.get $c_hi) (local.get $d_lo) (local.get $d_hi))
            (local.set $tmp_hi)
            (local.set $tmp_lo)

            ;; c = c >> 1
            (local.set $c_lo
                (i64.or
                    (i64.shl (local.get $c_hi) (i64.const 63))
                    (i64.shr_u (local.get $c_lo) (i64.const 1))
                )
            )
            (local.set $c_hi (i64.shr_u (local.get $c_hi) (i64.const 1)))

            ;; if n >= tmp
            (if (call $stdlib.ge-uint (local.get $lo) (local.get $hi) (local.get $tmp_lo) (local.get $tmp_hi))
                (then
                    ;; n -= tmp
                    (call $stdlib.sub-int128 (local.get $lo) (local.get $hi) (local.get $tmp_lo) (local.get $tmp_hi))
                    (local.set $hi)
                    (local.set $lo)

                    ;; c += d
                    (call $stdlib.add-int128 (local.get $c_lo) (local.get $c_hi) (local.get $d_lo) (local.get $d_hi))
                    (local.set $c_hi)
                    (local.set $c_lo)
                )
            )

            ;; d = d >> 2
            (local.set $d_lo
                (i64.or
                    (i64.shl (local.get $d_hi) (i64.const 62))
                    (i64.shr_u (local.get $d_lo) (i64.const 2))
                )
            )
            (local.set $d_hi (i64.shr_u (local.get $d_hi) (i64.const 2)))

            ;; branch if (d != 0)
            (br_if $loop_res
                (i64.ne (i64.or (local.get $d_lo) (local.get $d_hi)) (i64.const 0))
            )
        )

        (local.get $c_lo) (local.get $c_hi)
    )

    (func $stdlib.sqrti-int (param $lo i64) (param $hi i64) (result i64 i64)
        (if (i64.lt_s (local.get $hi) (i64.const 0))
            (then (call $stdlib.runtime-error (i32.const 4)))
        )
        (call $stdlib.sqrti-uint (local.get $lo) (local.get $hi))
    )

    (func $stdlib.bit-and (param $a_lo i64) (param $a_hi i64) (param $b_lo i64) (param $b_hi i64) (result i64 i64)
        (i64.and (local.get $a_lo) (local.get $b_lo))
        (i64.and (local.get $a_hi) (local.get $b_hi))
    )

    (func $stdlib.bit-not (param $a_lo i64) (param $a_hi i64) (result i64 i64)
          ;; wasm does not have bitwise negation, but xoring with -1 is equivalent
          (i64.xor (local.get $a_lo) (i64.const -1))
          (i64.xor (local.get $a_hi) (i64.const -1))
    )

    (func $stdlib.bit-or (param $a_lo i64) (param $a_hi i64) (param $b_lo i64) (param $b_hi i64) (result i64 i64)
          (i64.or (local.get $a_lo) (local.get $b_lo))
          (i64.or (local.get $a_hi) (local.get $b_hi))
    )

    (func $stdlib.bit-xor (param $a_lo i64) (param $a_hi i64) (param $b_lo i64) (param $b_hi i64) (result i64 i64)
          (i64.xor (local.get $a_lo) (local.get $b_lo))
          (i64.xor (local.get $a_hi) (local.get $b_hi))
    )

    (func $stdlib.bit-shift-left (param $a_lo i64) (param $a_hi i64) (param $b_lo i64) (param $b_hi i64) (result i64 i64)
          ;; only b_lo is useful here since we will take the reminder by 128
          ;; n % 128 == n & 127 == n & 0x7f
          (local.set $b_lo (i64.and (local.get $b_lo) (i64.const 0x7f)))
          ;; Two cases when we shift:
          ;; (1) we shift by a 0 <= shift < 64: we have to split the lower bits into the carried bits and the rest, then we shift
          ;;     the rest, we shift the higher part and we add the carry to the higher part.
          ;; (2) we shift by a 64 <= shift < 128: lower bits are automatically 0, and higher bits are the lower bits shifted by (shift - 64).
          (if (result i64 i64) (i64.lt_u (local.get $b_lo) (i64.const 64))
              (then ;; (1)
               (local.set $b_hi ;; using $b_hi for storing overflow bits
                          (select ;; that's a hack to workaround wasm shift by 64 has no effect
                           (i64.const 0)
                           (i64.shr_u (local.get $a_lo) (i64.sub (i64.const 64) (local.get $b_lo)))
                           (i64.eqz (local.get $b_lo))))
               (i64.shl (local.get $a_lo) (local.get $b_lo)) ;; lower_bits <<= shift
               (i64.or (i64.shl (local.get $a_hi) (local.get $b_lo))
                       (local.get $b_hi))) ;; higher_bits = (higher_bits << shift) | carry
              (else ;; (2)
               (i64.const 0)
               (i64.shl (local.get $a_lo) (i64.sub (local.get $b_lo) (i64.const 64))))))

    (func $stdlib.bit-shift-right-uint (param $a_lo i64) (param $a_hi i64) (param $b_lo i64) (param $b_hi i64) (result i64 i64)
		  ;; This is just an inverted version of shift-left, see above
          (local.set $b_lo (i64.and (local.get $b_lo) (i64.const 0x7f)))
          (if (result i64 i64) (i64.lt_u (local.get $b_lo) (i64.const 64))
              (then
               (local.set $b_hi
                          (select
                           (i64.const 0)
                           (i64.shl (local.get $a_hi)
                                    (i64.sub (i64.const 64)
                                             (local.get $b_lo)))
                           (i64.eqz (local.get $b_lo))))
               (i64.or (i64.shr_u (local.get $a_lo)
                                  (local.get $b_lo))
                       (local.get $b_hi))
               (i64.shr_u (local.get $a_hi)
                          (local.get $b_lo)))
              (else
               (i64.shr_u (local.get $a_hi)
                          (i64.sub (local.get $b_lo)
                                   (i64.const 64)))
               (i64.const 0))))

    (func $stdlib.bit-shift-right-int (param $a_lo i64) (param $a_hi i64) (param $b_lo i64) (param $b_hi i64) (result i64 i64)
		  ;; This is just shift-right but taking into account the sign (using shr_s when shifting the high bits)
          (local.set $b_lo (i64.and (local.get $b_lo) (i64.const 0x7f)))
          (if (result i64 i64) (i64.lt_u (local.get $b_lo) (i64.const 64))
              (then
               (local.set $b_hi
                          (select
                           (i64.const 0)
                           (i64.shl (local.get $a_hi) (i64.sub (i64.const 64) (local.get $b_lo)))
                           (i64.eqz (local.get $b_lo))))
               (i64.or (i64.shr_u (local.get $a_lo) (local.get $b_lo))
                       (local.get $b_hi))
               (i64.shr_s (local.get $a_hi) (local.get $b_lo)))
              (else
               (i64.shr_s (local.get $a_hi) (i64.sub (local.get $b_lo) (i64.const 64)))
               ;; this keeps the sign from changing
               (i64.shr_s (local.get $a_hi) (i64.const 63)))))

    (func $clz-int128 (param $a_lo i64) (param $a_hi i64) (result i32)
        (i32.wrap_i64
            (select
                (i64.add (i64.const 64) (i64.clz (local.get $a_lo)))
                (i64.clz (local.get $a_hi))
                (i64.eqz (local.get $a_hi))
            )
        )
    )

    (func $pow-inner (param $a_lo i64) (param $a_hi i64) (param $b i32) (result i64 i64)
        ;; examples of this algo:
        ;; 3 ^ 5 => (3 ^ 4) * 3 => (9 ^ 2) * 3 => (81 ^ 1) * 3 => 243
        ;; 4 ^ 6 => (16 ^ 3) * 1 => (16 ^ 2) * 16 => (256 ^ 1) * 16 => 4096
        (local $carry_lo i64) (local $carry_hi i64)
        (local.set $carry_lo (i64.const 1))
        (local.set $carry_hi (i64.const 0))
        (loop
            (if (i32.eqz (i32.and (local.get $b) (i32.const 1)))
                (then
                    (local.set $b (i32.shr_u (local.get $b) (i32.const 1)))
                    (call $stdlib.mul-uint (local.get $a_lo) (local.get $a_hi) (local.get $a_lo) (local.get $a_hi))
                    (local.set $a_hi)
                    (local.set $a_lo)
                )
                (else
                    (local.set $b (i32.xor (local.get $b) (i32.const 1)))
                    (call $stdlib.mul-uint (local.get $a_lo) (local.get $a_hi) (local.get $carry_lo) (local.get $carry_hi))
                    (local.set $carry_hi)
                    (local.set $carry_lo)
                )
            )
            (br_if 0 (i32.gt_u (local.get $b) (i32.const 1)))
        )
        (call $stdlib.mul-uint (local.get $a_lo) (local.get $a_hi) (local.get $carry_lo) (local.get $carry_hi))
    )

    (func $stdlib.pow-uint (param $a_lo i64) (param $a_hi i64) (param $b_lo i64) (param $b_hi i64) (result i64 i64)
        ;; (a == 0 && b == 0 => 1) & (b == 0 => 1) ==> (b == 0 => 1)
        (if (i64.eqz (i64.or (local.get $b_lo) (local.get $b_hi)))
            (then (return (i64.const 1) (i64.const 0)))
        )
        ;; (a == 0 => 0) & (a == 1 => 1) ==> (a < 2 => a)
        ;; also, (b == 1 => a)
        (if (i32.or
                (i32.and (i64.lt_u (local.get $a_lo) (i64.const 2)) (i64.eqz (local.get $a_hi)))
                (i64.eqz (i64.or (i64.xor (local.get $b_lo) (i64.const 1)) (local.get $b_hi)))
            )
            (then (return (local.get $a_lo) (local.get $a_hi)))
        )
        ;; if b > 127 -> runtime error: overflow (since the biggest b that doesn't
        ;; overflow is in 2^127)
        (if (i32.or
                (i64.gt_u (local.get $b_lo) (i64.const 127))
                (i64.ne (local.get $b_hi) (i64.const 0))
            )
            ;; In the interpreter, overflows for the power operation throw a specific error,
            ;; not a general ArithmeticOverflow error.
            ;; Therefore, the runtime error code should be 8,
            ;; which maps to the specific error.
            (then (call $stdlib.runtime-error (i32.const 8)))
        )

        ;; shortcut if a == 2
        (if (i64.eqz (i64.or (i64.xor (local.get $a_lo) (i64.const 2)) (local.get $a_hi)))
            (then
                (return
                    (select
                        (i64.shl (i64.const 1) (local.get $b_lo))
                        (i64.const 0)
                        (i64.lt_u (local.get $b_lo) (i64.const 64))
                    )
                    (select
                        (i64.const 0)
                        (i64.shl (i64.const 1) (i64.sub (local.get $b_lo) (i64.const 64)))
                        (i64.lt_u (local.get $b_lo) (i64.const 64))
                    )
                )
            )
        )

        (call $pow-inner (local.get $a_lo) (local.get $a_hi) (i32.wrap_i64 (local.get $b_lo)))
    )

    (func $stdlib.pow-int (param $a_lo i64) (param $a_hi i64) (param $b_lo i64) (param $b_hi i64) (result i64 i64)
        (local $negative i32)
        ;; (a == 0 && b == 0 => 1) & (b == 0 => 1) ==> (b == 0 => 1)
        (if (i64.eqz (i64.or (local.get $b_lo) (local.get $b_hi)))
            (then (return (i64.const 1) (i64.const 0)))
        )

        ;; (a == 0 => 0) & (a == 1 => 1) ==> (a < 2 => a)
        ;; also, (b == 1 => a)
        (if (i32.or
                (i32.and (i64.lt_u (local.get $a_lo) (i64.const 2)) (i64.eqz (local.get $a_hi)))
                (i64.eqz (i64.or (i64.xor (local.get $b_lo) (i64.const 1)) (local.get $b_hi)))
            )
            (then (return (local.get $a_lo) (local.get $a_hi)))
        )

        ;; otherwise, if b < 0 => runtime error
        (if (i64.lt_s (local.get $b_hi) (i64.const 0))
            (then (call $stdlib.runtime-error (i32.const 8)))
        )

        ;; if b > (a >= 0 ? 126 : 127) -> runtime error: overflow (since the biggest b that doesn't
        ;; overflow is in 2^126 and -2^127, and this is an edge case)
        (if (i32.or
                (i64.gt_u
                    (local.get $b_lo)
                    (i64.add (i64.const 126) (i64.extend_i32_u (i64.lt_s (local.get $a_hi) (i64.const 0))))
                )
                (i64.ne (local.get $b_hi) (i64.const 0))
            )
            ;; In the interpreter, overflows for the power operation throw a specific error,
            ;; not a general ArithmeticOverflow error.
            ;; Therefore, the runtime error code should be 8,
            ;; which maps to the specific error.
            (then (call $stdlib.runtime-error (i32.const 8)))
        )

        ;; shortcut if a == 2
        (if (i64.eqz (i64.or (i64.xor (local.get $a_lo) (i64.const 2)) (local.get $a_hi)))
            (then
                (return
                    (select
                        (i64.shl (i64.const 1) (local.get $b_lo))
                        (i64.const 0)
                        (local.tee $negative (i64.lt_u (local.get $b_lo) (i64.const 64)))
                    )
                    (select
                        (i64.const 0)
                        (i64.shl (i64.const 1) (i64.sub (local.get $b_lo) (i64.const 64)))
                        (local.get $negative)
                    )
                )
            )
        )

        ;; shortcut if a == -2 (handles edge case -2^127)
        (if (i32.and (i64.eq (local.get $a_lo) (i64.const -2)) (i64.eq (local.get $a_hi) (i64.const -1)))
            (then
                (local.set $a_lo (select (i64.const -1) (i64.const 1) (local.tee $negative (i32.wrap_i64 (i64.and (local.get $b_lo) (i64.const 1))))))
                (local.set $a_hi (select (i64.const -1) (i64.const 0) (local.get $negative)))
                (return
                    (select
                        (i64.shl (local.get $a_lo) (local.get $b_lo))
                        (i64.const 0)
                        (local.tee $negative (i64.lt_u (local.get $b_lo) (i64.const 64)))
                    )
                    (select
                        (local.get $a_hi)
                        (i64.shl (local.get $a_lo) (i64.sub (local.get $b_lo) (i64.const 64)))
                        (local.get $negative)
                    )
                )
            )
        )

        ;; $pow-inner arguments: abs(a) and $b_lo
        ;; no need to care of i128::MIN, at this point it will overflow
        ;; abs($a_lo)
        (select
            (i64.sub (i64.const 0) (local.get $a_lo))
            (local.get $a_lo)
            (local.tee $negative (i64.lt_s (local.get $a_hi) (i64.const 0)))
        )
        ;; abs($a_hi)
        (select
            (i64.sub (i64.const 0) (i64.add (local.get $a_hi) (i64.extend_i32_u (i64.ne (local.get $a_lo) (i64.const 0)))))
            (local.get $a_hi)
            (local.get $negative)
        )
        ;; $b_lo
        (local.tee $negative (i32.wrap_i64 (local.get $b_lo)))

        ;; $negative is 1 if end result should be negative else 0
        (local.set $negative
            (i32.and (i64.lt_s (local.get $a_hi) (i64.const 0))
                     (i32.and (local.get $negative) (i32.const 1))
            )
        )

        (call $pow-inner)
        (local.set $a_hi)
        (local.set $a_lo)

        ;; overflow if result is negative
        (if (i64.lt_s (local.get $a_hi) (i64.const 0))
            (then (call $stdlib.runtime-error (i32.const 0)))
        )

        (if (result i64 i64) (local.get $negative)
            (then
                (i64.sub (i64.const 0) (local.get $a_lo))
                (i64.sub (i64.const 0) (i64.add (local.get $a_hi) (i64.extend_i32_u (i64.ne (local.get $a_lo) (i64.const 0)))))
            )
            (else
                (local.get $a_lo)
                (local.get $a_hi)
            )
        )
    )

    (func $stdlib.sha256-buf (param $offset i32) (param $length i32) (param $offset-result i32) (param $workspace-offset i32) (result i32 i32)
        (local $i i32)
        ;; see this for an explanation: https://sha256algorithm.com/

        (call $extend-data (local.get $offset) (local.get $length) (local.get $workspace-offset))
        (local.set $length)

        (local.set $i (i32.const 0))
        (loop
            (call $block64 (local.get $i) (local.get $workspace-offset))
            (call $working-vars local.get $workspace-offset)
            (br_if 0
                (i32.lt_u
                    (local.tee $i (i32.add (local.get $i) (i32.const 64)))
                    (local.get $length)
                )
            )
        )

        ;; store at result position with correct endianness
        (v128.store
            (local.get $offset-result)
            (i8x16.swizzle
                (v128.load (local.get $workspace-offset))
                (v128.const i8x16 3 2 1 0 7 6 5 4 11 10 9 8 15 14 13 12)
            )
        )
        (v128.store offset=16
            (local.get $offset-result)
            (i8x16.swizzle
                (v128.load offset=16 (local.get $workspace-offset))
                (v128.const i8x16 3 2 1 0 7 6 5 4 11 10 9 8 15 14 13 12)
            )
        )

        (local.get $offset-result) (i32.const 32)
    )

    (func $stdlib.sha256-int (param $lo i64) (param $hi i64) (param $offset-result i32) (param $workspace-offset i32) (result i32 i32)
        ;; Copy data to the working stack, so that it has this relative configuration:
        ;;   0..32 -> Initial hash vals (will be the result hash in the end)
        ;;   32..288 -> Space to store W
        ;;   288..352 -> extended int
        (memory.copy (local.get $workspace-offset) (i32.const 0) (i32.const 32))

        (i64.store offset=288 (local.get $workspace-offset) (local.get $lo))
        (i64.store offset=296 (local.get $workspace-offset) (local.get $hi)) ;; offset = 288 + 8
        (i32.store offset=304 (local.get $workspace-offset) (i32.const 0x80)) ;; offset = 288+16
        (memory.fill (i32.add (local.get $workspace-offset) (i32.const 308)) (i32.const 0) (i32.const 46)) ;; offset = 288+20
        (i32.store8 offset=351 (local.get $workspace-offset) (i32.const 0x80)) ;; offset = 288+63

        (call $block64 (i32.const 0) (local.get $workspace-offset))
        (call $working-vars (local.get $workspace-offset))

        (v128.store
            (local.get $offset-result)
            (i8x16.swizzle
                (v128.load (local.get $workspace-offset))
                (v128.const i8x16 3 2 1 0 7 6 5 4 11 10 9 8 15 14 13 12)
            )
        )
        (v128.store offset=16
            (local.get $offset-result)
            (i8x16.swizzle
                (v128.load offset=16 (local.get $workspace-offset))
                (v128.const i8x16 3 2 1 0 7 6 5 4 11 10 9 8 15 14 13 12)
            )
        )

        (local.get $offset-result) (i32.const 32)
    )

    (func $extend-data (param $offset i32) (param $length i32) (param $workspace-offset i32) (result i32)
        (local $res_len i32) (local $len64 i64)

        ;; Move data to the working stack, so that it has this relative configuration:
        ;;   0..32 -> Initial hash vals (will be the result hash in the end)
        ;;   32..288 -> Space to store W (result of $block64)
        ;;   288..$length+288 -> shifted data
        (memory.copy (local.get $workspace-offset) (i32.const 0) (i32.const 32))
        (memory.copy (i32.add (local.get $workspace-offset) (i32.const 288)) (local.get $offset) (local.get $length))

        (local.set $res_len ;; total size of data with expansion
            (i32.add
                (i32.or
                    ;; len + 8 bytes for the size
                    (i32.add (local.get $length) (i32.const 8))
                    (i32.const 0x3f)
                )
                (i32.const 1)
            )
        )

        ;; Add "1" at the end of the data
        (i32.store offset=288
            (i32.add (local.get $workspace-offset) (local.get $length))
            (i32.const 0x80)
        )

        ;; Fill the remaining part before the size with 0s
        (memory.fill
            (i32.add (i32.add (local.get $workspace-offset) (local.get $length)) (i32.const 289))
            (i32.const 0)
            (i32.sub (i32.sub (local.get $res_len) (local.get $length)) (i32.const 8))
        )

        ;; Add the size, as a 64bits big-endian integer
        (local.set $len64 (i64.extend_i32_u (i32.shl (local.get $length) (i32.const 3))))
        (i32.sub (i32.add (local.get $workspace-offset) (local.get $res_len)) (i32.const 8))
        (i64.or
            (i64.or
                (i64.or
                    (i64.shl (local.get $len64) (i64.const 0x38))
                    (i64.shl (i64.and (local.get $len64) (i64.const 0xff00)) (i64.const 0x28))
                )
                (i64.or
                    (i64.shl (i64.and (local.get $len64) (i64.const 0xff0000)) (i64.const 0x18))
                    (i64.shl (i64.and (local.get $len64) (i64.const 0xff000000)) (i64.const 0x8))
                )
            )
            (i64.or
                (i64.or
                    (i64.and (i64.shr_u (local.get $len64) (i64.const 0x8)) (i64.const 0xff000000))
                    (i64.and (i64.shr_u (local.get $len64) (i64.const 0x18)) (i64.const 0xff0000))
                )
                (i64.or
                    (i64.and (i64.shr_u (local.get $len64) (i64.const 0x28)) (i64.const 0xff00))
                    (i64.shr_u (local.get $len64) (i64.const 0x38))
                )
            )
        )
        i64.store offset=288

        (local.get $res_len)
    )

    (func $block64 (param $data i32) (param $workspace-offset i32)
        (local $origin i32)
        (local $i i32) (local $tmp i32)

        (local.set $origin (local.get $workspace-offset))
        (local.set $data (i32.add (local.get $origin) (local.get $data)))

        (local.set $i (i32.const 0))
        ;; copy first 64 bytes of data to offset as i32 with endianness adjustment
        ;; Using v128 to process more bytes at a time
        ;; TODO? : unroll this loop, since it's one instruction 4 times?
        (loop
            (i32.add (local.get $origin) (local.get $i))
            (i8x16.swizzle
                (v128.load offset=288 (i32.add (local.get $data) (local.get $i)))
                (v128.const i8x16 3 2 1 0 7 6 5 4 11 10 9 8 15 14 13 12)
            )
            v128.store offset=32

            (br_if 0
                (i32.lt_u
                    (local.tee $i (i32.add (local.get $i) (i32.const 16)))
                    (i32.const 64)
                )
            )
        )

        (local.set $i (i32.const 0))
        (loop
            (local.set $data (i32.add (local.get $origin) (local.get $i)))
            ;; store address: w(current+16)
            (i32.add (local.get $data) (i32.const 64))
            ;; w(current)
            (i32.load offset=32 (local.get $data))
            ;; sigma 0
            (local.set $tmp (i32.load offset=36 (local.get $data))) ;; offset = 32 + 4
            (i32.rotr (local.get $tmp) (i32.const 7))
            (i32.xor (i32.rotr (local.get $tmp) (i32.const 18)))
            (i32.xor (i32.shr_u (local.get $tmp) (i32.const 3)))
            i32.add
            ;; w(current+9)
            (i32.add (i32.load offset=68 (local.get $data))) ;; offset = 32+36
            ;; sigma 1
            (local.set $tmp (i32.load offset=88 (local.get $data))) ;; offset = 32+56
            (i32.rotr (local.get $tmp) (i32.const 17))
            (i32.xor (i32.rotr (local.get $tmp) (i32.const 19)))
            (i32.xor (i32.shr_u (local.get $tmp) (i32.const 10)))
            i32.add
            ;; save
            i32.store offset=32

            (br_if 0
                (i32.lt_u
                    (local.tee $i (i32.add (local.get $i) (i32.const 4)))
                    (i32.const 192)
                )
            )
        )
    )

    (func $working-vars (param $workspace-offset i32)
        (local $origin i32)
        (local $a i32) (local $b i32) (local $c i32) (local $d i32)
        (local $e i32) (local $f i32) (local $g i32) (local $h i32)
        (local $temp1 i32) (local $temp2 i32) (local $i i32)

        (local.set $origin (local.get $workspace-offset))

        (local.set $a (i32.load offset=0 (local.get $origin)))
        (local.set $b (i32.load offset=4 (local.get $origin)))
        (local.set $c (i32.load offset=8 (local.get $origin)))
        (local.set $d (i32.load offset=12 (local.get $origin)))
        (local.set $e (i32.load offset=16 (local.get $origin)))
        (local.set $f (i32.load offset=20 (local.get $origin)))
        (local.set $g (i32.load offset=24 (local.get $origin)))
        (local.set $h (i32.load offset=28 (local.get $origin)))

        (local.set $i (i32.const 0))
        (loop
        ;; compute $temp1: h + sigma1 + choice + k0 + w0
            (local.get $h) ;; h

            (i32.rotr (local.get $e) (i32.const 6))
            (i32.xor (i32.rotr (local.get $e) (i32.const 11)))
            (i32.xor (i32.rotr (local.get $e) (i32.const 25)))
            i32.add ;; + sigma1

            (i32.and (local.get $e) (local.get $f))
            (i32.xor (i32.and (i32.xor (local.get $e) (i32.const -1)) (local.get $g)))
            i32.add ;; + choice

            (i32.add (i32.load offset=32 (local.get $i))) ;; + k(current)

            (i32.add (i32.load offset=32 (i32.add (local.get $origin) (local.get $i)))) ;; + w(current)
            (local.set $temp1)

            ;; compute temp2: sigma0 + majority
            (i32.rotr (local.get $a) (i32.const 2))
            (i32.xor (i32.rotr (local.get $a) (i32.const 13)))
            (i32.xor (i32.rotr (local.get $a) (i32.const 22))) ;; sigma0

            (i32.and (local.get $a) (local.get $b))
            (i32.xor (i32.and (local.get $a) (local.get $c)))
            (i32.xor (i32.and (local.get $b) (local.get $c)))
            i32.add ;; + majority
            (local.set $temp2)

            ;; assign new variables
            (local.set $h (local.get $g))
            (local.set $g (local.get $f))
            (local.set $f (local.get $e))
            (local.set $e (i32.add (local.get $d) (local.get $temp1)))
            (local.set $d (local.get $c))
            (local.set $c (local.get $b))
            (local.set $b (local.get $a))
            (local.set $a (i32.add (local.get $temp1) (local.get $temp2)))

            (br_if 0
                (i32.lt_u
                    (local.tee $i (i32.add (local.get $i) (i32.const 4)))
                    (i32.const 256)
                )
            )
        )

        ;; update hash
        (i32.store offset=0 (local.get $origin) (i32.add (i32.load offset=0 (local.get $origin)) (local.get $a)))
        (i32.store offset=4 (local.get $origin) (i32.add (i32.load offset=4 (local.get $origin)) (local.get $b)))
        (i32.store offset=8 (local.get $origin) (i32.add (i32.load offset=8 (local.get $origin)) (local.get $c)))
        (i32.store offset=12 (local.get $origin) (i32.add (i32.load offset=12 (local.get $origin)) (local.get $d)))
        (i32.store offset=16 (local.get $origin) (i32.add (i32.load offset=16 (local.get $origin)) (local.get $e)))
        (i32.store offset=20 (local.get $origin) (i32.add (i32.load offset=20 (local.get $origin)) (local.get $f)))
        (i32.store offset=24 (local.get $origin) (i32.add (i32.load offset=24 (local.get $origin)) (local.get $g)))
        (i32.store offset=28 (local.get $origin) (i32.add (i32.load offset=28 (local.get $origin)) (local.get $h)))
    )

    (func $stdlib.hash160-buf (param $offset i32) (param $length i32) (param $offset-result i32) (param $workspace-offset i32) (result i32 i32)
        (local $i i32)
        ;; ripemd-160 article: https://www.esat.kuleuven.be/cosic/publications/article-317.pdf
        ;; Here we implement a ripemd with an easier padding since inputs are results of sha256,
        ;; and thus always have the same length.

        ;; move $worksapce-offset: current value will contain sha256 result and moved place is new stack
        (local.set $workspace-offset (i32.add (local.tee $i (local.get $workspace-offset)) (i32.const 32)))
        ;; compute sha256
        (call $stdlib.sha256-buf (local.get $offset) (local.get $length) (local.get $i) (local.get $workspace-offset))
        drop ;; we don't need the length of sha256, it is always 32
        (local.set $workspace-offset) ;; set $workspace-offset to its original value, aka offset of sha256 result

        (call $hash160-pad (local.get $workspace-offset))
        (call $hash160-compress (local.get $offset-result) (local.get $workspace-offset))

        (local.get $offset-result) (i32.const 20)
    )

    (func $stdlib.hash160-int (param $lo i64) (param $hi i64) (param $offset-result i32) (param $workspace-offset i32) (result i32 i32)
        (local $i i32)
        ;; ripemd-160 article: https://www.esat.kuleuven.be/cosic/publications/article-317.pdf
        ;; Here we implement a ripemd with an easier padding since inputs are results of sha256,
        ;; and thus always have the same length.

        ;; move $workspace-offset: current value will contain sha256 result and moved place is new stack
        (local.set $workspace-offset (i32.add (local.tee $i (local.get $workspace-offset)) (i32.const 32)))
        ;; compute sha256
        (call $stdlib.sha256-int (local.get $lo) (local.get $hi) (local.get $i) (local.get $workspace-offset))
        drop ;; we don't need the length of sha256, it is always 32
        (local.set $workspace-offset) ;; set $workspace-offset to its original value, aka offset of sha256 result

        (call $hash160-pad (local.get $workspace-offset))
        (call $hash160-compress (local.get $offset-result) (local.get $workspace-offset))

        (local.get $offset-result) (i32.const 20)
    )

    (func $hash160-pad (param $workspace-offset i32)
        ;; MD-padding: (already placed sha256 +) "1" + "00000..." + size as i64 big endian
        (i64.store offset=32 (local.get $workspace-offset) (i64.const 0x80))
        (memory.fill
            (i32.add (local.get $workspace-offset) (i32.const 40))
            (i32.const 0)
            (i32.const 16)
        )
        (i64.store offset=56 (local.get $workspace-offset) (i64.const 256))
    )

    (func $hash160-compress (param $offset-result i32) (param $workspace-offset i32)
        (local $h0 i32) (local $h1 i32) (local $h2 i32) (local $h3 i32) (local $h4 i32)
        (local $a1 i32) (local $b1 i32) (local $c1 i32) (local $d1 i32) (local $e1 i32)
        (local $a2 i32) (local $b2 i32) (local $c2 i32) (local $d2 i32) (local $e2 i32)
        (local $i i32) (local $round i32)

        (local.set $a2 (local.tee $a1 (local.tee $h0 (i32.const 0x67452301))))
        (local.set $b2 (local.tee $b1 (local.tee $h1 (i32.const 0xefcdab89))))
        (local.set $c2 (local.tee $c1 (local.tee $h2 (i32.const 0x98badcfe))))
        (local.set $d2 (local.tee $d1 (local.tee $h3 (i32.const 0x10325476))))
        (local.set $e2 (local.tee $e1 (local.tee $h4 (i32.const 0xc3d2e1f0))))

        (local.set $i (i32.const 0))
        (loop
            (local.set $round (i32.shr_u (local.get $i) (i32.const 4)))
            ;; ROUND
            ;; a
            (local.get $a1)

            ;; + f(round, b, c, d) + K(i)
            (local.get $b1) (local.get $c1) (local.get $d1)
            (i32.load offset=608 (i32.shl (local.get $round) (i32.const 2)))
            (call_indirect (type $hash160-compress-function) (local.get $round))
            i32.add

            ;; + word[r[i]]
            (i32.load
                (i32.add
                    (local.get $workspace-offset)
                    (i32.shl (i32.load8_u offset=288 (local.get $i)) (i32.const 2))
                )
            )
            i32.add

            ;; left-rotate the addition by s[i]
            (i32.load8_u offset=448 (local.get $i))
            i32.rotl

            ;; + e
            (i32.add (local.get $e1))

            ;; set new vars
            (local.set $a1 (local.get $e1))
            (local.set $e1 (local.get $d1))
            (local.set $d1 (i32.rotl (local.get $c1) (i32.const 10)))
            (local.set $c1 (local.get $b1))
            (local.set $b1) ;; set with addition on the top of the stack

            ;; PARALLEL ROUND
            ;; a'
            (local.get $a2)

            ;; + f(round, b', c', d') + K'(i)
            (local.get $b2) (local.get $c2) (local.get $d2)
            (i32.load offset=628 (i32.shl (local.get $round) (i32.const 2)))
            (call_indirect (type $hash160-compress-function) (i32.sub (i32.const 4) (local.get $round)))
            i32.add

            ;; + word[r'[i]]
            (i32.load
                (i32.add
                    (local.get $workspace-offset)
                    (i32.shl (i32.load8_u offset=368 (local.get $i)) (i32.const 2))
                )
            )
            i32.add

            ;; left-rotate the addition by s'[i]
            (i32.load8_u offset=528 (local.get $i))
            i32.rotl

            ;; + e'
            (i32.add (local.get $e2))

            ;; set new vars
            (local.set $a2 (local.get $e2))
            (local.set $e2 (local.get $d2))
            (local.set $d2 (i32.rotl (local.get $c2) (i32.const 10)))
            (local.set $c2 (local.get $b2))
            (local.set $b2) ;; set with addition on the top of the stack

            (br_if 0
                (i32.lt_u
                    (local.tee $i (i32.add (local.get $i) (i32.const 1)))
                    (i32.const 80)
                )
            )
        )

        ;; compute and save result to $offset-result
        (i32.store (local.get $offset-result) (i32.add (i32.add (local.get $h1) (local.get $c1)) (local.get $d2)))
        (i32.store offset=4 (local.get $offset-result) (i32.add (i32.add (local.get $h2) (local.get $d1)) (local.get $e2)))
        (i32.store offset=8 (local.get $offset-result) (i32.add (i32.add (local.get $h3) (local.get $e1)) (local.get $a2)))
        (i32.store offset=12 (local.get $offset-result) (i32.add (i32.add (local.get $h4) (local.get $a1)) (local.get $b2)))
        (i32.store offset=16 (local.get $offset-result) (i32.add (i32.add (local.get $h0) (local.get $b1)) (local.get $c2)))
    )

    (func $hash160-f1 (type $hash160-compress-function)
        (param $x i32) (param $y i32) (param $z i32) (param $k i32) (result i32)
        (i32.xor (i32.xor (local.get $x) (local.get $y)) (local.get $z))
        (i32.add (local.get $k))
    )

    (func $hash160-f2 (type $hash160-compress-function)
        (param $x i32) (param $y i32) (param $z i32) (param $k i32) (result i32)
        (i32.or
            (i32.and (local.get $x) (local.get $y))
            (i32.and (i32.xor (local.get $x) (i32.const -1)) (local.get $z))
        )
        (i32.add (local.get $k))
    )

    (func $hash160-f3 (type $hash160-compress-function)
        (param $x i32) (param $y i32) (param $z i32) (param $k i32) (result i32)
        (i32.xor
            (i32.or (local.get $x) (i32.xor (local.get $y) (i32.const -1)))
            (local.get $z)
        )
        (i32.add (local.get $k))
    )

    (func $hash160-f4 (type $hash160-compress-function)
        (param $x i32) (param $y i32) (param $z i32) (param $k i32) (result i32)
        (i32.or
            (i32.and (local.get $x) (local.get $z))
            (i32.and (local.get $y) (i32.xor (local.get $z) (i32.const -1)))
        )
        (i32.add (local.get $k))
    )

    (func $hash160-f5 (type $hash160-compress-function)
        (param $x i32) (param $y i32) (param $z i32) (param $k i32) (result i32)
        (i32.xor
            (local.get $x)
            (i32.or (local.get $y) (i32.xor (local.get $z) (i32.const -1)))
        )
        (i32.add (local.get $k))
    )

    (func $stdlib.store-i32-be (param $address i32) (param $value i32)
        (i32.store
            (local.get $address)
            (i32.or
                (i32.or
                    (i32.shl (local.get $value) (i32.const 24))
                    (i32.shl (i32.and (local.get $value) (i32.const 0xff00)) (i32.const 8))
                )
                (i32.or
                    (i32.and (i32.shr_u (local.get $value) (i32.const 8)) (i32.const 0xff00))
                    (i32.shr_u (local.get $value) (i32.const 24))
                )
            )
        )
    )

    (func $stdlib.load-i32-be (param $address i32) (result i32)
        (local $value i32)
        (local.set $value (i32.load (local.get $address)))
        (i32.or
            (i32.or
                (i32.shl (local.get $value) (i32.const 24))
                (i32.shl (i32.and (local.get $value) (i32.const 0xff00)) (i32.const 8))
            )
            (i32.or
                (i32.and (i32.shr_u (local.get $value) (i32.const 8)) (i32.const 0xff00))
                (i32.shr_u (local.get $value) (i32.const 24))
            )
        )
    )

    (func $stdlib.store-i64-be (param $address i32) (param $value i64)
        (i64.store
            (local.get $address)
            (i64.or
                (i64.or
                    (i64.or
                        (i64.shl (local.get $value) (i64.const 56))
                        (i64.shl (i64.and (local.get $value) (i64.const 0xff00)) (i64.const 40))
                    )
                    (i64.or
                        (i64.shl (i64.and (local.get $value) (i64.const 0xff0000)) (i64.const 24))
                        (i64.shl (i64.and (local.get $value) (i64.const 0xff000000)) (i64.const 8))
                    )
                )
                (i64.or
                    (i64.or
                        (i64.and (i64.shr_u (local.get $value) (i64.const 8)) (i64.const 0xff000000))
                        (i64.and (i64.shr_u (local.get $value) (i64.const 24)) (i64.const 0xff0000))
                    )
                    (i64.or
                        (i64.and (i64.shr_u (local.get $value) (i64.const 40)) (i64.const 0xff00))
                        (i64.shr_u (local.get $value) (i64.const 56))
                    )
                )
            )
        )
    )

    (func $stdlib.buff-to-uint-be (param $offset i32) (param $length i32) (result i64 i64)
        (local $mask_lo i64) (local $mask_hi i64) (local $double v128)
        (if (i32.gt_u (local.get $length) (i32.const 16))
            (then (call $stdlib.runtime-error (i32.const 5)))
        )

        (if (i32.eqz (local.get $length))
            (then (return (i64.const 0) (i64.const 0)))
        )

        ;; SAFETY: this function works because we already have data in the memory,
        ;;         otherwise we could have a negative offset.
        (local.set $offset (i32.sub (i32.add (local.get $offset) (local.get $length)) (i32.const 16)))

        ;; we compute masks for the low and high part of the resulting integer
        (local.set $mask_lo
            (select
                (i64.const -1)
                (local.tee $mask_hi
                    (i64.shr_u (i64.const -1) (i64.extend_i32_u (i32.and (i32.mul (local.get $length) (i32.const 56)) (i32.const 56))))
                )
                (i32.ge_u (local.get $length) (i32.const 8))
            )
        )
        (local.set $mask_hi (select (local.get $mask_hi) (i64.const 0) (i32.gt_u (local.get $length) (i32.const 8))))

        ;; we load both low and high part at once, and rearrange the bytes for endianness
        (local.set $double
            (i8x16.swizzle
                (v128.load (local.get $offset))
                (v128.const i8x16 7 6 5 4 3 2 1 0 15 14 13 12 11 10 9 8)
            )
        )

        (i64.and (i64x2.extract_lane 1 (local.get $double)) (local.get $mask_lo))
        (i64.and (i64x2.extract_lane 0 (local.get $double)) (local.get $mask_hi))
    )

    (func $stdlib.buff-to-uint-le (param $offset i32) (param $length i32) (result i64 i64)
        (local $mask_lo i64) (local $mask_hi i64)
        (if (i32.gt_u (local.get $length) (i32.const 16))
            (then (call $stdlib.runtime-error (i32.const 5)))
        )

        (if (i32.eqz (local.get $length))
            (then (return (i64.const 0) (i64.const 0)))
        )

        (local.set $mask_lo
            (select
                (i64.const -1)
                (local.tee $mask_hi
                    (i64.shr_u (i64.const -1) (i64.extend_i32_u (i32.and (i32.mul (local.get $length) (i32.const 56)) (i32.const 56))))
                )
                (i32.ge_u (local.get $length) (i32.const 8))
            )
        )
        (local.set $mask_hi (select (local.get $mask_hi) (i64.const 0) (i32.gt_u (local.get $length) (i32.const 8))))

        (i64.and (i64.load (local.get $offset)) (local.get $mask_lo))
        (i64.and (i64.load offset=8 (local.get $offset)) (local.get $mask_hi))
    )

    ;;
    ;; logical 'not' implementation
    ;;
    (func $stdlib.not (param $bool_in i32) (result i32)
        (i32.eqz (local.get $bool_in))
    )

    ;;
    ;; `(principal-construct? version pkhash)` implementation
    ;; `version` is a `(buff 1)` and `pkhash` is a `(buff 20)`.
    ;;
    (func $stdlib.principal-construct
            (param $version_offset i32)
            (param $version_length i32)
            (param $pkhash_offset i32)
            (param $pkhash_length i32)
            (param $contract_present i32)
            (param $contract_offset i32)
            (param $contract_length i32)
            (param $res_principal_offset i32)
            (result i32 i32 i32 i64 i64 i32 i32 i32)
        (local $version i32) (local $valid i32) (local $result_length i32)
        ;; Return `(err u1)` if `version` is empty. The type-checker and
        ;; compiler ensure it cannot be > 1 byte.
        ;; PrincipalConstructErrorCode::BUFFER_LENGTH == u1
        (if (i32.eqz (local.get $version_length))
            (then
                (i32.const 0) ;; err indicator
                (i32.const 0) ;; ok value placeholder
                (i32.const 0) ;; ok value placeholder
                (i64.const 1) ;; error_code low
                (i64.const 0) ;; error_code high
                (i32.const 0) ;; principal none indicator
                (i32.const 0) ;; principal placeholder
                (i32.const 0) ;; principal placeholder
                (return)
            )
        )

        ;; Load the version byte
        (local.tee $version (i32.load8_u (local.get $version_offset)))

        ;; Return `(err u1)` if `version` is >= 32.
        (i32.const 32)
        (if (i32.ge_u)
            (then
                (i32.const 0) ;; err indicator
                (i32.const 0) ;; ok value placeholder
                (i32.const 0) ;; ok value placeholder
                (i64.const 1) ;; error_code low
                (i64.const 0) ;; error_code high
                (i32.const 0) ;; principal none indicator
                (i32.const 0) ;; principal placeholder
                (i32.const 0) ;; principal placeholder
                (return)
            )
        )

        ;; Check if the version matches the current network
        (local.set $valid (call $stdlib.is-version-valid (local.get $version)))

        ;; If the public key hash buffer has less than 20 bytes, this is a
        ;; runtime error. The type-checker and compiler ensure it cannot be
        ;; > 20 bytes.
        (if (i32.lt_u (local.get $pkhash_length) (i32.const 20))
            (then
                (i32.const 0) ;; err indicator
                (i32.const 0) ;; ok value placeholder
                (i32.const 0) ;; ok value placeholder
                (i64.const 1) ;; error_code low
                (i64.const 0) ;; error_code high
                (i32.const 0) ;; principal none indicator
                (i32.const 0) ;; principal placeholder
                (i32.const 0) ;; principal placeholder
                (return)
            )
        )

        ;; Build the principal on the call stack
        ;; Write the version
        (i32.store8 (local.get $res_principal_offset) (local.get $version))
        ;; Write the public key hash
        (memory.copy
            (i32.add (local.get $res_principal_offset) (i32.const 1))
            (local.get $pkhash_offset)
            (i32.const 20)
        )
        ;; Write the size of the contract name
        (i32.store8 offset=21 (local.get $res_principal_offset) (local.get $contract_length))

        ;; If a contract name is specified, check if it is valid. If so,
        ;; append it to the principal
        (if (i32.eq (local.get $contract_present) (i32.const 1))
            (then
                ;; Check if this is a valid contract name. If not return an error.
                ;; PrincipalConstructErrorCode::CONTRACT_NAME == 2
                (if (i32.eqz (call $stdlib.is-valid-contract-name (local.get $contract_offset) (local.get $contract_length)))
                    (then
                        (i32.const 0) ;; err indicator
                        (i32.const 0) ;; ok value placeholder
                        (i32.const 0) ;; ok value placeholder
                        (i64.const 2) ;; error_code low
                        (i64.const 0) ;; error_code high
                        (i32.const 0) ;; principal none indicator
                        (i32.const 0) ;; principal placeholder
                        (i32.const 0) ;; principal placeholder
                        (return)
                    )
                )

                ;; Copy the contract name to the stack
                (memory.copy
                    (i32.add (local.get $res_principal_offset) (i32.const 22))
                    (local.get $contract_offset)
                    (local.get $contract_length)
                )
            )
        )

        (local.set $result_length (i32.add (local.get $contract_length) (i32.const 22)))

        ;; If the version was valid, return an ok value
        (if (result i32 i32 i32 i64 i64 i32 i32 i32) (local.get $valid)
            (then
                ;; (ok the-principal)
                (i32.const 1) ;; ok indicator
                (local.get $res_principal_offset) ;; principal offset
                (local.get $result_length) ;; principal length
                (i64.const 0) ;; error_code placeholder
                (i64.const 0) ;; error_code placeholder
                (i32.const 0) ;; optional placeholder
                (i32.const 0) ;; principal placeholder
                (i32.const 0) ;; principal placeholder
            )
            (else
                ;; (err {error_code: VERSION_BYTE, principal: (some the-principal)})
                (i32.const 0) ;; err indicator
                (i32.const 0) ;; ok value placeholder
                (i32.const 0) ;; ok value placeholder
                (i64.const 0) ;; error_code low
                (i64.const 0) ;; error_code high
                (i32.const 1) ;; principal some indicator
                (local.get $res_principal_offset) ;; principal offset
                (local.get $result_length) ;; principal length
            )
        )
    )

    (func $stdlib.is-valid-contract-name (param $offset i32) (param $length i32) (result i32)
        (local $end i32)

        ;; Check if the string is empty
        (local.get $length)
        (if (i32.eqz)
            (then (return (i32.const 0)))
        )

        ;; Check the first character: [a-zA-Z]
        (call $stdlib.is-alpha (i32.load8_u (local.get $offset)))
        (if (i32.eqz)
            (then
                ;; There is a special case for the contract name `__transient`.
                (if (call $stdlib.is-transient (local.get $offset) (local.get $length))
                    (then (return (i32.const 1)))
                )
                (return (i32.const 0))
            )
        )

        ;; Check remaining characters: [a-zA-Z0-9_-]
        (local.set $end (i32.add (local.get $offset) (local.get $length)))
        (local.set $offset (i32.add (local.get $offset) (i32.const 1)))

        (loop $char_loop
            (if (i32.eq (local.get $offset) (local.get $end))
                (then (return (i32.const 1)))
            )

            (if (i32.eqz (call $stdlib.is-valid-char (i32.load8_u (local.get $offset))))
                (then (return (i32.const 0)))
            )

            (local.set $offset (i32.add (local.get $offset) (i32.const 1)))
            (br $char_loop)
        )

        (unreachable)
    )

    ;; Helper function to check if a character is a letter [a-zA-Z]
    (func $stdlib.is-alpha (param $char i32) (result i32)
        (i32.lt_u
            (i32.and
                (i32.sub (i32.and (local.get $char) (i32.const 223)) (i32.const 65))
                (i32.const 255)
            )
            (i32.const 26)
        )
    )

    ;; Helper function to check if a character is valid [a-zA-Z0-9_-]
    (func $stdlib.is-valid-char (param $char i32) (result i32)
        (call $stdlib.is-alpha (local.get $char)) ;; [a-zA-Z]

        (i32.ge_u (local.get $char) (i32.const 48)) ;; >= '0'
        (i32.le_u (local.get $char) (i32.const 57)) ;; <= '9'
        (i32.and)

        (i32.or)

        (i32.eq (local.get $char) (i32.const 45)) ;; '-'
        (i32.eq (local.get $char) (i32.const 95)) ;; '_'
        (i32.or)

        (i32.or)
    )

    ;; Helper function to check if a string is `__transient`
    (func $stdlib.is-transient (param $offset i32) (param $length i32) (result i32)
        (if (result i32)
            (i32.ne (local.get $length) (i32.const 11)) ;; Length must be 11
            (then (i32.const 0))
            (else
                (v128.load (local.get $offset))
                ;; keep 11 bytes
                (v128.and (v128.const i64x2 0xffffffffffffffff 0xffffff))
                ;; == "__transient"
                (v128.xor (v128.const i8x16 0x5f 0x5f 0x74 0x72 0x61 0x6e 0x73 0x69 0x65 0x6e 0x74 0x00 0x00 0x00 0x00 0x00))
                ;; after a xor comparison, if everything is equal, everything is 0
                v128.any_true
                i32.eqz
            )
        )
    )

    ;; Check if the version matches the current network
    (func $stdlib.is-version-valid (param $version i32) (result i32)
        (if (result i32) (call $stdlib.is_in_mainnet)
            (then
                (local.get $version)
                (i32.const 20) ;; C32_ADDRESS_VERSION_MAINNET_MULTISIG
                (i32.eq)
                (local.get $version)
                (i32.const 22) ;; C32_ADDRESS_VERSION_MAINNET_SINGLESIG
                (i32.eq)
                (i32.or)
            )
            (else
                (local.get $version)
                (i32.const 21) ;; C32_ADDRESS_VERSION_TESTNET_MULTISIG
                (i32.eq)
                (local.get $version)
                (i32.const 26) ;; C32_ADDRESS_VERSION_TESTNET_SINGLESIG
                (i32.eq)
                (i32.or)
            )
        )
    )

    (func $stdlib.string-to-uint (param $offset i32) (param $len i32) (result i32 i64 i64)
        (local $lo i64) (local $hi i64) (local $loaded i64)
        ;; a string is automatically invalid if its size is 0 or
        ;; bigger than 39, the max number of digits of a u128
        (if (i32.lt_u (i32.sub (local.get $len) (i32.const 40)) (i32.const -39))
            (then (return (i32.const 0) (i64.const 0) (i64.const 0)))
        )

        ;; loop with simple multiplication, for speed
        (loop $loop_small
            ;; if next digit is valid, $lo * 10 + digit, otherwise we return none
            (if (i64.lt_u (local.tee $loaded (i64.sub (i64.load8_u (local.get $offset)) (i64.const 48))) (i64.const 10))
                (then
                    (local.set $lo (i64.add (i64.mul (local.get $lo) (i64.const 10)) (local.get $loaded)))
                )
                (else
                    (return (i32.const 0) (i64.const 0) (i64.const 0))
                )
            )
            (local.set $offset (i32.add (local.get $offset) (i32.const 1)))
            ;; we branch while we still have digits to add and $lo < (u64::MAX / 10)
            (br_if $loop_small
                (i32.and
                    (i32.ne (local.tee $len (i32.sub (local.get $len) (i32.const 1))) (i32.const 0))
                    (i64.lt_u (local.get $lo) (i64.const 1844674407370955161))
                )
            )
        )

        ;; we return if no more digits
        (if (i32.eqz (local.get $len))
            (then (return (i32.const 1) (local.get $lo) (i64.const 0)))
        )

        ;; here we keep looping but with our defined mul and add instead of i64.mul and i64.add
        (loop $loop_big
            (if (i64.lt_u (local.tee $loaded (i64.sub (i64.load8_u (local.get $offset)) (i64.const 48))) (i64.const 10))
                (then
                    (call $stdlib.add-int128
                      (call $stdlib.mul-int128 (local.get $lo) (local.get $hi) (i64.const 10) (i64.const 0))
                      (local.get $loaded) (i64.const 0)
                    )
                    (local.set $hi)
                    (local.set $lo)
                )
                (else
                    (return (i32.const 0) (i64.const 0) (i64.const 0))
                )
            )
            (local.set $offset (i32.add (local.get $offset) (i32.const 1)))
            ;; we branch while we still have digits and $result < (u128::MAX / 10)
            (br_if $loop_big
                (i32.and
                    (i32.ne (local.tee $len (i32.sub (local.get $len) (i32.const 1))) (i32.const 0))
                    (select
                        (i64.lt_u (local.get $lo) (i64.const -7378697629483820647))
                        (i64.lt_u (local.get $hi) (i64.const 1844674407370955161))
                        (i64.eq (local.get $hi) (i64.const 1844674407370955161))
                    )
                )
            )
        )
        ;; we have to return if we have no more digits, otherwise it means that we have
        ;; a result between (u128::MAX - 5)..u128::MAX or an overflow
        (if (result i32 i64 i64)
            (i32.eqz (local.get $len))
            (then (i32.const 1) (local.get $lo) (local.get $hi))
            (else
                (if (result i32 i64 i64)
                    (i64.le_u (local.tee $loaded (i64.sub (i64.load8_u (local.get $offset)) (i64.const 48))) (i64.const 5))
                    (then (i32.const 1) (i64.add (i64.const -6) (local.get $loaded)) (i64.const -1))
                    (else (i32.const 0) (i64.const 0) (i64.const 0))
                )
            )
        )
    )

    (func $stdlib.utf8-to-uint (param $offset i32) (param $len i32) (result i32 i64 i64)
        (local $lo i64) (local $hi i64) (local $loaded i64)
        ;; a string is automatically invalid if its size is 0 or
        ;; bigger than 39 (*4 bytes), the max number of digits of a u128
        (if (i32.lt_u (i32.sub (local.get $len) (i32.const 157)) (i32.const -156))
            (then (return (i32.const 0) (i64.const 0) (i64.const 0)))
        )

        ;; loop with simple multiplication, for speed
        (loop $loop_small
            ;; valid digit: 24 first bits are 0 and rest is valid ascii char
            (i32.and
                (i64.eqz (i64.and (local.tee $loaded (i64.load32_u (local.get $offset))) (i64.const 0xffffff)))
                (i64.lt_u (local.tee $loaded (i64.sub (i64.shr_u (local.get $loaded) (i64.const 24)) (i64.const 48))) (i64.const 10))
            )
            ;; if next digit is valid, $lo * 10 + digit, otherwise we return none
            (if
                (then (local.set $lo (i64.add (i64.mul (local.get $lo) (i64.const 10)) (local.get $loaded))))
                (else (return (i32.const 0) (i64.const 0) (i64.const 0)))
            )
            (local.set $offset (i32.add (local.get $offset) (i32.const 4)))
            ;; we branch while we still have digits to add and $lo < (u64::MAX / 10)
            (br_if $loop_small
                (i32.and
                    (i32.ne (local.tee $len (i32.sub (local.get $len) (i32.const 4))) (i32.const 0))
                    (i64.lt_u (local.get $lo) (i64.const 1844674407370955161))
                )
            )
        )

        ;; we return if no more digits
        (if (i32.eqz (local.get $len))
            (then (return (i32.const 1) (local.get $lo) (i64.const 0)))
        )

        ;; here we keep looping but with our defined mul and add instead of i64.mul and i64.add
        (loop $loop_big
            (i32.and
                (i64.eqz (i64.and (local.tee $loaded (i64.load32_u (local.get $offset))) (i64.const 0xffffff)))
                (i64.lt_u (local.tee $loaded (i64.sub (i64.shr_u (local.get $loaded) (i64.const 24)) (i64.const 48))) (i64.const 10))
            )
            (if
                (then
                    (call $stdlib.add-int128
                      (call $stdlib.mul-int128 (local.get $lo) (local.get $hi) (i64.const 10) (i64.const 0))
                      (local.get $loaded) (i64.const 0)
                    )
                    (local.set $hi)
                    (local.set $lo)
                )
                (else (return (i32.const 0) (i64.const 0) (i64.const 0)))
            )
            (local.set $offset (i32.add (local.get $offset) (i32.const 4)))
            ;; we branch while we still have digits and $result < (u128::MAX / 10)
            (br_if $loop_big
                (i32.and
                    (i32.ne (local.tee $len (i32.sub (local.get $len) (i32.const 4))) (i32.const 0))
                    (select
                        (i64.lt_u (local.get $lo) (i64.const -7378697629483820647))
                        (i64.lt_u (local.get $hi) (i64.const 1844674407370955161))
                        (i64.eq (local.get $hi) (i64.const 1844674407370955161))
                    )
                )
            )
        )
        ;; we have to return if we have no more digits, otherwise it means that we have
        ;; a result between (u128::MAX - 5)..u128::MAX or an overflow
        (if (result i32 i64 i64)
            (i32.eqz (local.get $len))
            (then (i32.const 1) (local.get $lo) (local.get $hi))
            (else
                (i32.and
                    (i64.eqz (i64.and (local.tee $loaded (i64.load32_u (local.get $offset))) (i64.const 0xffffff)))
                    (i64.le_u (local.tee $loaded (i64.sub (i64.shr_u (local.get $loaded) (i64.const 24)) (i64.const 48))) (i64.const 5))
                )
                (if (result i32 i64 i64)
                    (then (i32.const 1) (i64.add (i64.const -6) (local.get $loaded)) (i64.const -1))
                    (else (i32.const 0) (i64.const 0) (i64.const 0))
                )
            )
        )
    )

    (func $stdlib.string-to-int (param $offset i32) (param $len i32) (result i32 i64 i64)
        (local $neg i32) (local $lo i64) (local $hi i64)

        ;; Save in neg if the number starts with "-"
        (local.set $neg (i32.eq (i32.load8_u (local.get $offset)) (i32.const 45)))

        (call $stdlib.string-to-uint
            (i32.add (local.get $offset) (local.get $neg))
            (i32.sub (local.get $len) (local.get $neg))
        )
        (local.set $hi)
        (local.set $lo)

        ;; edge case i127::MIN
        (if (i32.and (local.get $neg) (i32.and (i64.eqz (local.get $lo)) (i64.eq (local.get $hi) (i64.const -9223372036854775808))))
            (then
                (i32.const 1)
                (i64.const 0)
                (i64.const -9223372036854775808)
                return
            )
        )

        ;; if result is none or $hi < 0 (number too big to be a i128), return none
        i32.eqz ;; is-none
        (if (i32.or (i64.lt_s (local.get $hi) (i64.const 0)))
            (then (return (i32.const 0) (i64.const 0) (i64.const 0)))
        )

        ;; result is some
        (i32.const 1)

        ;; if !neg { current_result } else { -current_result }
        (if (result i64 i64)
            (i32.eqz (local.get $neg))
            (then (local.get $lo) (local.get $hi))
            (else
                (i64.sub (i64.const 0) (local.get $lo))
                (i64.sub (i64.const 0) (i64.add (local.get $hi) (i64.extend_i32_u (i64.ne (local.get $lo) (i64.const 0)))))
            )
        )
    )

    (func $stdlib.utf8-to-int (param $offset i32) (param $len i32) (result i32 i64 i64)
        (local $neg i32) (local $lo i64) (local $hi i64)

        ;; Save in neg if the number starts with "-" (as 4 for the number of bytes)
        (local.set $neg (i32.shl (i32.eq (i32.load (local.get $offset)) (i32.const 754974720)) (i32.const 2)))

        (call $stdlib.utf8-to-uint
            (i32.add (local.get $offset) (local.get $neg))
            (i32.sub (local.get $len) (local.get $neg))
        )
        (local.set $hi)
        (local.set $lo)

        ;; edge case i127::MIN
        (if (i32.and (i32.ne (local.get $neg) (i32.const 0)) (i32.and (i64.eqz (local.get $lo)) (i64.eq (local.get $hi) (i64.const -9223372036854775808))))
            (then
                (i32.const 1)
                (i64.const 0)
                (i64.const -9223372036854775808)
                return
            )
        )

        ;; if result is none or $hi < 0 (number too big to be a i128), return none
        i32.eqz ;; is-none
        (if (i32.or (i64.lt_s (local.get $hi) (i64.const 0)))
            (then (return (i32.const 0) (i64.const 0) (i64.const 0)))
        )

        ;; result is some
        (i32.const 1)

        ;; if !neg { current_result } else { -current_result }
        (if (result i64 i64)
            (i32.eqz (local.get $neg))
            (then (local.get $lo) (local.get $hi))
            (else
                (i64.sub (i64.const 0) (local.get $lo))
                (i64.sub (i64.const 0) (i64.add (local.get $hi) (i64.extend_i32_u (i64.ne (local.get $lo) (i64.const 0)))))
            )
        )
    )

    (func $stdlib.uint-to-string (param $lo i64) (param $hi i64) (param $result_offset i32) (result i32 i32)
        (local $i i32) (local $j i32)
        (local.set $j (local.tee $i (local.get $result_offset)))

        ;; slow loop while $hi > 0
        (if (i64.ne (local.get $hi) (i64.const 0))
            (then
                (loop $loop
                    (call $stdlib.div-int128 (local.get $lo) (local.get $hi) (i64.const 10) (i64.const 0))
                    ;; remainder on the stack
                    drop ;; drop remainder_hi
                    (local.set $lo (i64.add (i64.const 48))) ;; to ascii
                    (i64.store8 (local.get $i) (local.get $lo))

                    ;; quotient on the stack
                    (local.set $hi)
                    (local.set $lo)

                    (local.set $i (i32.add (local.get $i) (i32.const 1)))
                    (br_if $loop (i64.ne (local.get $hi) (i64.const 0)))
                )
            )
        )

        ;; faster loop while $lo > 0 (or at least once in case the number was 0)
        (loop $loop
            (local.get $i)

            ;; divmod(n, 10) => div = n / 10, mod = (div * -10) + n
            (i64.add
                (local.get $lo)
                (i64.mul
                    (local.tee $lo (i64.div_u (local.get $lo) (i64.const 10)))
                    (i64.const -10)
                )
            )
            ;; to ascii
            (i64.add (i64.const 48))

            i64.store8

            (local.set $i (i32.add (local.get $i) (i32.const 1)))
            (br_if $loop (i64.ne (local.get $lo) (i64.const 0)))
        )

        ;; final result offset and length on the stack
        (local.get $j)
        (i32.sub (local.get $i) (local.get $j))
        ;; update result_offset
        (local.set $result_offset (local.get $i))

        ;; reverse answer in memory
        (local.set $i (i32.sub (local.get $i) (i32.const 1)))
        (loop $loop
            (local.get $j)
            (i32.load8_u (local.get $i))

            (local.get $i)
            (i32.load8_u (local.get $j))

            i32.store8
            i32.store8

            (br_if $loop
                (i32.lt_u
                    (local.tee $j (i32.add (local.get $j) (i32.const 1)))
                    (local.tee $i (i32.sub (local.get $i) (i32.const 1)))
                )
            )
        )

        ;; final result is already on the stack
    )

    (func $stdlib.int-to-string (param $lo i64) (param $hi i64) (param $result_offset i32) (result i32 i32)
        (local $negative i32) (local $len i32)
        (local.set $negative (i64.lt_s (local.get $hi) (i64.const 0)))
        ;; add a '-' if n < 0
        (if (local.get $negative)
            (then
                (i32.store8 (local.get $result_offset) (i32.const 45))
                (local.set $result_offset (i32.add (local.get $result_offset) (i32.const 1)))
            )
        )

        ;; if (n >= 0 or n == i128::MIN) { uint-to-string(n) } else { uint-to-string(-n) }
        (if (result i32 i32)
            (select
                (i64.eqz (local.get $lo))
                (i64.ge_s (local.get $hi) (i64.const 0))
                (i64.eq (local.get $hi) (i64.const 0x8000000000000000))
            )
            (then (call $stdlib.uint-to-string (local.get $lo) (local.get $hi) (local.get $result_offset)))
            (else
                (call $stdlib.uint-to-string
                    (i64.sub (i64.const 0) (local.get $lo))
                    (i64.sub (i64.const 0) (i64.add (local.get $hi) (i64.extend_i32_u (i64.ne (local.get $lo) (i64.const 0)))))
                    (local.get $result_offset)
                )
            )
        )

        ;; we adjust offset and length to account for the '-'
        ;; we save the length to pop it from the stack and so that we can update the offset
        ;; and return it in the right order after the offset
        (local.set $len (i32.add (local.get $negative)))
        (i32.sub (local.get $negative))
        (local.get $len)
    )

    (func $stdlib.uint-to-utf8 (param $lo i64) (param $hi i64) (param $result_offset i32) (result i32 i32)
        (local $i i32) (local $j i32)
        (local.set $j (local.tee $i (local.get $result_offset)))

        ;; slow loop while $hi > 0
        (if (i64.ne (local.get $hi) (i64.const 0))
            (then
                (loop $loop
                    (call $stdlib.div-int128 (local.get $lo) (local.get $hi) (i64.const 10) (i64.const 0))
                    ;; remainder on the stack
                    drop ;; drop remainder_hi
                    (local.set $lo (i64.add (i64.const 48))) ;; to ascii
                    ;; store as 4 bytes in big-endian
                    (i64.store32 (local.get $i) (i64.shl (local.get $lo) (i64.const 24)))

                    ;; quotient on the stack
                    (local.set $hi)
                    (local.set $lo)

                    (local.set $i (i32.add (local.get $i) (i32.const 4)))
                    (br_if $loop (i64.ne (local.get $hi) (i64.const 0)))
                )
            )
        )

        ;; faster loop while $lo > 0 (or at least once in case the number was 0)
        (loop $loop
            (local.get $i)

            ;; divmod(n, 10) => div = n / 10, mod = (div * -10) + n
            (i64.add
                (local.get $lo)
                (i64.mul
                    (local.tee $lo (i64.div_u (local.get $lo) (i64.const 10)))
                    (i64.const -10)
                )
            )
            ;; to ascii
            (i64.add (i64.const 48))
            ;; to be on 4 bytes
            (i64.shl (i64.const 24))

            i64.store32

            (local.set $i (i32.add (local.get $i) (i32.const 4)))
            (br_if $loop (i64.ne (local.get $lo) (i64.const 0)))
        )

        ;; final result offset and length on the stack
        (local.get $j)
        (i32.sub (local.get $i) (local.get $j))
        ;; update result_offset
        (local.set $result_offset (local.get $i))

        ;; reverse answer in memory
        (local.set $i (i32.sub (local.get $i) (i32.const 4)))
        (loop $loop
            (local.get $j)
            (i32.load (local.get $i))

            (local.get $i)
            (i32.load (local.get $j))

            i32.store
            i32.store

            (br_if $loop
                (i32.lt_u
                    (local.tee $j (i32.add (local.get $j) (i32.const 4)))
                    (local.tee $i (i32.sub (local.get $i) (i32.const 4)))
                )
            )
        )

        ;; final result is already on the stack
    )

    (func $stdlib.int-to-utf8 (param $lo i64) (param $hi i64) (param $result_offset i32) (result i32 i32)
        (local $negative i32) (local $len i32)
        (local.set $negative (i32.shl (i64.lt_s (local.get $hi) (i64.const 0)) (i32.const 2)))
        ;; add a '-' if n < 0
        (if (local.get $negative)
            (then
                ;; store "-" in big-endian
                (i32.store (local.get $result_offset) (i32.const 754974720))
                (local.set $result_offset (i32.add (local.get $result_offset) (i32.const 4)))
            )
        )

        ;; if (n >= 0 or n == i128::MIN) { uint-to-utf8(n) } else { uint-to-utf8(-n) }
        (if (result i32 i32)
            (select
                (i64.eqz (local.get $lo))
                (i64.ge_s (local.get $hi) (i64.const 0))
                (i64.eq (local.get $hi) (i64.const 0x8000000000000000))
            )
            (then (call $stdlib.uint-to-utf8 (local.get $lo) (local.get $hi) (local.get $result_offset)))
            (else
                (call $stdlib.uint-to-utf8
                    (i64.sub (i64.const 0) (local.get $lo))
                    (i64.sub (i64.const 0) (i64.add (local.get $hi) (i64.extend_i32_u (i64.ne (local.get $lo) (i64.const 0)))))
                    (local.get $result_offset)
                )
            )
        )

        ;; we adjust offset and length to account for the '-'
        ;; we save the length to pop it from the stack and so that we can update the offset
        ;; and return it in the right order after the offset
        (local.set $len (i32.add (local.get $negative)))
        (i32.sub (local.get $negative))
        (local.get $len)
    )

    ;;
    ;; -- 'to-uint' implementation
    ;;
    ;; Should raise a runtime error
    ;; if the argument is < 0.
    ;;
    (func $stdlib.to-uint (param $lo i64) (param $hi i64) (result i64 i64)
        (if (i64.lt_s (local.get $hi) (i64.const 0))
            (then (call $stdlib.runtime-error (i32.const 1)))
        )
        (local.get $lo)
        (local.get $hi)
    )

    ;;
    ;; -- 'to-int' implementation
    ;;
    ;; Should raise a runtime error
    ;; if the argument is >= 2^127.
    ;;
    (func $stdlib.to-int (param $lo i64) (param $hi i64) (result i64 i64)
        ;; 9223372036854775808 -> 2^63
        ;; 2^63 is one more than the maximum positive value
        ;; that can be represented by a signed 64-bit integer.
        ;; Thus, if $hi >= 2^63 the argument is >= 2^127,
        ;; no matter what is present in $lo.
        (if (i64.ge_u (local.get $hi) (i64.const 9223372036854775808))
            (then (call $stdlib.runtime-error (i32.const 0)))
        )
        (local.get $lo)
        (local.get $hi)
    )

    (func $stdlib.sha512-buf (param $offset i32) (param $length i32) (param $offset-result i32) (param $workspace-offset i32)(result i32 i32)

        ;; For binary representation, you can take a look at https://sha256algorithm.com/
        ;; Keep in mind that SHA-256 handles 4-byte words, but SHA-512 handles 8-byte words
        ;; SHA-256 block is of 512-bits(64 bytes) but SHA-512 block is of 1024-bits(128 bytes)
        ;; For initial values, constants and high level understanding of SHA-512, please take a look at this rust implementation
        ;; https://github.com/dandyvica/sha/blob/master/src/sha512.rs
        ;; If you're interested in the paper, please take a look at https://eprint.iacr.org/2010/548.pdf

        ;; Length of the data after adding padding and length to it
        (local $length_after_padding i32)
        ;; Index to track all blocks
        (local $index i32)

        (call $pad-sha512-data (local.get $offset) (local.get $length) (local.get $workspace-offset))
        (local.set $length_after_padding)

        (local.set $index (i32.const 0))
        ;; Iterations on blocks
        (loop
            ;; Process a block
            (call $process-sha512-block (local.get $index) (local.get $workspace-offset))
            ;; Calculate hash using initial values and k-constants (80 rounds total)
            (call $calculate-sha512 (local.get $workspace-offset))

            (br_if 0
                (i32.lt_u
                    (local.tee $index (i32.add (local.get $index) (i32.const 128)))
                    (local.get $length_after_padding)
                )
            )
        )

        ;; store at result position with correct endianness
        (call $store-calculated-sha512 (local.get $offset-result) (local.get $workspace-offset))
        (local.get $offset-result) (i32.const 64)
    )

    (func $stdlib.sha512-int (param $lo i64) (param $hi i64) (param $offset-result i32) (param $workspace-offset i32)(result i32 i32)

        ;; Copy data to the working stack, so that it has this relative configuration:
        ;;   0..64 -> Initial hash vals (will be the result hash in the end)
        ;;   64..704 -> Space to store W
        ;;   704..831 -> extended int
        (memory.copy (local.get $workspace-offset) (i32.const 648) (i32.const 64))
        (i64.store offset=704 (local.get $workspace-offset) (local.get $lo))
        (i64.store offset=712 (local.get $workspace-offset) (local.get $hi)) ;; offset = 704 + 8
        (i32.store offset=720 (local.get $workspace-offset) (i32.const 0x80)) ;; offset = 704 + 16
        (memory.fill (i32.add (local.get $workspace-offset) (i32.const 724)) (i32.const 0) (i32.const 110)) ;; offset = 704+20
        (i32.store8 offset=831 (local.get $workspace-offset) (i32.const 0x80)) ;; offset = 704+127

        (call $process-sha512-block (i32.const 0) (local.get $workspace-offset))
        (call $calculate-sha512 (local.get $workspace-offset))

        ;; store at result position with correct endianness
        (call $store-calculated-sha512 (local.get $offset-result) (local.get $workspace-offset))

        (local.get $offset-result) (i32.const 64)
    )

    (func $pad-sha512-data (param $offset i32) (param $length i32) (param $workspace-offset i32) (result i32)
        ;; Length of the data after adding padding and length to it
        (local $length_after_padding i32)

        ;; Message length in 8 bytes
        (local $message_length_64 i64)

        ;; Copying initial values (64 bytes) for SHA-512 from 648 index
        (memory.copy (local.get $workspace-offset) (i32.const 648) (i32.const 64))

        ;; Copying the data from the offset to isolated environment (i.e. target-index = $workspace-offset+(initial-values+(80 rounds * 8)))
        (memory.copy (i32.add (local.get $workspace-offset) (i32.const 704)) (local.get $offset) (local.get $length))

        (local.set $length_after_padding ;; total size of data with expansion divisible by 128
            (i32.add
                (i32.or
                    ;; len + 16 bytes for the size
                    (i32.add (local.get $length) (i32.const 16))
                    (i32.const 0x7f)
                )
                (i32.const 1)
            )
        )

        ;; Add "1" at the end of the data
        (i32.store offset=704
            (i32.add (local.get $workspace-offset) (local.get $length))
            (i32.const 0x80)
        )

        ;; Fill the remaining part before the size with 0s
        (memory.fill
                (i32.add (i32.add (local.get $workspace-offset) (local.get $length)) (i32.const 705))
                (i32.const 0)
                ;; Leave the last 8 bytes for the length
                ;; Not handling 16 bytes length here
                (i32.sub (i32.sub (local.get $length_after_padding) (local.get $length)) (i32.const 8))
        )

        ;; Add the length, as a 64bits big-endian integer
        (local.set $message_length_64 (i64.extend_i32_u (i32.shl (local.get $length) (i32.const 3))))

        ;; Length is being handled as i64 (8 bytes), because we don't need to handle it in 16 bytes, it will be complex
        ;; This is the location where reversed length is going to be stored
        (i32.sub (i32.add (local.get $workspace-offset) (local.get $length_after_padding)) (i32.const 8))

        ;; i64.store values in little-endian format, so to convert the length to big-endian, we need to reverse the 8 bits of length
        (i64.or
                (i64.or
                    (i64.or
                        (i64.shl (local.get $message_length_64) (i64.const 0x38))
                        (i64.shl (i64.and (local.get $message_length_64) (i64.const 0xff00)) (i64.const 0x28))
                    )
                    (i64.or
                        (i64.shl (i64.and (local.get $message_length_64) (i64.const 0xff0000)) (i64.const 0x18))
                        (i64.shl (i64.and (local.get $message_length_64) (i64.const 0xff000000)) (i64.const 0x8))
                    )
                )
                (i64.or
                    (i64.or
                        (i64.and (i64.shr_u (local.get $message_length_64) (i64.const 0x8)) (i64.const 0xff000000))
                        (i64.and (i64.shr_u (local.get $message_length_64) (i64.const 0x18)) (i64.const 0xff0000))
                    )
                    (i64.or
                        (i64.and (i64.shr_u (local.get $message_length_64) (i64.const 0x28)) (i64.const 0xff00))
                        (i64.shr_u (local.get $message_length_64) (i64.const 0x38))
                    )
                )
        )
        i64.store offset=704

        (local.get $length_after_padding)

    )

    (func $process-sha512-block (param $current-block-index i32) (param $workspace-offset i32)
        ;; Basically is the $workspace-offset
        (local $origin i32)

        ;; Temporary block data, in an iteration
        (local $temp-block-data i32)

        ;; Temporary block data (a word of 8 bytes) in current block iteration
        (local $block-iteration-temp i64)

        (local $index i32)

        (local.set $origin (local.get $workspace-offset))
        (local.set $temp-block-data (i32.add (local.get $origin) (local.get $current-block-index)))

        (local.set $index (i32.const 0))
        ;; Reverse each word in the block (8 bytes for sha-512) to convert it to little-endian format
        (loop
            (i32.add (local.get $origin) (local.get $index))
            (i8x16.swizzle
                (v128.load offset=704 (i32.add (local.get $temp-block-data) (local.get $index)))
                (v128.const i8x16 7 6 5 4 3 2 1 0 15 14 13 12 11 10 9 8)
            )
            v128.store offset=64

            (br_if 0
                (i32.lt_u
                    (local.tee $index (i32.add (local.get $index) (i32.const 16)))
                    (i32.const 128)
                )
            )
        )

        (local.set $index (i32.const 0))
        (loop
            (local.set $temp-block-data (i32.add (local.get $origin) (local.get $index)))
            ;; Location to store the calculated word in current iteration (current-word + 16)
            (i32.add (local.get $temp-block-data) (i32.const 128))
            ;; w(current)
            (i64.load offset=64 (local.get $temp-block-data))
            ;; sigma 0
            (local.set $block-iteration-temp (i64.load offset=72 (local.get $temp-block-data))) ;; offset (w+1) = 64 + 8
            (i64.rotr (local.get $block-iteration-temp) (i64.const 1))
            (i64.xor (i64.rotr (local.get $block-iteration-temp) (i64.const 8)))
            (i64.xor (i64.shr_u (local.get $block-iteration-temp) (i64.const 7)))
            i64.add
            ;; w(current+9)
            (i64.add (i64.load offset=136 (local.get $temp-block-data))) ;; offset = 64+72
            ;; sigma 1
            (local.set $block-iteration-temp (i64.load offset=176 (local.get $temp-block-data))) ;; offset = 64 + 112 w(current+14)
            (i64.rotr (local.get $block-iteration-temp) (i64.const 19))
            (i64.xor (i64.rotr (local.get $block-iteration-temp) (i64.const 61)))
            (i64.xor (i64.shr_u (local.get $block-iteration-temp) (i64.const 6)))
            i64.add
            ;; save
            i64.store offset=64

            (br_if 0
                (i32.lt_u
                    (local.tee $index (i32.add (local.get $index) (i32.const 8)))
                    (i32.const 512)
                )
            )
        )
    )

    (func $calculate-sha512 (param $workspace-offset i32)

        (local $origin i32)
        (local $index i32)

        ;; Variables used in hash rounds
        (local $a i64) (local $b i64) (local $c i64) (local $d i64)
        (local $e i64) (local $f i64) (local $g i64) (local $h i64)
        (local $temp1 i64) (local $temp2 i64)

        (local.set $origin (local.get $workspace-offset))

        ;; Calculating variables
        (local.set $a (i64.load offset=0 (local.get $origin)))
        (local.set $b (i64.load offset=8 (local.get $origin)))
        (local.set $c (i64.load offset=16 (local.get $origin)))
        (local.set $d (i64.load offset=24 (local.get $origin)))
        (local.set $e (i64.load offset=32 (local.get $origin)))
        (local.set $f (i64.load offset=40 (local.get $origin)))
        (local.set $g (i64.load offset=48 (local.get $origin)))
        (local.set $h (i64.load offset=56 (local.get $origin)))

        (local.set $index (i32.const 0))

        (loop
            ;; compute $temp1: h + sigma1 + choice + k0 + w0
            (local.get $h) ;; h

            (i64.rotr (local.get $e) (i64.const 14))
            (i64.xor (i64.rotr (local.get $e) (i64.const 18)))
            (i64.xor (i64.rotr (local.get $e) (i64.const 41)))
            i64.add ;; + sigma1

            (i64.and (local.get $e) (local.get $f))
            (i64.xor (i64.and (i64.xor (local.get $e) (i64.const -1)) (local.get $g)))
            i64.add ;; + choice

            (i64.add (i64.load offset=712 (local.get $index))) ;; + k(current)

            (i64.add (i64.load offset=64 (i32.add (local.get $origin) (local.get $index)))) ;; + w(current)

            (local.set $temp1)

            ;; compute temp2: sigma0 + majority
            (i64.rotr (local.get $a) (i64.const 28))
            (i64.xor (i64.rotr (local.get $a) (i64.const 34)))
            (i64.xor (i64.rotr (local.get $a) (i64.const 39))) ;; sigma0

            (i64.and (local.get $a) (local.get $b))
            (i64.xor (i64.and (local.get $a) (local.get $c)))
            (i64.xor (i64.and (local.get $b) (local.get $c)))
            i64.add ;; + majority

            (local.set $temp2)

            ;; assign new variables
            (local.set $h (local.get $g))
            (local.set $g (local.get $f))
            (local.set $f (local.get $e))
            (local.set $e (i64.add (local.get $d) (local.get $temp1)))
            (local.set $d (local.get $c))
            (local.set $c (local.get $b))
            (local.set $b (local.get $a))
            (local.set $a (i64.add (local.get $temp1) (local.get $temp2)))

            (br_if 0
                (i32.lt_u
                    (local.tee $index (i32.add (local.get $index) (i32.const 8)))
                    (i32.const 640)
                )
            )
        )

        ;; update hash
        (i64.store offset=0 (local.get $origin) (i64.add (i64.load offset=0 (local.get $origin)) (local.get $a)))
        (i64.store offset=8 (local.get $origin) (i64.add (i64.load offset=8 (local.get $origin)) (local.get $b)))
        (i64.store offset=16 (local.get $origin) (i64.add (i64.load offset=16 (local.get $origin)) (local.get $c)))
        (i64.store offset=24 (local.get $origin) (i64.add (i64.load offset=24 (local.get $origin)) (local.get $d)))
        (i64.store offset=32 (local.get $origin) (i64.add (i64.load offset=32 (local.get $origin)) (local.get $e)))
        (i64.store offset=40 (local.get $origin) (i64.add (i64.load offset=40 (local.get $origin)) (local.get $f)))
        (i64.store offset=48 (local.get $origin) (i64.add (i64.load offset=48 (local.get $origin)) (local.get $g)))
        (i64.store offset=56 (local.get $origin) (i64.add (i64.load offset=56 (local.get $origin)) (local.get $h)))
    )

    (func $store-calculated-sha512 (param $offset-result i32) (param $workspace-offset i32)
        (v128.store
            (local.get $offset-result)
            (i8x16.swizzle
                (v128.load (local.get $workspace-offset))
                (v128.const i8x16 7 6 5 4 3 2 1 0 15 14 13 12 11 10 9 8)
            )
        )
        (v128.store offset=16
            (local.get $offset-result)
            (i8x16.swizzle
                (v128.load offset=16 (local.get $workspace-offset))
                (v128.const i8x16 7 6 5 4 3 2 1 0 15 14 13 12 11 10 9 8)
            )
        )
        (v128.store offset=32
            (local.get $offset-result)
            (i8x16.swizzle
                (v128.load offset=32 (local.get $workspace-offset))
                (v128.const i8x16 7 6 5 4 3 2 1 0 15 14 13 12 11 10 9 8)
            )
        )
        (v128.store offset=48
            (local.get $offset-result)
            (i8x16.swizzle
                (v128.load offset=48 (local.get $workspace-offset))
                (v128.const i8x16 7 6 5 4 3 2 1 0 15 14 13 12 11 10 9 8)
            )
        )
    )

    ;; Converts a span of 4-byte unicode scalar values into UTF-8.
    ;; The input bytes are assumed to be composed of valid unicode scalar values.
    ;; Do not call this function with arbitrary bytes.
    (func $stdlib.convert-scalars-to-utf8 (param $offset i32) (param $length i32) (param $output-offset i32) (result i32)
        (local $i i32)       ;; Loop counter
        (local $initial-output-offset i32)
        (local $scalar i32)  ;; Scalar value
        (local $byte1 i32)   ;; Byte variables for UTF-8 encoding
        (local $byte2 i32)
        (local $byte3 i32)
        (local $byte4 i32)

        ;; Store the initial value of $output-offset
        (local.set $initial-output-offset (local.get $output-offset))

        ;; Initialize loop counter
        (local.set $i (i32.const 0))

        ;; Check if the length is zero to avoid unnecessary processing
        (if (i32.eqz (local.get $length))
            (then
                (i32.const 0)  ;; Push 0 as the return value
                (return)       ;; Return with two values on the stack
            )
        )

        (loop $loop
            ;; Load the scalar value from the array and convert to big-endian
            (local.set $scalar (i32.load (i32.add (local.get $offset) (local.get $i))))

            ;; Big-endian conversion (if necessary)
            (local.set $scalar
                (i32.or
                    (i32.shl (i32.and (local.get $scalar) (i32.const 0xFF)) (i32.const 24))
                    (i32.or
                        (i32.shl (i32.and (local.get $scalar) (i32.const 0xFF00)) (i32.const 8))
                        (i32.or
                            (i32.shr_u (i32.and (local.get $scalar) (i32.const 0xFF0000)) (i32.const 8))
                            (i32.shr_u (local.get $scalar) (i32.const 24))
                        )
                    )
                )
            )

            ;; UTF-8 encoding

            ;; block 1
            (if (i32.lt_u (local.get $scalar) (i32.const 0x80))
                (then
                    ;; 1-byte sequence: 0xxxxxxx
                    (i32.store8 (local.get $output-offset) (local.get $scalar))
                    (local.set $output-offset (i32.add (local.get $output-offset) (i32.const 1)))
                )
                (else
                    ;; block 2
                    (if (i32.lt_u (local.get $scalar) (i32.const 0x800))
                        (then
                            ;; 2-byte sequence: 110xxxxx 10xxxxxx
                            (local.set $byte1
                                (i32.or (i32.const 0xC0) (i32.shr_u (local.get $scalar) (i32.const 6)))
                            )
                            (local.set $byte2
                                (i32.or (i32.const 0x80) (i32.and (local.get $scalar) (i32.const 0x3F)))
                            )
                            (i32.store8 (local.get $output-offset) (local.get $byte1))
                            (local.set $output-offset (i32.add (local.get $output-offset) (i32.const 1)))
                            (i32.store8 (local.get $output-offset) (local.get $byte2))
                            (local.set $output-offset (i32.add (local.get $output-offset) (i32.const 1)))
                        )
                        (else
                            ;; block 3
                            (if (i32.lt_u (local.get $scalar) (i32.const 0x10000))
                                (then
                                    ;; 3-byte sequence: 1110xxxx 10xxxxxx 10xxxxxx
                                    (local.set $byte1
                                        (i32.or (i32.const 0xE0) (i32.shr_u (local.get $scalar) (i32.const 12)))
                                    )
                                    (local.set $byte2
                                        (i32.or (i32.const 0x80) (i32.and (i32.shr_u (local.get $scalar) (i32.const 6)) (i32.const 0x3F)))
                                    )
                                    (local.set $byte3
                                        (i32.or (i32.const 0x80) (i32.and (local.get $scalar) (i32.const 0x3F)))
                                    )
                                    (i32.store8 (local.get $output-offset) (local.get $byte1))
                                    (local.set $output-offset (i32.add (local.get $output-offset) (i32.const 1)))
                                    (i32.store8 (local.get $output-offset) (local.get $byte2))
                                    (local.set $output-offset (i32.add (local.get $output-offset) (i32.const 1)))
                                    (i32.store8 (local.get $output-offset) (local.get $byte3))
                                    (local.set $output-offset (i32.add (local.get $output-offset) (i32.const 1)))
                                )
                                (else
                                    ;; block 4
                                    (if (i32.lt_u (local.get $scalar) (i32.const 0x110000))
                                        (then
                                            ;; 4-byte sequence: 11110xxx 10xxxxxx 10xxxxxx 10xxxxxx
                                            (local.set $byte1
                                                (i32.or (i32.const 0xF0) (i32.shr_u (local.get $scalar) (i32.const 18)))
                                            )
                                            (local.set $byte2
                                                (i32.or (i32.const 0x80) (i32.and (i32.shr_u (local.get $scalar) (i32.const 12)) (i32.const 0x3F)))
                                            )
                                            (local.set $byte3
                                                (i32.or (i32.const 0x80) (i32.and (i32.shr_u (local.get $scalar) (i32.const 6)) (i32.const 0x3F)))
                                            )
                                            (local.set $byte4
                                                (i32.or (i32.const 0x80) (i32.and (local.get $scalar) (i32.const 0x3F)))
                                            )
                                            (i32.store8 (local.get $output-offset) (local.get $byte1))
                                            (local.set $output-offset (i32.add (local.get $output-offset) (i32.const 1)))
                                            (i32.store8 (local.get $output-offset) (local.get $byte2))
                                            (local.set $output-offset (i32.add (local.get $output-offset) (i32.const 1)))
                                            (i32.store8 (local.get $output-offset) (local.get $byte3))
                                            (local.set $output-offset (i32.add (local.get $output-offset) (i32.const 1)))
                                            (i32.store8 (local.get $output-offset) (local.get $byte4))
                                            (local.set $output-offset (i32.add (local.get $output-offset) (i32.const 1)))
                                        )
                                    )
                                )
                            )
                        )
                    )
                )
            )

            ;; Increment loop counter and continue loop
            (local.set $i (i32.add (local.get $i) (i32.const 4)))
            (br_if $loop (i32.lt_u (local.get $i) (local.get $length)))
        )

        ;; Calculate the length and push to stack
        (i32.sub (local.get $output-offset) (local.get $initial-output-offset))
    )

    ;; Validates that the bytes at the specified offset and length form a valid
    ;; Clarity string-ascii value.
    (func $stdlib.is-valid-string-ascii (param $offset i32) (param $length i32) (result i32)
        (local $char i32) (local $current_length i32)
        (loop $loop
            (if (local.tee $current_length (local.get $length))
                (then
                    (local.set $char (i32.load8_u (local.get $offset)))
                    (local.set $offset (i32.add (local.get $offset) (i32.const 1)))
                    (local.set $length (i32.sub (local.get $length) (i32.const 1)))
                    ;; keep looping if char is in [32..=126]
                    (br_if $loop (i32.lt_u (i32.sub (local.get $char) (i32.const 32)) (i32.const 95)))
                    ;; keep looping if char is in [\t, \n, \x0c, \r]
                    (br_if $loop
                        (i32.and
                            (i32.shr_u (i32.const 0x3600) (local.get $char))
                            (i32.lt_u (local.get $char) (i32.const 14))
                        )
                    )
                )
            )
        )
        (i32.eqz (local.get $current_length))
    )

    (func $stdlib.utf8-to-string-utf8
        ;; This function translates a utf-8 encoded string into our representation of string-utf8, which
        ;; is a sequence of unicode characters on 32 bits in big-endian
        ;; The utf-8 encoding process is well explained on wikipedia: https://en.wikipedia.org/wiki/UTF-8#Encoding
        (param $offset i32) (param $len i32) (param $output-offset i32) (param $max-len i32)
        (result i32 i32 i32)
        (local $scalar i32) (local $byte i32) (local $writeptr i32)

        ;; returns (some u"") if empty string
        (if (i32.eqz (local.get $len))
            (then (return (i32.const 1) (local.get $output-offset) (i32.const 0)))
        )

        ;; this will contain the offset at which we should write the next char
        (local.set $writeptr (local.get $output-offset))

        ;; each iteration of this loop tries to parse 1 char and writes the result to $writeptr
        (loop $chars-decode-loop
            ;; if we are in this loop, it means that we will parse another char, so we check that
            ;; adding a new char won't make the string longer than $max-len
            (if (i32.lt_s (local.tee $max-len (i32.sub (local.get $max-len) (i32.const 1))) (i32.const 0))
                (then (return (i32.const 0) (i32.const 0) (i32.const 0)))
            )
            ;; $scalar will contain the current char. for now we will parse the first byte
            (local.set $scalar (i32.load8_u (local.get $offset)))
            ;; utf8 on 1 byte is of the form [0b0xxxxxxx]
            (if (i32.lt_u (local.get $scalar) (i32.const 0x80))
                (then
                    ;; the next char to parse will be 1 byte further in $offset, and the remaining bytes are 1 less
                    (local.set $offset (i32.add (local.get $offset) (i32.const 1)))
                    (local.set $len (i32.sub (local.get $len) (i32.const 1)))
                )
                (else
                    ;; utf8 on 2 bytes is of the form [0b110xxxxx 0b10xxxxxx]
                    (if (i32.eq (i32.and (local.get $scalar) (i32.const 0xe0)) (i32.const 0xc0))
                        (then
                            ;; we shift the scalar so that we can add the next bits at the right position after
                            (local.set $scalar (i32.shl (i32.and (local.get $scalar) (i32.const 0x1f)) (i32.const 6)))
                            ;; reading and checking of the next byte
                            (local.set $byte (i32.load8_u offset=1 (local.get $offset)))
                            (if (i32.eq (i32.and (local.get $byte) (i32.const 0xc0)) (i32.const 0x80))
                                ;; if the 2nd byte is of the correct form, we use a mask to get the relevant bits and `or` it to $scalar
                                (then (local.set $scalar (i32.or (local.get $scalar) (i32.and (local.get $byte) (i32.const 0x3f)))))
                                (else (return (i32.const 0) (i32.const 0) (i32.const 0)))
                            )
                            ;; The result number cannot be < 0x80
                            (if (i32.lt_u (local.get $scalar) (i32.const 0x80))
                                (then (return (i32.const 0) (i32.const 0) (i32.const 0)))
                            )
                            ;; the next char to parse will be 2 bytes further in $offset, and the remaining bytes are 2 less
                            (local.set $offset (i32.add (local.get $offset) (i32.const 2)))
                            (local.set $len (i32.sub (local.get $len) (i32.const 2)))
                        )
                        (else
                            ;; utf8 on 3 bytes is of the form [0b1110xxxx 0b10xxxxxx 0b10xxxxxx]
                            (if (i32.eq (i32.and (local.get $scalar) (i32.const 0xf0)) (i32.const 0xe0))
                                (then
                                    ;; this will be the same principle as the 2-bytes case, but with 2 next bytes to parse
                                    (local.set $scalar (i32.shl (i32.and (local.get $scalar) (i32.const 0xf)) (i32.const 12)))
                                    (local.set $byte (i32.load8_u offset=1 (local.get $offset)))
                                    (if (i32.eq (i32.and (local.get $byte) (i32.const 0xc0)) (i32.const 0x80))
                                        (then (local.set $scalar (i32.or (local.get $scalar) (i32.shl (i32.and (local.get $byte) (i32.const 0x3f)) (i32.const 6)))))
                                        (else (return (i32.const 0) (i32.const 0) (i32.const 0)))
                                    )
                                    (local.set $byte (i32.load8_u offset=2 (local.get $offset)))
                                    (if (i32.eq (i32.and (local.get $byte) (i32.const 0xc0)) (i32.const 0x80))
                                        (then (local.set $scalar (i32.or (local.get $scalar) (i32.and (local.get $byte) (i32.const 0x3f)))))
                                        (else (return (i32.const 0) (i32.const 0) (i32.const 0)))
                                    )
                                    ;; The result number cannot be < 0x800, and cannot be surrogate [0xd800..=0xdfff]
                                    (if (i32.or
                                            (i32.eq (i32.and (local.get $scalar) (i32.const 0xfffff800)) (i32.const 0xd800))
                                            (i32.lt_u (local.get $scalar) (i32.const 0x800))
                                        )
                                        (then (return (i32.const 0) (i32.const 0) (i32.const 0)))
                                    )
                                    ;; the next char to parse will be 3 bytes further in $offset, and the remaining bytes are 3 less
                                    (local.set $offset (i32.add (local.get $offset) (i32.const 3)))
                                    (local.set $len (i32.sub (local.get $len) (i32.const 3)))
                                )
                                (else
                                    ;; utf8 on 4 bytes is of the form [0b11110xxx 0b10xxxxxx 0b10xxxxxx 0b10xxxxxx]
                                    (if (i32.eq (i32.and (local.get $scalar) (i32.const 0xf8)) (i32.const 0xf0))
                                        (then
                                            ;; this will be the same principle as the 2-bytes case, but with 3 next bytes to parse
                                            (local.set $scalar (i32.shl (i32.and (local.get $scalar) (i32.const 0x7)) (i32.const 18)))
                                            (local.set $byte (i32.load8_u offset=1 (local.get $offset)))
                                            (if (i32.eq (i32.and (local.get $byte) (i32.const 0xc0)) (i32.const 0x80))
                                                (then (local.set $scalar (i32.or (local.get $scalar) (i32.shl (i32.and (local.get $byte) (i32.const 0x3f)) (i32.const 12)))))
                                                (else (return (i32.const 0) (i32.const 0) (i32.const 0)))
                                            )
                                            (local.set $byte (i32.load8_u offset=2 (local.get $offset)))
                                            (if (i32.eq (i32.and (local.get $byte) (i32.const 0xc0)) (i32.const 0x80))
                                                (then (local.set $scalar (i32.or (local.get $scalar) (i32.shl (i32.and (local.get $byte) (i32.const 0x3f)) (i32.const 6)))))
                                                (else (return (i32.const 0) (i32.const 0) (i32.const 0)))
                                            )
                                            (local.set $byte (i32.load8_u offset=3 (local.get $offset)))
                                            (if (i32.eq (i32.and (local.get $byte) (i32.const 0xc0)) (i32.const 0x80))
                                                (then (local.set $scalar (i32.or (local.get $scalar) (i32.and (local.get $byte) (i32.const 0x3f)))))
                                                (else (return (i32.const 0) (i32.const 0) (i32.const 0)))
                                            )
                                            ;; this char should be in [U+10000 ..= U+10ffff]
                                            (if (i32.lt_u (i32.sub (local.get $scalar) (i32.const 0x110000)) (i32.const 0xfff00000))
                                                (then  (return (i32.const 0) (i32.const 0) (i32.const 0)))
                                            )
                                            ;; the next char to parse will be 3 bytes further in $offset, and the remaining bytes are 4 less
                                            (local.set $offset (i32.add (local.get $offset) (i32.const 4)))
                                            (local.set $len (i32.sub (local.get $len) (i32.const 4)))
                                        )
                                        ;; this case is when the current byte pattern does not match a utf-8 first byte
                                        (else (return (i32.const 0) (i32.const 0) (i32.const 0)))
                                    )
                                )
                            )
                        )
                    )
                )
            )
            ;; we store the read character in big endian
            (i32.store (local.get $writeptr)
                (i32.or
                    (i32.or
                        (i32.shl (local.get $scalar) (i32.const 24))
                        (i32.shl (i32.and (local.get $scalar) (i32.const 0xff00)) (i32.const 8))
                    )
                    (i32.or
                        (i32.and (i32.shr_u (local.get $scalar) (i32.const 8)) (i32.const 0xff00))
                        (i32.shr_u (local.get $scalar) (i32.const 24))
                    )
                )
            )
            ;; next character to write will be 4 bytes further
            (local.set $writeptr (i32.add (local.get $writeptr) (i32.const 4)))
            ;; we loop if there are still bytes to parse
            (br_if $chars-decode-loop (local.get $len))
        )

        ;; result is [some offset length]
        (i32.const 1) (local.get $output-offset) (i32.sub (local.get $writeptr) (local.get $output-offset))
    )

    (func $compare-clarity-names (param $offset_a i32) (param $len_a i32) (param $offset_b i32) (param $len_b i32) (result i32)
        ;; compare two clarity names and return -1 if a < b, 0 if a == b or 1 if a > b
        (local $min_len i32) (local $a i32) (local $b i32)

        (local.set $min_len (select (local.get $len_a) (local.get $len_b) (i32.lt_u (local.get $len_a) (local.get $len_b))))

        (loop $loop
            (if
                (i32.eq
                    (local.tee $a (i32.load8_u (local.get $offset_a)))
                    (local.tee $b (i32.load8_u (local.get $offset_b)))
                )
                (then
                    (local.set $offset_a (i32.add (local.get $offset_a) (i32.const 1)))
                    (local.set $offset_b (i32.add (local.get $offset_b) (i32.const 1)))
                    (br_if $loop (local.tee $min_len (i32.sub (local.get $min_len) (i32.const 1))))
                )
            )
        )

        (select
            (select (i32.const -1) (i32.ne (local.get $len_a) (local.get $len_b)) (i32.lt_u (local.get $len_a) (local.get $len_b)))
            (select (i32.const -1) (i32.ne (local.get $a) (local.get $b)) (i32.lt_u (local.get $a) (local.get $b)))
            (i32.eq (local.get $a) (local.get $b))
        )
    )

    (func $stdlib.bsearch-clarity-name (param $offset_list i32) (param $len_list i32) (param $offset_elem i32) (param $len_elem i32) (result i32)
        ;; find the index of a clarity name in a list with this format: [number of elem as u32, offset 1 u32, offset 2 u32,... , len 1 u8, len 2 u8, ..., item 1 [u8...], item 2 [u8...], ...]
        (local $size i32) (local $i i32) (local $j i32) (local $mid i32) (local $cmp i32) (local $offset_len i32)

        (local.set $j (local.tee $size (i32.load (local.get $offset_list))))
        (local.set $offset_list (i32.add (local.get $offset_list) (i32.const 4)))
        (local.set $offset_len (i32.add (local.get $offset_list) (i32.shl (local.get $size) (i32.const 2))))

        (loop $loop
            (local.set $mid (i32.add (local.get $i) (i32.shr_u (local.get $size) (i32.const 1))))

            (local.set $cmp
                (call $compare-clarity-names
                    (local.get $offset_elem)
                    (local.get $len_elem)
                    (i32.load (i32.add (local.get $offset_list) (i32.shl (local.get $mid) (i32.const 2))))
                    (i32.load8_u (i32.add (local.get $offset_len) (local.get $mid)))
                )
            )
            (if (i32.eqz (local.get $cmp))
                (then
                    (return (local.get $mid))
                )
            )
            (local.set $i
                (select
                    (local.get $i)
                    (i32.add (local.get $mid) (i32.const 1))
                    (i32.eq (local.get $cmp) (i32.const -1))
                )
            )
            (local.set $j
                (select
                    (local.get $j)
                    (local.get $mid)
                    (i32.eq (local.get $cmp) (i32.const 1))
                )
            )

            (local.set $size (i32.sub (local.get $j) (local.get $i)))
            (br_if $loop (i32.lt_u (local.get $i) (local.get $j)))
        )
        (i32.const -1)
    )

    (func $stdlib.skip-unknown-value (param $offset i32) (param $offset_end i32) (result i32)
        (local $id i32)
        (if (result i32)
            (i32.eq (local.get $offset) (local.get $offset_end))
            (then (local.get $offset))
            (else
                (if (i32.gt_u (local.tee $id (i32.load8_u (local.get $offset))) (i32.const 0xe))
                    (then (return (i32.const 0)))
                )
                (i32.add (local.get $offset) (i32.const 1))
                (local.get $offset_end)
                (call_indirect (type $skip-function) (i32.add (local.get $id) (i32.const 5)))
            )
        )
    )

    (func $skip-int128 (param $offset i32) (param $offset_end i32) (result i32)
        ;; nothing to check here, we should just make sure that 16 bytes further is <= offset_end
        (select
            (local.tee $offset (i32.add (local.get $offset) (i32.const 16)))
            (i32.const 0)
            (i32.le_u (local.get $offset) (local.get $offset_end))
        )
    )

    (func $skip-buffer (param $offset i32) (param $offset_end i32) (result i32)
        ;; read the size in the first 4 bytes, and skip that many bytes
        (local $size i32)
        (if (i32.gt_u (i32.add (local.get $offset) (i32.const 4)) (local.get $offset_end))
            (then (return (i32.const 0)))
        )
        (local.set $size (call $stdlib.load-i32-be (local.get $offset)))
        (select
            (local.tee $offset (i32.add (i32.add (local.get $offset) (i32.const 4)) (local.get $size)))
            (i32.const 0)
            (i32.le_u (local.get $offset) (local.get $offset_end))
        )
    )

    (func $skip-boolean-or-none (param $offset i32) (param $offset_end i32) (result i32)
        ;; nothing to do here
        (local.get $offset)
    )

    (func $skip-principal (param $offset i32) (param $offset_end i32) (result i32)
        ;; first byte <= 32, and skip 20 next bytes
        (if (result i32)
            (i32.ge_u
                (local.get $offset_end)
                (local.tee $offset_end (i32.add (local.get $offset) (i32.const 21)))
            )
            (then
                (select
                    (local.get $offset_end)
                    (i32.const 0)
                    (i32.le_u (i32.load8_u (local.get $offset)) (i32.const 32))
                )
            )
            (else (i32.const 0))
        )
    )

    (func $skip-contract (param $offset i32) (param $offset_end i32) (result i32)
        ;; we need to skip a principal, then a clarity name
        (if
            (i32.and
                (i32.ne
                    (local.tee $offset (call $skip-principal (local.get $offset) (local.get $offset_end)))
                    (i32.const 0)
                )
                (i32.gt_u (local.get $offset_end) (local.get $offset))
            )
            (then
                (if
                    (i32.ge_u
                        (local.get $offset_end)
                        (local.tee $offset_end (i32.load8_u (local.get $offset)))
                    )
                    (then
                        (local.set $offset (i32.add (local.get $offset) (i32.const 1)))
                        (return
                            (select
                                (i32.add (local.get $offset) (local.get $offset_end))
                                (i32.const 0)
                                (call $stdlib.check-clarity-name (local.get $offset) (local.get $offset_end))
                            )
                        )
                    )
                )
            )
        )
        (i32.const 0)
    )

    (func $skip-some-ok-err (param $offset i32) (param $offset_end i32) (result i32)
        ;; we need to skip the following value
        (call $stdlib.skip-unknown-value (local.get $offset) (local.get $offset_end))
    )

    (func $skip-tuple (param $offset i32) (param $offset_end i32) (result i32)
        ;; get first 4 bytes as size then parse "size" times a clarity name and a value
        (local $tuple_size i32) (local $name_size i32)
        (if (i32.gt_u (i32.add (local.get $offset) (i32.const 4)) (local.get $offset_end))
            (then (return (i32.const 0)))
        )
        (local.set $tuple_size (call $stdlib.load-i32-be (local.get $offset)))
        ;; a tuple cannot be empty
        (if (i32.eqz (local.get $tuple_size)) (then (return (i32.const 0))))

        (local.set $offset (i32.add (local.get $offset) (i32.const 4)))
        (block $done
            (loop $loop
                ;; check clarity name
                (br_if $done (i32.ge_u (local.get $offset) (local.get $offset_end)))
                (local.set $name_size (i32.load8_u (local.get $offset)))
                (br_if $done
                    (i32.eqz
                        (call $stdlib.check-clarity-name
                            (local.tee $offset (i32.add (local.get $offset) (i32.const 1)))
                            (local.get $name_size)
                        )
                    )
                )
                (local.tee $offset (call $stdlib.skip-unknown-value (i32.add (local.get $offset) (local.get $name_size)) (local.get $offset_end)))
                (br_if $done (i32.eqz))
                (br_if $loop (local.tee $tuple_size (i32.sub (local.get $tuple_size) (i32.const 1))))
            )
        )
        (select (i32.const 0) (local.get $offset) (local.get $tuple_size))
    )

    (func $skip-string-ascii (param $offset i32) (param $offset_end i32) (result i32)
        (local $size i32)
        (if (i32.lt_s (i32.sub (local.get $offset_end) (local.get $offset)) (i32.const 4))
            (then (return (i32.const 0)))
        )
        (local.set $size (call $stdlib.load-i32-be (local.get $offset)))
        (if
            (i32.lt_s
                (i32.sub (local.get $offset_end) (local.tee $offset (i32.add (local.get $offset) (i32.const 4))))
                (local.get $size)
            )
            (then (return (i32.const 0)))
        )
        (select
            (i32.add (local.get $offset) (local.get $size))
            (i32.const 0)
            (call $stdlib.is-valid-string-ascii (local.get $offset) (local.get $size))
        )
    )

    (func $skip-string-utf8 (param $offset i32) (param $offset_end i32) (result i32)
        (local $size i32) (local $char i32) (local $byte i32)
        (if (i32.lt_s (i32.sub (local.get $offset_end) (local.get $offset)) (i32.const 4))
            (then (return (i32.const 0)))
        )
        (local.set $size (call $stdlib.load-i32-be (local.get $offset)))
        (if
            (i32.lt_s
                (i32.sub (local.get $offset_end) (local.tee $offset (i32.add (local.get $offset) (i32.const 4))))
                (local.get $size)
            )
            (then (return (i32.const 0)))
        )
        (block $done
            ;; empty string case
            (br_if $done (i32.eqz (local.get $size)))
            ;; for more info on utf8 decoding, check $stdlib.utf8-to-string-utf8
            (loop $loop
                (local.set $char (i32.load8_u (local.get $offset)))
                ;; try one byte utf8
                (if (i32.lt_u (local.get $char) (i32.const 0x80))
                    (then
                        (local.set $offset (i32.add (local.get $offset) (i32.const 1)))
                        (br_if $loop (local.tee $size (i32.sub (local.get $size) (i32.const 1))))
                        (br $done)
                    )
                )
                ;; try 2 bytes utf8
                (if (i32.eq (i32.and (local.get $char) (i32.const 0xe0)) (i32.const 0xc0))
                    (then
                        (br_if $done (i32.lt_u (local.get $size) (i32.const 2)))
                        (local.set $byte (i32.load8_u offset=1 (local.get $offset)))
                        (br_if $done (i32.ne (i32.and (local.get $byte) (i32.const 0xc0)) (i32.const 0x80)))
                        (local.set $char
                            (i32.or
                                (i32.shl (i32.and (local.get $char) (i32.const 0x1f)) (i32.const 6))
                                (i32.and (local.get $byte) (i32.const 0x3f))
                            )
                        )
                        (br_if $done (i32.lt_u (local.get $char) (i32.const 0x80)))
                        (local.set $offset (i32.add (local.get $offset) (i32.const 2)))
                        (br_if $loop (local.tee $size (i32.sub (local.get $size) (i32.const 2))))
                        (br $done)
                    )
                )
                ;; try 3 bytes utf8
                (if (i32.eq (i32.and (local.get $char) (i32.const 0xf0)) (i32.const 0xe0))
                    (then
                        (br_if $done (i32.lt_u (local.get $size) (i32.const 3)))
                        (local.set $byte (i32.load8_u offset=1 (local.get $offset)))
                        (br_if $done (i32.ne (i32.and (local.get $byte) (i32.const 0xc0)) (i32.const 0x80)))
                        (local.set $char
                            (i32.or
                                (i32.or
                                    (i32.shl (i32.and (local.get $char) (i32.const 0xf)) (i32.const 12))
                                    (i32.shl (i32.and (local.get $byte) (i32.const 0x3f)) (i32.const 6))
                                )
                                (i32.and
                                    (local.tee $byte (i32.load8_u offset=2 (local.get $offset)))
                                    (i32.const 0x3f)
                                )
                            )
                        )
                        (br_if $done (i32.ne (i32.and (local.get $byte) (i32.const 0xc0)) (i32.const 0x80)))
                        (br_if $done (i32.lt_u (local.get $char) (i32.const 0x800)))
                        (br_if $done (i32.eq (i32.and (local.get $char) (i32.const 0xfffff800)) (i32.const 0xd800)))
                        (local.set $offset (i32.add (local.get $offset) (i32.const 3)))
                        (br_if $loop (local.tee $size (i32.sub (local.get $size) (i32.const 3))))
                        (br $done)
                    )
                )
                ;; finally, try 4 bytes utf8
                (if (i32.eq (i32.and (local.get $char) (i32.const 0xf8)) (i32.const 0xf0))
                    (then
                        (br_if $done (i32.lt_u (local.get $size) (i32.const 4)))
                        (local.set $byte (i32.load8_u offset=1 (local.get $offset)))
                        (br_if $done (i32.ne (i32.and (local.get $byte) (i32.const 0xc0)) (i32.const 0x80)))
                        (local.set $char
                            (i32.or
                                (i32.or
                                    (i32.shl (i32.and (local.get $char) (i32.const 0x7)) (i32.const 18))
                                    (i32.shl (i32.and (local.get $byte) (i32.const 0x3f)) (i32.const 12))
                                )
                                (i32.shl
                                    (i32.and
                                        (local.tee $byte (i32.load8_u offset=2 (local.get $offset)))
                                        (i32.const 0x3f)
                                    )
                                    (i32.const 6)
                                )
                            )
                        )
                        (br_if $done (i32.ne (i32.and (local.get $byte) (i32.const 0xc0)) (i32.const 0x80)))
                        (local.set $byte (i32.load8_u offset=3 (local.get $offset)))
                        (br_if $done (i32.ne (i32.and (local.get $byte) (i32.const 0xc0)) (i32.const 0x80)))
                        (local.set $char
                            (i32.or
                                (local.get $char)
                                (i32.and (local.get $byte) (i32.const 0x3f))
                            )
                        )
                        (br_if $done (i32.lt_u (i32.sub (local.get $char) (i32.const 0x110000)) (i32.const 0xfff00000)))
                        (local.set $offset (i32.add (local.get $offset) (i32.const 4)))
                        (br_if $loop (local.tee $size (i32.sub (local.get $size) (i32.const 4))))
                    )
                )
            )
        )
        (select
            (i32.const 0)
            (local.get $offset)
            (local.get $size)
        )
    )

    (func $stdlib.check-clarity-name (param $offset i32) (param $size i32) (result i32)
        ;; check if clarity name is valid
        (local $char i32)

        ;; check if size is null or > 128
        (if (i32.lt_u (i32.sub (local.get $size) (i32.const 129)) (i32.const -128))
            (then (return (i32.const 0)))
        )

        ;; if first char is alpha, we start validating that remainings are in [a-zA-Z0-9-_!?+<>=/*]
        (if
            (i32.lt_u
                (i32.sub
                    (i32.and (i32.load8_u (local.get $offset)) (i32.const 0x1fffdf))
                    (i32.const 65)
                )
                (i32.const 26)
            )
            (then
                (block $done
                    (loop $loop
                        (br_if $done (i32.eqz (local.tee $size (i32.sub (local.get $size) (i32.const 1)))))
                        (local.set $char
                            (i32.load8_u
                                (local.tee $offset (i32.add (local.get $offset) (i32.const 1)))
                            )
                        )
                        ;; check if is_alpha
                        (br_if $loop
                            (i32.lt_u
                                (i32.sub
                                    (i32.and (local.get $char) (i32.const 0x1fffdf))
                                    (i32.const 65)
                                )
                                (i32.const 26)
                            )
                        )
                        ;; check if is_num
                        (br_if $loop
                            (i32.lt_u (i32.sub (local.get $char) (i32.const 48)) (i32.const 10))
                        )
                        ;; check if is special char -_!?+<>=/*
                        (br_if $loop
                            (i32.and
                                (i32.lt_u
                                    (local.tee $char (i32.sub (local.get $char) (i32.const 33)))
                                    (i32.const 63)
                                )
                                (i32.wrap_i64
                                    (i64.shr_u
                                        (i64.const 0x4000000078005601)
                                        (i64.extend_i32_u (local.get $char))
                                    )
                                )
                            )
                        )
                    )
                )
                (return (i32.eqz (local.get $size)))
            )
        )

        ;; check for size 1 with -+=/*<>
        (if (i32.eq (local.get $size) (i32.const 1))
            (then
                (return
                    (i32.and
                        (i32.lt_u
                            (local.tee $char (i32.load8_u (local.get $offset)))
                            (i32.const 63)
                        )
                        (i32.wrap_i64
                            (i64.shr_u (i64.const 0x7000ac0000000000) (i64.extend_i32_u (local.get $char)))
                        )
                    )
                )
            )
        )

        ;; check for <= and >=, which are [0x3c, 0x3d] and [0x3e, 0x3d]
        (if (i32.eq (local.get $size) (i32.const 2))
            (then
                (return
                    (i32.eq
                        (i32.and (i32.load16_u (local.get $offset)) (i32.const -3))
                        (i32.const 0x3d3c)
                    )
                )
            )
        )

        (i32.const 0)
    )

    ;;
    ;; Export section

    ;; Memory
    (memory (export "memory") 10)

    ;; Globals
    (export "stack-pointer" (global $stack-pointer))
    (export "runtime-error-code" (global $runtime-error-code))
    (export "runtime-error-arg-offset" (global $runtime-error-arg-offset))
    (export "runtime-error-arg-len" (global $runtime-error-arg-len))
    (export "runtime-error-value-offset" (global $runtime-error-value-offset))
    (export "runtime-error-type-ser-offset" (global $runtime-error-type-ser-offset))
    (export "runtime-error-type-ser-len" (global $runtime-error-type-ser-len))

    ;; Functions
    (export "stdlib.add-uint" (func $stdlib.add-uint))
    (export "stdlib.add-int" (func $stdlib.add-int))
    (export "stdlib.sub-uint" (func $stdlib.sub-uint))
    (export "stdlib.sub-int" (func $stdlib.sub-int))
    (export "stdlib.mul-uint" (func $stdlib.mul-uint))
    (export "stdlib.mul-int" (func $stdlib.mul-int))
    (export "stdlib.div-uint" (func $stdlib.div-uint))
    (export "stdlib.div-int" (func $stdlib.div-int))
    (export "stdlib.mod-uint" (func $stdlib.mod-uint))
    (export "stdlib.mod-int" (func $stdlib.mod-int))
    (export "stdlib.lt-uint" (func $stdlib.lt-uint))
    (export "stdlib.gt-uint" (func $stdlib.gt-uint))
    (export "stdlib.le-uint" (func $stdlib.le-uint))
    (export "stdlib.ge-uint" (func $stdlib.ge-uint))
    (export "stdlib.lt-int" (func $stdlib.lt-int))
    (export "stdlib.gt-int" (func $stdlib.gt-int))
    (export "stdlib.le-int" (func $stdlib.le-int))
    (export "stdlib.ge-int" (func $stdlib.ge-int))
    (export "stdlib.lt-buff" (func $stdlib.lt-buff))
    (export "stdlib.gt-buff" (func $stdlib.gt-buff))
    (export "stdlib.le-buff" (func $stdlib.le-buff))
    (export "stdlib.ge-buff" (func $stdlib.ge-buff))
    (export "stdlib.log2-uint" (func $stdlib.log2-uint))
    (export "stdlib.log2-int" (func $stdlib.log2-int))
    (export "stdlib.sqrti-uint" (func $stdlib.sqrti-uint))
    (export "stdlib.sqrti-int" (func $stdlib.sqrti-int))
    (export "stdlib.bit-and-uint" (func $stdlib.bit-and))
    (export "stdlib.bit-and-int" (func $stdlib.bit-and))
    (export "stdlib.bit-not-uint" (func $stdlib.bit-not))
    (export "stdlib.bit-not-int" (func $stdlib.bit-not))
    (export "stdlib.bit-or-uint" (func $stdlib.bit-or))
    (export "stdlib.bit-or-int" (func $stdlib.bit-or))
    (export "stdlib.bit-xor-uint" (func $stdlib.bit-xor))
    (export "stdlib.bit-xor-int" (func $stdlib.bit-xor))
    (export "stdlib.bit-shift-left-uint" (func $stdlib.bit-shift-left))
    (export "stdlib.bit-shift-left-int" (func $stdlib.bit-shift-left))
    (export "stdlib.bit-shift-right-uint" (func $stdlib.bit-shift-right-uint))
    (export "stdlib.bit-shift-right-int" (func $stdlib.bit-shift-right-int))
    (export "stdlib.pow-uint" (func $stdlib.pow-uint))
    (export "stdlib.pow-int" (func $stdlib.pow-int))
    (export "stdlib.sha256-buf" (func $stdlib.sha256-buf))
    (export "stdlib.sha256-int" (func $stdlib.sha256-int))
    (export "stdlib.hash160-buf" (func $stdlib.hash160-buf))
    (export "stdlib.hash160-int" (func $stdlib.hash160-int))
    (export "stdlib.store-i32-be" (func $stdlib.store-i32-be))
    (export "stdlib.store-i64-be" (func $stdlib.store-i64-be))
    (export "stdlib.load-i32-be" (func $stdlib.load-i32-be))
    (export "stdlib.buff-to-uint-be" (func $stdlib.buff-to-uint-be))
    (export "stdlib.buff-to-uint-le" (func $stdlib.buff-to-uint-le))
    (export "stdlib.not" (func $stdlib.not))
    (export "stdlib.principal-construct" (func $stdlib.principal-construct))
    (export "stdlib.is-valid-contract-name" (func $stdlib.is-valid-contract-name))
    (export "stdlib.is-alpha" (func $stdlib.is-alpha))
    (export "stdlib.is-valid-char" (func $stdlib.is-valid-char))
    (export "stdlib.is-transient" (func $stdlib.is-transient))
    (export "stdlib.is-version-valid" (func $stdlib.is-version-valid))
    (export "stdlib.string-to-int" (func $stdlib.string-to-int))
    (export "stdlib.string-to-uint" (func $stdlib.string-to-uint))
    (export "stdlib.utf8-to-uint" (func $stdlib.utf8-to-uint))
    (export "stdlib.utf8-to-int" (func $stdlib.utf8-to-int))
    (export "stdlib.uint-to-string" (func $stdlib.uint-to-string))
    (export "stdlib.uint-to-utf8" (func $stdlib.uint-to-utf8))
    (export "stdlib.int-to-string" (func $stdlib.int-to-string))
    (export "stdlib.int-to-utf8" (func $stdlib.int-to-utf8))
    (export "stdlib.to-uint" (func $stdlib.to-uint))
    (export "stdlib.to-int" (func $stdlib.to-int))
    (export "stdlib.sha512-buf" (func $stdlib.sha512-buf))
    (export "stdlib.sha512-int" (func $stdlib.sha512-int))
    (export "stdlib.convert-scalars-to-utf8" (func $stdlib.convert-scalars-to-utf8))
    (export "stdlib.is-valid-string-ascii" (func $stdlib.is-valid-string-ascii))
    (export "stdlib.utf8-to-string-utf8" (func $stdlib.utf8-to-string-utf8))
    (export "stdlib.bsearch-clarity-name" (func $stdlib.bsearch-clarity-name))
    (export "stdlib.check-clarity-name" (func $stdlib.check-clarity-name))
    (export "stdlib.skip-unknown-value" (func $stdlib.skip-unknown-value))
)
