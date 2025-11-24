use std::collections::HashMap;

use clar2wasm::compile;
use clar2wasm::datastore::{BurnDatastore, StacksConstants};
use clar2wasm::initialize::initialize_contract;
use clar2wasm::tools::execute;
use clar2wasm::wasm_utils::call_function;
use clarity::consts::CHAIN_ID_TESTNET;
use clarity::types::chainstate::BlockHeaderHash;
use clarity::types::StacksEpochId;
use clarity::vm::callables::DefineType;
use clarity::vm::contexts::{CallStack, EventBatch, GlobalContext};
use clarity::vm::contracts::Contract;
use clarity::vm::costs::LimitedCostTracker;
use clarity::vm::database::{ClarityDatabase, MemoryBackingStore};
use clarity::vm::errors::{CheckErrors, Error, RuntimeErrorType};
use clarity::vm::events::StacksTransactionEvent;
use clarity::vm::types::{
    PrincipalData, QualifiedContractIdentifier, ResponseData, StandardPrincipalData, TupleData,
    TypeSignature,
};
use clarity::vm::{ClarityVersion, ContractContext, Value};
use hex::FromHex;

/// This macro provides a convenient way to test contract initialization.
/// In order, it takes as parameters:
/// - the name of the test to create,
/// - the names of the contracts to initialize (optionally including a
///   subdirectory, e.g. `multi-contract/contract-caller`),
/// - a closure with type
///   `|global_context: &mut GlobalContext, contract_context: &HashMap<&str, ContractContext>, return_val: Option<Value>|`
///   and that contains all the assertions we want to test.
macro_rules! test_multi_contract_init {
    ($func: ident, $contract_names: expr, $context_test: expr) => {
        #[test]
        fn $func() {
            let mut contract_contexts = HashMap::new();

            let constants = StacksConstants::default();
            let burn_datastore = BurnDatastore::new(constants);
            let mut clarity_store = MemoryBackingStore::new();
            let mut cost_tracker = LimitedCostTracker::new_free();

            let mut db = ClarityDatabase::new(&mut clarity_store, &burn_datastore, &burn_datastore);
            db.begin();
            db.set_clarity_epoch_version(StacksEpochId::latest())
                .expect("Failed to set epoch version.");
            db.commit().expect("Failed to commit.");

            // Iterate through all of the contracts and initialize them,
            // saving the return value of the last one.
            let mut return_val = None;
            for contract in $contract_names.iter() {
                let contract_name = contract.rsplit('/').next().unwrap();
                let contract_id = QualifiedContractIdentifier::new(
                    StandardPrincipalData::transient(),
                    (*contract_name).into(),
                );

                let contract_path = format!(
                    "{}/tests/contracts/{}.clar",
                    env!("CARGO_MANIFEST_DIR"),
                    contract
                );
                let contract_str = std::fs::read_to_string(contract_path).unwrap();

                let mut compile_result = clarity_store
                    .as_analysis_db()
                    .execute(|analysis_db| {
                        compile(
                            contract_str.as_str(),
                            &contract_id,
                            LimitedCostTracker::new_free(),
                            ClarityVersion::Clarity2,
                            StacksEpochId::latest(),
                            analysis_db,
                            false,
                        )
                        .map_err(|_| CheckErrors::Expects("Compilation failure".to_string()))
                    })
                    .expect("Failed to compile contract.");

                clarity_store
                    .as_analysis_db()
                    .execute(|analysis_db| {
                        analysis_db.insert_contract(&contract_id, &compile_result.contract_analysis)
                    })
                    .expect("Failed to insert contract analysis.");

                let mut contract_context =
                    ContractContext::new(contract_id.clone(), ClarityVersion::Clarity2);
                // compile_result.module.emit_wasm_file("test.wasm").unwrap();
                contract_context.set_wasm_module(compile_result.module.emit_wasm());

                let mut global_context = GlobalContext::new(
                    false,
                    CHAIN_ID_TESTNET,
                    clarity_store.as_clarity_db(),
                    cost_tracker,
                    StacksEpochId::latest(),
                );
                global_context.begin();
                global_context
                    .execute(|g| g.database.insert_contract_hash(&contract_id, &contract_str))
                    .expect("Failed to insert contract hash.");

                return_val = initialize_contract(
                    &mut global_context,
                    &mut contract_context,
                    None,
                    &compile_result.contract_analysis,
                )
                .expect("Failed to initialize contract.")
                .ret;

                let data_size = contract_context.data_size;
                global_context
                    .database
                    .insert_contract(
                        &contract_id,
                        Contract {
                            contract_context: contract_context.clone(),
                        },
                    )
                    .expect("Failed to insert contract.");
                global_context
                    .database
                    .set_contract_data_size(&contract_id, data_size)
                    .expect("Failed to set contract data size.");

                global_context.commit().unwrap();
                cost_tracker = global_context.cost_track;

                contract_contexts.insert(contract_name, contract_context);
            }

            // Do this once for all contracts
            let recipient = PrincipalData::Standard(StandardPrincipalData::transient());
            let amount = 1_000_000_000;
            let mut conn = clarity_store.as_clarity_db();
            execute(&mut conn, |database| {
                let mut snapshot = database.get_stx_balance_snapshot(&recipient)?;
                snapshot.credit(amount)?;
                snapshot.save()?;
                database.increment_ustx_liquid_supply(amount)
            })
            .expect("Failed to increment liquid supply.");

            let mut global_context = GlobalContext::new(
                false,
                CHAIN_ID_TESTNET,
                clarity_store.as_clarity_db(),
                cost_tracker,
                StacksEpochId::latest(),
            );
            global_context.begin();

            #[allow(clippy::redundant_closure_call)]
            $context_test(&mut global_context, &contract_contexts, return_val);

            global_context.commit().unwrap();
        }
    };
}

/// This macro provides a convenient way to test contract initialization.
/// In order, it takes as parameters:
/// - the name of the test to create,
/// - the name of the contracts to initialize,
/// - a closure with type
///   `|global_context: &mut GlobalContext, contract_context: &ContractContext, return_val: Option<Value>|`
///   and that contains all the assertions we want to test.
macro_rules! test_contract_init {
    ($func: ident, $contract_name: literal, $context_test: expr) => {
        test_multi_contract_init!(
            $func,
            [$contract_name],
            |global_context: &mut GlobalContext,
             contract_contexts: &HashMap<&str, ContractContext>,
             return_val: Option<Value>| {
                let contract_context = contract_contexts.get($contract_name).unwrap();
                $context_test(global_context, contract_context, return_val);
            }
        );
    };
}

/// This macro provides a convenient way to test functions inside contracts.
/// In order, it takes as parameters:
/// - the name of the test to create,
/// - the name of all contracts to initialize,
/// - the name of the contract containing the function,
/// - the name of the function to test,
/// - an optional list of parameters,
/// - a closure with type `|result: Result<Value, Error>|`, and
///   that contains all the assertions we want to test.
macro_rules! test_multi_contract_call {
    ($func: ident, $init_contracts: expr, $contract_name: literal, $contract_func: literal, $params: expr, $test: expr) => {
        test_multi_contract_init!(
            $func,
            $init_contracts,
            |global_context: &mut GlobalContext,
             contract_contexts: &HashMap<&str, ContractContext>,
             _return_val: Option<Value>| {
                // Initialize a call stack
                let mut call_stack = CallStack::new();

                let result = call_function(
                    $contract_func,
                    $params,
                    global_context,
                    &contract_contexts.get($contract_name).unwrap(),
                    &mut call_stack,
                    Some(StandardPrincipalData::transient().into()),
                    Some(StandardPrincipalData::transient().into()),
                    None,
                );

                // https://github.com/rust-lang/rust-clippy/issues/1553
                #[allow(clippy::redundant_closure_call)]
                $test(result);
            }
        );
    };

    ($func: ident, $init_contracts: expr, $contract_name: literal, $contract_func: literal, $test: expr) => {
        test_multi_contract_call!(
            $func,
            $init_contracts,
            $contract_name,
            $contract_func,
            &[],
            $test
        );
    };
}

/// This macro provides a convenient way to test functions inside contracts.
/// In order, it takes as parameters:
/// - the name of the test to create,
/// - the name of the contract containing the function,
/// - the name of the function to test,
/// - an optional list of parameters,
/// - a closure with type `|response: ResponseData|`, and
///   that contains all the assertions we want to test.
macro_rules! test_multi_contract_call_response {
    ($func: ident, $init_contracts: expr, $contract_name: literal, $contract_func: literal, $params: expr, $test: expr) => {
        test_multi_contract_call!(
            $func,
            $init_contracts,
            $contract_name,
            $contract_func,
            $params,
            |result: Result<Value, Error>| {
                let result = result.expect("Function call failed.");

                if let Value::Response(response_data) = result {
                    // https://github.com/rust-lang/rust-clippy/issues/1553
                    #[allow(clippy::redundant_closure_call)]
                    $test(response_data);
                } else {
                    panic!("Unexpected result received from Wasm function call.");
                }
            }
        );
    };

    ($func: ident, $init_contracts: expr, $contract_name: literal, $contract_func: literal, $test: expr) => {
        test_multi_contract_call_response!(
            $func,
            $init_contracts,
            $contract_name,
            $contract_func,
            &[],
            $test
        );
    };
}

/// This macro provides a convenient way to test functions inside contracts.
/// In order, it takes as parameters:
/// - the name of the test to create,
/// - the name of the contract containing the function,
/// - the name of the function to test,
/// - an optional list of parameters,
/// - a closure with type `|response: ResponseData|`, and
///   that contains all the assertions we want to test.
#[macro_export]
macro_rules! test_contract_call_response {
    ($func: ident, $contract_name: literal, $contract_func: literal, $params: expr, $test: expr) => {
        test_multi_contract_call_response!(
            $func,
            [$contract_name],
            $contract_name,
            $contract_func,
            $params,
            $test
        );
    };

    ($func: ident, $contract_name: literal, $contract_func: literal, $test: expr) => {
        test_contract_call_response!($func, $contract_name, $contract_func, &[], $test);
    };
}

/// This macro provides a convenient way to test functions inside contracts.
/// In order, it takes as parameters:
/// - the name of the test to create,
/// - the name of all contracts to initialize,
/// - the name of the contract containing the function,
/// - the name of the function to test,
/// - an optional list of parameters,
/// - a closure with type `|result: Result<Value, Error>|`
///   that contains all the assertions we want to test on the result, and
/// - a closure with type `|events: &Vec<EventBatch>|`,
///   that contains all the assertions we want to test on the events.
macro_rules! test_multi_contract_call_events {
    ($func: ident, $init_contracts: expr, $contract_name: literal, $contract_func: literal, $params: expr, $test_result: expr, $test_events: expr) => {
        test_multi_contract_init!(
            $func,
            $init_contracts,
            |global_context: &mut GlobalContext,
             contract_contexts: &HashMap<&str, ContractContext>,
             _return_val: Option<Value>| {
                // Initialize a call stack
                let mut call_stack = CallStack::new();

                let result = call_function(
                    $contract_func,
                    $params,
                    global_context,
                    &contract_contexts.get($contract_name).unwrap(),
                    &mut call_stack,
                    Some(StandardPrincipalData::transient().into()),
                    Some(StandardPrincipalData::transient().into()),
                    None,
                );

                // https://github.com/rust-lang/rust-clippy/issues/1553
                #[allow(clippy::redundant_closure_call)]
                $test_result(result);

                #[allow(clippy::redundant_closure_call)]
                $test_events(&global_context.event_batches);
            }
        );
    };

    ($func: ident, $init_contracts: expr, $contract_name: literal, $contract_func: literal, $test_result: expr, $test_events: expr) => {
        test_multi_contract_call_events!(
            $func,
            $init_contracts,
            $contract_name,
            $contract_func,
            &[],
            $test_result,
            $test_events
        );
    };
}

/// This macro provides a convenient way to test functions inside contracts.
/// In order, it takes as parameters:
/// - the name of the test to create,
/// - the name of the contract containing the function,
/// - the name of the function to test,
/// - an optional list of parameters,
/// - a closure with type `|result: Result<Value, Error>|`
///   that contains all the assertions we want to test on the result, and
/// - a closure with type `|events: &Vec<EventBatch>|`,
///   that contains all the assertions we want to test on the events.
#[allow(unused_macros)]
macro_rules! test_contract_call_events {
    ($func: ident, $contract_name: literal, $contract_func: literal, $params: expr, $test_result: expr, $test_events: expr) => {
        test_multi_contract_call_events!(
            $func,
            [$contract_name],
            $contract_name,
            $contract_func,
            $params,
            $test_result,
            $test_events
        );
    };

    ($func: ident, $contract_name: literal, $contract_func: literal, $test_result: expr, $test_events: expr) => {
        test_contract_call_events!(
            $func,
            $contract_name,
            $contract_func,
            &[],
            $test_result,
            $test_events
        );
    };
}

/// This macro provides a convenient way to test functions inside contracts.
/// In order, it takes as parameters:
/// - the name of the test to create,
/// - the name of all contracts to initialize,
/// - the name of the contract containing the function,
/// - the name of the function to test,
/// - an optional list of parameters,
/// - a closure with type `|result: Result<Value, Error>|`,
///   that contains all the assertions we want to test on the result, and
/// - a closure with type `|events: &Vec<EventBatch>|`,
///   that contains all the assertions we want to test on the events.
macro_rules! test_multi_contract_call_response_events {
    ($func: ident, $init_contracts: expr, $contract_name: literal, $contract_func: literal, $params: expr, $test_response: expr, $test_events: expr) => {
        test_multi_contract_call_events!(
            $func,
            $init_contracts,
            $contract_name,
            $contract_func,
            $params,
            |result: Result<Value, Error>| {
                let result = result.expect("Function call failed.");

                if let Value::Response(response_data) = result {
                    // https://github.com/rust-lang/rust-clippy/issues/1553
                    #[allow(clippy::redundant_closure_call)]
                    $test_response(response_data);
                } else {
                    panic!("Unexpected result received from Wasm function call.");
                }
            },
            $test_events
        );
    };

    ($func: ident, $init_contracts: expr, $contract_name: literal, $contract_func: literal, $test_response: expr, $test_events: expr) => {
        test_multi_contract_call_response_events!(
            $func,
            $init_contracts,
            $contract_name,
            $contract_func,
            &[],
            $test_response,
            $test_events
        );
    };
}

/// This macro provides a convenient way to test functions inside contracts.
/// In order, it takes as parameters:
/// - the name of the test to create,
/// - the name of the contract containing the function,
/// - the name of the function to test,
/// - an optional list of parameters,
/// - a closure with type `|response: ResponseData|`,
///   that contains all the assertions we want to test on the response, and
/// - a closure with type `|events: &Vec<EventBatch>|`,
///   that contains all the assertions we want to test on the events.
macro_rules! test_contract_call_response_events {
    ($func: ident, $contract_name: literal, $contract_func: literal, $params: expr, $test_response: expr, $test_events: expr) => {
        test_multi_contract_call_response_events!(
            $func,
            [$contract_name],
            $contract_name,
            $contract_func,
            $params,
            $test_response,
            $test_events
        );
    };

    ($func: ident, $contract_name: literal, $contract_func: literal, $test_response: expr, $test_events: expr) => {
        test_contract_call_response_events!(
            $func,
            $contract_name,
            $contract_func,
            &[],
            $test_response,
            $test_events
        );
    };
}

macro_rules! test_contract_call_error {
    ($func: ident, $contract_name: literal, $contract_func: literal, $test: expr) => {
        test_multi_contract_init!(
            $func,
            [$contract_name],
            |global_context: &mut GlobalContext,
             contract_contexts: &HashMap<&str, ContractContext>,
             _return_val: Option<Value>| {
                // Initialize a call stack
                let mut call_stack = CallStack::new();

                let result = call_function(
                    $contract_func,
                    &[],
                    global_context,
                    &contract_contexts.get($contract_name).unwrap(),
                    &mut call_stack,
                    Some(StandardPrincipalData::transient().into()),
                    Some(StandardPrincipalData::transient().into()),
                    None,
                );

                match result {
                    Err(e) => $test(e),
                    _ => (),
                }
            }
        );
    };
}

// ****************************************************************************
//  TESTS START HERE
// ****************************************************************************

test_contract_init!(
    test_define_private,
    "call-private-with-args",
    |_global_context: &mut GlobalContext,
     contract_context: &ContractContext,
     _return_val: Option<Value>| {
        let public_function = contract_context.lookup_function("simple").unwrap();
        assert_eq!(public_function.define_type, DefineType::Private);
        assert_eq!(
            public_function.get_arg_types(),
            &[TypeSignature::IntType, TypeSignature::IntType]
        );
        assert_eq!(
            public_function.get_return_type(),
            &Some(TypeSignature::IntType)
        );
    }
);

test_contract_init!(
    test_define_public,
    "define-public-ok",
    |_global_context: &mut GlobalContext,
     contract_context: &ContractContext,
     _return_val: Option<Value>| {
        let public_function = contract_context.lookup_function("simple").unwrap();
        assert_eq!(public_function.define_type, DefineType::Public);
        assert!(public_function.get_arg_types().is_empty());
        assert_eq!(
            public_function.get_return_type(),
            &Some(TypeSignature::ResponseType(Box::new((
                TypeSignature::IntType,
                TypeSignature::NoType
            ))))
        );
    }
);

test_contract_init!(
    test_define_data_var,
    "var-get",
    |_global_context: &mut GlobalContext,
     contract_context: &ContractContext,
     _return_val: Option<Value>| {
        let metadata = contract_context.meta_data_var.get("something").unwrap();
        assert_eq!(metadata.value_type, TypeSignature::IntType);
    }
);

test_contract_call_response!(
    test_as_contract_sender,
    "as-contract",
    "check-sender",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::Principal(PrincipalData::Contract(QualifiedContractIdentifier {
                issuer: StandardPrincipalData::transient(),
                name: "as-contract".into()
            }))
        );
    }
);

test_contract_call_response!(
    test_as_contract_caller,
    "as-contract",
    "check-caller",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::Principal(PrincipalData::Contract(QualifiedContractIdentifier {
                issuer: StandardPrincipalData::transient(),
                name: "as-contract".into()
            }))
        );
    }
);

test_contract_call_response!(
    test_as_contract_sender_no_leak,
    "as-contract",
    "check-sender-after-as-contract",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::Principal(PrincipalData::Standard(StandardPrincipalData::transient()))
        );
    }
);

test_contract_call_response!(
    test_as_contract_caller_no_leak,
    "as-contract",
    "check-caller-after-as-contract",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::Principal(PrincipalData::Standard(StandardPrincipalData::transient()))
        );
    }
);

test_contract_init!(
    test_define_ft,
    "define-tokens",
    |_global_context: &mut GlobalContext,
     contract_context: &ContractContext,
     _return_val: Option<Value>| {
        let ft_metadata = contract_context
            .meta_ft
            .get("foo")
            .expect("FT 'foo' not found");
        assert_eq!(ft_metadata.total_supply, None);

        let ft_metadata = contract_context
            .meta_ft
            .get("bar")
            .expect("FT 'bar' not found");
        assert_eq!(ft_metadata.total_supply, Some(1000000u128));
    }
);

test_contract_init!(
    test_define_nft,
    "define-tokens",
    |_global_context: &mut GlobalContext,
     contract_context: &ContractContext,
     _return_val: Option<Value>| {
        let nft_metadata = contract_context
            .meta_nft
            .get("baz")
            .expect("NFT 'baz' not found");
        assert_eq!(nft_metadata.key_type, TypeSignature::UIntType);
    }
);

test_contract_init!(
    test_define_map,
    "define-map",
    |_global_context: &mut GlobalContext,
     contract_context: &ContractContext,
     _return_val: Option<Value>| {
        let map_metadata = contract_context
            .meta_data_map
            .get("my-map")
            .expect("Map 'my-map' not found");
        assert_eq!(map_metadata.key_type, TypeSignature::PrincipalType);
        assert_eq!(map_metadata.value_type, TypeSignature::UIntType);
    }
);

test_contract_call_response!(
    test_ft_get_supply_0,
    "tokens",
    "foo-get-supply-0",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::UInt(0));
    }
);

test_contract_call_response!(
    test_ft_mint,
    "tokens",
    "foo-mint",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_ft_mint_0,
    "tokens",
    "foo-mint-0",
    |response: ResponseData| {
        assert!(!response.committed);
        assert_eq!(*response.data, Value::UInt(1));
    }
);

test_contract_call_response!(
    test_ft_balance_0,
    "tokens",
    "ft-balance-0",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::UInt(0));
    }
);

test_contract_call_response!(
    test_ft_balance_10,
    "tokens",
    "ft-balance-10",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::UInt(10));
    }
);

test_contract_call_response!(
    test_ft_burn_unowned,
    "tokens",
    "ft-burn-unowned",
    |response: ResponseData| {
        assert!(!response.committed);
        assert_eq!(*response.data, Value::UInt(1));
    }
);

test_contract_call_response!(
    test_ft_burn_0,
    "tokens",
    "ft-burn-0",
    |response: ResponseData| {
        assert!(!response.committed);
        assert_eq!(*response.data, Value::UInt(1));
    }
);

test_contract_call_response!(
    test_ft_burn_ok,
    "tokens",
    "ft-burn-ok",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_ft_burn_too_many,
    "tokens",
    "ft-burn-too-many",
    |response: ResponseData| {
        assert!(!response.committed);
        assert_eq!(*response.data, Value::UInt(1));
    }
);

test_contract_call_response!(
    test_ft_burn_other,
    "tokens",
    "ft-burn-other",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_ft_transfer_unowned,
    "tokens",
    "ft-transfer-unowned",
    |response: ResponseData| {
        assert!(!response.committed);
        assert_eq!(*response.data, Value::UInt(1));
    }
);

test_contract_call_response!(
    test_ft_transfer_0,
    "tokens",
    "ft-transfer-0",
    |response: ResponseData| {
        assert!(!response.committed);
        assert_eq!(*response.data, Value::UInt(3));
    }
);

test_contract_call_response!(
    test_ft_transfer_ok,
    "tokens",
    "ft-transfer-ok",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_ft_transfer_too_many,
    "tokens",
    "ft-transfer-too-many",
    |response: ResponseData| {
        assert!(!response.committed);
        assert_eq!(*response.data, Value::UInt(1));
    }
);

test_contract_call_response!(
    test_ft_transfer_other,
    "tokens",
    "ft-transfer-other",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_ft_transfer_self,
    "tokens",
    "ft-transfer-self",
    |response: ResponseData| {
        assert!(!response.committed);
        assert_eq!(*response.data, Value::UInt(2));
    }
);

test_contract_call_response!(
    test_nft_mint,
    "tokens",
    "nft-mint",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_nft_mint_other,
    "tokens",
    "nft-mint-other",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_nft_mint_duplicate,
    "tokens",
    "nft-mint-duplicate",
    |response: ResponseData| {
        assert!(!response.committed);
        assert_eq!(*response.data, Value::UInt(1));
    }
);

test_contract_call_response!(
    test_nft_get_owner,
    "tokens",
    "nft-get-owner",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::some(Value::Principal(
                PrincipalData::parse("ST1PQHQKV0RJXZFY1DGX8MNSNYVE3VGZJSRTPGZGM").unwrap()
            ))
            .unwrap()
        );
    }
);

test_contract_call_response!(
    test_nft_get_owner_unowned,
    "tokens",
    "nft-get-owner-unowned",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::none(),);
    }
);

test_contract_call_response!(
    test_nft_burn,
    "tokens",
    "nft-burn",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_nft_burn_other,
    "tokens",
    "nft-burn-other",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_nft_burn_wrong,
    "tokens",
    "nft-burn-wrong",
    |response: ResponseData| {
        assert!(!response.committed);
        assert_eq!(*response.data, Value::UInt(3));
    }
);

test_contract_call_response!(
    test_nft_transfer_does_not_exist,
    "tokens",
    "nft-transfer-does-not-exist",
    |response: ResponseData| {
        assert!(!response.committed);
        assert_eq!(*response.data, Value::UInt(3));
    }
);

test_contract_call_response!(
    test_nft_transfer_ok,
    "tokens",
    "nft-transfer-ok",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_nft_transfer_wrong,
    "tokens",
    "nft-transfer-wrong",
    |response: ResponseData| {
        assert!(!response.committed);
        assert_eq!(*response.data, Value::UInt(3));
    }
);

test_contract_call_response!(
    test_nft_transfer_not_owner,
    "tokens",
    "nft-transfer-not-owner",
    |response: ResponseData| {
        assert!(!response.committed);
        assert_eq!(*response.data, Value::UInt(1));
    }
);

test_contract_call_response!(
    test_nft_transfer_self,
    "tokens",
    "nft-transfer-self",
    |response: ResponseData| {
        assert!(!response.committed);
        assert_eq!(*response.data, Value::UInt(2));
    }
);

test_contract_call_response!(
    test_nft_transfer_other,
    "tokens",
    "nft-transfer-other",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_map_insert,
    "maps",
    "test-map-insert",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_map_insert_exists,
    "maps",
    "test-map-insert-exists",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_map_set,
    "maps",
    "test-map-set",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_map_set_exists,
    "maps",
    "test-map-set-exists",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_map_get_insert,
    "maps",
    "test-map-get-insert",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::some(Value::UInt(2)).unwrap());
    }
);

test_contract_call_response!(
    test_map_get_insert_exists,
    "maps",
    "test-map-get-insert-exists",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::some(Value::UInt(1)).unwrap());
    }
);

test_contract_call_response!(
    test_map_get_set,
    "maps",
    "test-map-get-set",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::some(Value::UInt(2)).unwrap());
    }
);

test_contract_call_response!(
    test_map_get_set_exists,
    "maps",
    "test-map-get-set-exists",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::some(Value::UInt(2)).unwrap());
    }
);

test_contract_call_response!(
    test_map_get_none,
    "maps",
    "test-map-get-none",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::none());
    }
);

test_contract_call_response!(
    test_map_delete,
    "maps",
    "test-map-delete",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_map_delete_none,
    "maps",
    "test-map-delete-none",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_map_delete_get,
    "maps",
    "test-map-delete-get",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::none());
    }
);

test_contract_call_response!(
    test_sha256_buffer,
    "hashes",
    "sha256-buffer",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::Sequence(clarity::vm::types::SequenceData::Buffer(
                clarity::vm::types::BuffData {
                    data: Vec::from_hex(
                        "973153f86ec2da1748e63f0cf85b89835b42f8ee8018c549868a1308a19f6ca3"
                    )
                    .unwrap(),
                },
            )),
        );
    }
);

test_contract_call_response!(
    test_sha256_int,
    "hashes",
    "sha256-integer",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::Sequence(clarity::vm::types::SequenceData::Buffer(
                clarity::vm::types::BuffData {
                    data: Vec::from_hex(
                        "bf9d9b2cf6fa58e2d98fe7357d73ddf052aba366ea543741510591fbf64cd60d"
                    )
                    .unwrap(),
                },
            )),
        );
    }
);

test_contract_call_response!(
    test_sha256_uint,
    "hashes",
    "sha256-unsigned",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::Sequence(clarity::vm::types::SequenceData::Buffer(
                clarity::vm::types::BuffData {
                    data: Vec::from_hex(
                        "3c9f0d5d10486e680b92df0124aaa55ec061c7684e5e67241b44ed42a323aa5b"
                    )
                    .unwrap(),
                },
            )),
        );
    }
);

test_contract_call_response!(
    test_hash160_buffer,
    "hashes",
    "hash160-buffer",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::Sequence(clarity::vm::types::SequenceData::Buffer(
                clarity::vm::types::BuffData {
                    data: Vec::from_hex("d6f2b43388048a339abd861be2babd817e3717cd").unwrap(),
                },
            )),
        );
    }
);

test_contract_call_response!(
    test_hash160_int,
    "hashes",
    "hash160-integer",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::Sequence(clarity::vm::types::SequenceData::Buffer(
                clarity::vm::types::BuffData {
                    data: Vec::from_hex("9b85445a5562baee1c22211ac662e1c580006ca7").unwrap(),
                },
            )),
        );
    }
);

test_contract_call_response!(
    test_hash160_uint,
    "hashes",
    "hash160-unsigned",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::Sequence(clarity::vm::types::SequenceData::Buffer(
                clarity::vm::types::BuffData {
                    data: Vec::from_hex("105ba6e56008b7de1c41f752db695fca0588f530").unwrap(),
                },
            )),
        );
    }
);

// These tests are disabled because they require a block to be present in the
// chain, which is not the case when running the tests. Once the test framework
// supports this, these tests can be re-enabled.

test_contract_call_response!(
    test_gbi_non_existent,
    "get-block-info",
    "non-existent",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::none());
    }
);

// test_contract_call_response!(
//     test_gbi_bhh,
//     "get-block-info",
//     "get-burnchain-header-hash",
//     |response: ResponseData| {
//         assert!(response.committed);
//         assert_eq!(
//             *response.data,
//             Value::some(Value::buff_from(vec![0u8; 32]).unwrap()).unwrap()
//         );
//     }
// );

// test_contract_call_response!(
//     test_gbi_id_hh,
//     "get-block-info",
//     "get-id-header-hash",
//     |response: ResponseData| {
//         assert!(response.committed);
//         assert_eq!(
//             *response.data,
//             Value::some(Value::buff_from(vec![0u8; 32]).unwrap()).unwrap()
//         );
//     }
// );

// test_contract_call_response!(
//     test_gbi_hh,
//     "get-block-info",
//     "get-header-hash",
//     |response: ResponseData| {
//         assert!(response.committed);
//         assert_eq!(
//             *response.data,
//             Value::some(Value::buff_from(vec![0u8; 32]).unwrap()).unwrap()
//         );
//     }
// );

// test_contract_call_response!(
//     test_gbi_miner_address,
//     "get-block-info",
//     "get-miner-address",
//     |response: ResponseData| {
//         assert!(response.committed);
//         assert_eq!(
//             *response.data,
//             Value::some(StandardPrincipalData::transient().into()).unwrap()
//         );
//     }
// );

// test_contract_call_response!(
//     test_gbi_time,
//     "get-block-info",
//     "get-time",
//     |response: ResponseData| {
//         assert!(response.committed);
//         assert_eq!(*response.data, Value::some(Value::UInt(42)).unwrap());
//     }
// );

// test_contract_call_response!(
//     test_gbi_block_reward,
//     "get-block-info",
//     "get-block-reward",
//     |response: ResponseData| {
//         assert!(response.committed);
//         assert_eq!(*response.data, Value::some(Value::UInt(0)).unwrap());
//     }
// );

test_contract_call_response!(
    test_gbi_miner_spend_total,
    "get-block-info",
    "get-miner-spend-total",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::some(Value::UInt(0)).unwrap());
    }
);

test_contract_call_response!(
    test_gbi_miner_spend_winner,
    "get-block-info",
    "get-miner-spend-winner",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::some(Value::UInt(0)).unwrap());
    }
);

test_multi_contract_call_response!(
    test_contract_call_no_args,
    ["contract-callee", "multi-contract/contract-caller"],
    "contract-caller",
    "no-args",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::UInt(42));
    }
);

test_multi_contract_call_response!(
    test_contract_call_one_simple_arg,
    ["contract-callee", "multi-contract/contract-caller"],
    "contract-caller",
    "one-simple-arg",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Int(17));
    }
);

test_multi_contract_call_response!(
    test_contract_call_one_arg,
    ["contract-callee", "multi-contract/contract-caller"],
    "contract-caller",
    "one-arg",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::string_ascii_from_bytes("hello".to_string().into_bytes()).unwrap()
        );
    }
);

test_multi_contract_call_response!(
    test_contract_call_two_simple_args,
    ["contract-callee", "multi-contract/contract-caller"],
    "contract-caller",
    "two-simple-args",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Int(42 + 17),);
    }
);

test_multi_contract_call_response!(
    test_contract_call_two_args,
    ["contract-callee", "multi-contract/contract-caller"],
    "contract-caller",
    "two-args",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::string_ascii_from_bytes("hello world".to_string().into_bytes()).unwrap()
        );
    }
);

test_contract_call_response_events!(
    test_print_int,
    "print",
    "print-int",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Int(12345));
    },
    |event_batches: &Vec<EventBatch>| {
        assert_eq!(event_batches.len(), 1);
        assert_eq!(event_batches[0].events.len(), 1);
        if let StacksTransactionEvent::SmartContractEvent(event) = &event_batches[0].events[0] {
            let (ref contract, ref label) = &event.key;
            assert_eq!(
                contract,
                &QualifiedContractIdentifier::local("print").unwrap()
            );
            assert_eq!(label, "print");
            assert_eq!(event.value, Value::Int(12345));
        } else {
            panic!("Unexpected event received from Wasm function call.");
        }
    }
);

test_contract_call_response_events!(
    test_print_uint,
    "print",
    "print-uint",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::UInt(98765));
    },
    |event_batches: &Vec<EventBatch>| {
        assert_eq!(event_batches.len(), 1);
        assert_eq!(event_batches[0].events.len(), 1);
        if let StacksTransactionEvent::SmartContractEvent(event) = &event_batches[0].events[0] {
            let (ref contract, ref label) = &event.key;
            assert_eq!(
                contract,
                &QualifiedContractIdentifier::local("print").unwrap()
            );
            assert_eq!(label, "print");
            assert_eq!(event.value, Value::UInt(98765));
        } else {
            panic!("Unexpected event received from Wasm function call.");
        }
    }
);

test_contract_call_response_events!(
    test_print_standard_principal,
    "print",
    "print-standard-principal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::Principal(
                PrincipalData::parse("ST1PQHQKV0RJXZFY1DGX8MNSNYVE3VGZJSRTPGZGM").unwrap()
            )
        );
    },
    |event_batches: &Vec<EventBatch>| {
        assert_eq!(event_batches.len(), 1);
        assert_eq!(event_batches[0].events.len(), 1);
        if let StacksTransactionEvent::SmartContractEvent(event) = &event_batches[0].events[0] {
            let (ref contract, ref label) = &event.key;
            assert_eq!(
                contract,
                &QualifiedContractIdentifier::local("print").unwrap()
            );
            assert_eq!(label, "print");
            assert_eq!(
                event.value,
                Value::Principal(
                    PrincipalData::parse("ST1PQHQKV0RJXZFY1DGX8MNSNYVE3VGZJSRTPGZGM").unwrap()
                )
            );
        } else {
            panic!("Unexpected event received from Wasm function call.");
        }
    }
);

test_contract_call_response_events!(
    test_print_contract_principal,
    "print",
    "print-contract-principal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::Principal(
                PrincipalData::parse("ST1PQHQKV0RJXZFY1DGX8MNSNYVE3VGZJSRTPGZGM.foo").unwrap()
            )
        );
    },
    |event_batches: &Vec<EventBatch>| {
        assert_eq!(event_batches.len(), 1);
        assert_eq!(event_batches[0].events.len(), 1);
        if let StacksTransactionEvent::SmartContractEvent(event) = &event_batches[0].events[0] {
            let (ref contract, ref label) = &event.key;
            assert_eq!(
                contract,
                &QualifiedContractIdentifier::local("print").unwrap()
            );
            assert_eq!(label, "print");
            assert_eq!(
                event.value,
                Value::Principal(
                    PrincipalData::parse("ST1PQHQKV0RJXZFY1DGX8MNSNYVE3VGZJSRTPGZGM.foo").unwrap()
                )
            );
        } else {
            panic!("Unexpected event received from Wasm function call.");
        }
    }
);

test_contract_call_response_events!(
    test_print_response_ok_int,
    "print",
    "print-response-ok-int",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Int(12345));
    },
    |event_batches: &Vec<EventBatch>| {
        assert_eq!(event_batches.len(), 1);
        assert_eq!(event_batches[0].events.len(), 1);
        if let StacksTransactionEvent::SmartContractEvent(event) = &event_batches[0].events[0] {
            let (ref contract, ref label) = &event.key;
            assert_eq!(
                contract,
                &QualifiedContractIdentifier::local("print").unwrap()
            );
            assert_eq!(label, "print");
            assert_eq!(event.value, Value::okay(Value::Int(12345)).unwrap());
        } else {
            panic!("Unexpected event received from Wasm function call.");
        }
    }
);

test_contract_call_response_events!(
    test_print_response_err_uint,
    "print",
    "print-response-err-uint",
    |response: ResponseData| {
        assert!(!response.committed);
        assert_eq!(*response.data, Value::UInt(98765));
    },
    |event_batches: &Vec<EventBatch>| {
        assert_eq!(event_batches.len(), 1);
        assert_eq!(event_batches[0].events.len(), 1);
        if let StacksTransactionEvent::SmartContractEvent(event) = &event_batches[0].events[0] {
            let (ref contract, ref label) = &event.key;
            assert_eq!(
                contract,
                &QualifiedContractIdentifier::local("print").unwrap()
            );
            assert_eq!(label, "print");
            assert_eq!(event.value, Value::error(Value::UInt(98765)).unwrap());
        } else {
            panic!("Unexpected event received from Wasm function call.");
        }
    }
);

test_contract_call_response_events!(
    test_print_response_ok_principal,
    "print",
    "print-response-ok-principal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::Principal(
                PrincipalData::parse("ST1PQHQKV0RJXZFY1DGX8MNSNYVE3VGZJSRTPGZGM").unwrap()
            )
        );
    },
    |event_batches: &Vec<EventBatch>| {
        assert_eq!(event_batches.len(), 1);
        assert_eq!(event_batches[0].events.len(), 1);
        if let StacksTransactionEvent::SmartContractEvent(event) = &event_batches[0].events[0] {
            let (ref contract, ref label) = &event.key;
            assert_eq!(
                contract,
                &QualifiedContractIdentifier::local("print").unwrap()
            );
            assert_eq!(label, "print");
            assert_eq!(
                event.value,
                Value::okay(Value::Principal(
                    PrincipalData::parse("ST1PQHQKV0RJXZFY1DGX8MNSNYVE3VGZJSRTPGZGM").unwrap()
                ))
                .unwrap()
            );
        } else {
            panic!("Unexpected event received from Wasm function call.");
        }
    }
);

test_contract_call_response_events!(
    test_print_response_err_principal,
    "print",
    "print-response-err-principal",
    |response: ResponseData| {
        assert!(!response.committed);
        assert_eq!(
            *response.data,
            Value::Principal(
                PrincipalData::parse("ST1PQHQKV0RJXZFY1DGX8MNSNYVE3VGZJSRTPGZGM").unwrap()
            )
        );
    },
    |event_batches: &Vec<EventBatch>| {
        assert_eq!(event_batches.len(), 1);
        assert_eq!(event_batches[0].events.len(), 1);
        if let StacksTransactionEvent::SmartContractEvent(event) = &event_batches[0].events[0] {
            let (ref contract, ref label) = &event.key;
            assert_eq!(
                contract,
                &QualifiedContractIdentifier::local("print").unwrap()
            );
            assert_eq!(label, "print");
            assert_eq!(
                event.value,
                Value::error(Value::Principal(
                    PrincipalData::parse("ST1PQHQKV0RJXZFY1DGX8MNSNYVE3VGZJSRTPGZGM").unwrap()
                ))
                .unwrap()
            );
        } else {
            panic!("Unexpected event received from Wasm function call.");
        }
    }
);

test_contract_call_response_events!(
    test_print_true,
    "print",
    "print-true",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    },
    |event_batches: &Vec<EventBatch>| {
        assert_eq!(event_batches.len(), 1);
        assert_eq!(event_batches[0].events.len(), 1);
        if let StacksTransactionEvent::SmartContractEvent(event) = &event_batches[0].events[0] {
            let (ref contract, ref label) = &event.key;
            assert_eq!(
                contract,
                &QualifiedContractIdentifier::local("print").unwrap()
            );
            assert_eq!(label, "print");
            assert_eq!(event.value, Value::Bool(true));
        } else {
            panic!("Unexpected event received from Wasm function call.");
        }
    }
);

test_contract_call_response_events!(
    test_print_false,
    "print",
    "print-false",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    },
    |event_batches: &Vec<EventBatch>| {
        assert_eq!(event_batches.len(), 1);
        assert_eq!(event_batches[0].events.len(), 1);
        if let StacksTransactionEvent::SmartContractEvent(event) = &event_batches[0].events[0] {
            let (ref contract, ref label) = &event.key;
            assert_eq!(
                contract,
                &QualifiedContractIdentifier::local("print").unwrap()
            );
            assert_eq!(label, "print");
            assert_eq!(event.value, Value::Bool(false));
        } else {
            panic!("Unexpected event received from Wasm function call.");
        }
    }
);

test_contract_call_response_events!(
    test_print_none,
    "print",
    "print-none",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::none());
    },
    |event_batches: &Vec<EventBatch>| {
        assert_eq!(event_batches.len(), 1);
        assert_eq!(event_batches[0].events.len(), 1);
        if let StacksTransactionEvent::SmartContractEvent(event) = &event_batches[0].events[0] {
            let (ref contract, ref label) = &event.key;
            assert_eq!(
                contract,
                &QualifiedContractIdentifier::local("print").unwrap()
            );
            assert_eq!(label, "print");
            assert_eq!(event.value, Value::none());
        } else {
            panic!("Unexpected event received from Wasm function call.");
        }
    }
);

test_contract_call_response_events!(
    test_print_some,
    "print",
    "print-some",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::some(Value::Int(42)).unwrap());
    },
    |event_batches: &Vec<EventBatch>| {
        assert_eq!(event_batches.len(), 1);
        assert_eq!(event_batches[0].events.len(), 1);
        if let StacksTransactionEvent::SmartContractEvent(event) = &event_batches[0].events[0] {
            let (ref contract, ref label) = &event.key;
            assert_eq!(
                contract,
                &QualifiedContractIdentifier::local("print").unwrap()
            );
            assert_eq!(label, "print");
            assert_eq!(event.value, Value::some(Value::Int(42)).unwrap());
        } else {
            panic!("Unexpected event received from Wasm function call.");
        }
    }
);

test_contract_call_response_events!(
    test_print_list,
    "print",
    "print-list",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::cons_list_unsanitized(vec![Value::Int(1), Value::Int(2), Value::Int(3)])
                .unwrap()
        );
    },
    |event_batches: &Vec<EventBatch>| {
        assert_eq!(event_batches.len(), 1);
        assert_eq!(event_batches[0].events.len(), 1);
        if let StacksTransactionEvent::SmartContractEvent(event) = &event_batches[0].events[0] {
            let (ref contract, ref label) = &event.key;
            assert_eq!(
                contract,
                &QualifiedContractIdentifier::local("print").unwrap()
            );
            assert_eq!(label, "print");
            assert_eq!(
                event.value,
                Value::cons_list_unsanitized(vec![Value::Int(1), Value::Int(2), Value::Int(3)])
                    .unwrap()
            );
        } else {
            panic!("Unexpected event received from Wasm function call.");
        }
    }
);

test_contract_call_response_events!(
    test_print_list_principals,
    "print",
    "print-list-principals",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::cons_list_unsanitized(vec![
                Value::Principal(
                    PrincipalData::parse("ST1PQHQKV0RJXZFY1DGX8MNSNYVE3VGZJSRTPGZGM").unwrap()
                ),
                Value::Principal(
                    PrincipalData::parse("ST1PQHQKV0RJXZFY1DGX8MNSNYVE3VGZJSRTPGZGM.contract")
                        .unwrap()
                )
            ])
            .unwrap()
        );
    },
    |event_batches: &Vec<EventBatch>| {
        assert_eq!(event_batches.len(), 1);
        assert_eq!(event_batches[0].events.len(), 1);
        if let StacksTransactionEvent::SmartContractEvent(event) = &event_batches[0].events[0] {
            let (ref contract, ref label) = &event.key;
            assert_eq!(
                contract,
                &QualifiedContractIdentifier::local("print").unwrap()
            );
            assert_eq!(label, "print");
            assert_eq!(
                event.value,
                Value::cons_list_unsanitized(vec![
                    Value::Principal(
                        PrincipalData::parse("ST1PQHQKV0RJXZFY1DGX8MNSNYVE3VGZJSRTPGZGM").unwrap()
                    ),
                    Value::Principal(
                        PrincipalData::parse("ST1PQHQKV0RJXZFY1DGX8MNSNYVE3VGZJSRTPGZGM.contract")
                            .unwrap()
                    )
                ])
                .unwrap()
            );
        } else {
            panic!("Unexpected event received from Wasm function call.");
        }
    }
);

test_contract_call_response_events!(
    test_print_list_empty,
    "print",
    "print-list-empty",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::cons_list_unsanitized(vec![]).unwrap()
        );
    },
    |event_batches: &Vec<EventBatch>| {
        assert_eq!(event_batches.len(), 1);
        assert_eq!(event_batches[0].events.len(), 1);
        if let StacksTransactionEvent::SmartContractEvent(event) = &event_batches[0].events[0] {
            let (ref contract, ref label) = &event.key;
            assert_eq!(
                contract,
                &QualifiedContractIdentifier::local("print").unwrap()
            );
            assert_eq!(label, "print");
            assert_eq!(event.value, Value::cons_list_unsanitized(vec![]).unwrap());
        } else {
            panic!("Unexpected event received from Wasm function call.");
        }
    }
);

test_contract_call_response_events!(
    test_print_buffer,
    "print",
    "print-buffer",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::buff_from(vec![0xde, 0xad, 0xbe, 0xef]).unwrap()
        );
    },
    |event_batches: &Vec<EventBatch>| {
        assert_eq!(event_batches.len(), 1);
        assert_eq!(event_batches[0].events.len(), 1);
        if let StacksTransactionEvent::SmartContractEvent(event) = &event_batches[0].events[0] {
            let (ref contract, ref label) = &event.key;
            assert_eq!(
                contract,
                &QualifiedContractIdentifier::local("print").unwrap()
            );
            assert_eq!(label, "print");
            assert_eq!(
                event.value,
                Value::buff_from(vec![0xde, 0xad, 0xbe, 0xef]).unwrap()
            );
        } else {
            panic!("Unexpected event received from Wasm function call.");
        }
    }
);

test_contract_call_response_events!(
    test_print_buffer_empty,
    "print",
    "print-buffer-empty",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::buff_from(vec![]).unwrap());
    },
    |event_batches: &Vec<EventBatch>| {
        assert_eq!(event_batches.len(), 1);
        assert_eq!(event_batches[0].events.len(), 1);
        if let StacksTransactionEvent::SmartContractEvent(event) = &event_batches[0].events[0] {
            let (ref contract, ref label) = &event.key;
            assert_eq!(
                contract,
                &QualifiedContractIdentifier::local("print").unwrap()
            );
            assert_eq!(label, "print");
            assert_eq!(event.value, Value::buff_from(vec![]).unwrap());
        } else {
            panic!("Unexpected event received from Wasm function call.");
        }
    }
);

test_contract_call_response_events!(
    test_print_side_effect,
    "print",
    "print-side-effect",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::UInt(1));
    },
    |event_batches: &Vec<EventBatch>| {
        assert_eq!(event_batches.len(), 1);
        assert_eq!(event_batches[0].events.len(), 1);
        if let StacksTransactionEvent::SmartContractEvent(event) = &event_batches[0].events[0] {
            let (ref contract, ref label) = &event.key;
            assert_eq!(
                contract,
                &QualifiedContractIdentifier::local("print").unwrap()
            );
            assert_eq!(label, "print");
            assert_eq!(event.value, Value::Bool(true));
        } else {
            panic!("Unexpected event received from Wasm function call.");
        }
    }
);

test_contract_call_response_events!(
    test_print_string_utf8,
    "print",
    "print-string-utf8",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::string_utf8_from_bytes("helŁo world 愛🦊".into()).unwrap()
        );
    },
    |event_batches: &Vec<EventBatch>| {
        assert_eq!(event_batches.len(), 1);
        assert_eq!(event_batches[0].events.len(), 1);
        if let StacksTransactionEvent::SmartContractEvent(event) = &event_batches[0].events[0] {
            let (ref contract, ref label) = &event.key;
            assert_eq!(
                contract,
                &QualifiedContractIdentifier::local("print").unwrap()
            );
            assert_eq!(label, "print");
            assert_eq!(
                event.value,
                Value::string_utf8_from_bytes("helŁo world 愛🦊".into()).unwrap()
            );
        } else {
            panic!("Unexpected event received from Wasm function call.");
        }
    }
);

test_contract_call_response_events!(
    test_print_string_ascii,
    "print",
    "print-string-ascii",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::string_ascii_from_bytes("hello world".to_string().into_bytes()).unwrap()
        );
    },
    |event_batches: &Vec<EventBatch>| {
        assert_eq!(event_batches.len(), 1);
        assert_eq!(event_batches[0].events.len(), 1);
        if let StacksTransactionEvent::SmartContractEvent(event) = &event_batches[0].events[0] {
            let (ref contract, ref label) = &event.key;
            assert_eq!(
                contract,
                &QualifiedContractIdentifier::local("print").unwrap()
            );
            assert_eq!(label, "print");
            assert_eq!(
                event.value,
                Value::string_ascii_from_bytes("hello world".to_string().into_bytes()).unwrap()
            );
        } else {
            panic!("Unexpected event received from Wasm function call.");
        }
    }
);

test_contract_call_response_events!(
    test_print_string_ascii_empty,
    "print",
    "print-string-ascii-empty",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::string_ascii_from_bytes(vec![]).unwrap()
        );
    },
    |event_batches: &Vec<EventBatch>| {
        assert_eq!(event_batches.len(), 1);
        assert_eq!(event_batches[0].events.len(), 1);
        if let StacksTransactionEvent::SmartContractEvent(event) = &event_batches[0].events[0] {
            let (ref contract, ref label) = &event.key;
            assert_eq!(
                contract,
                &QualifiedContractIdentifier::local("print").unwrap()
            );
            assert_eq!(label, "print");
            assert_eq!(event.value, Value::string_ascii_from_bytes(vec![]).unwrap());
        } else {
            panic!("Unexpected event received from Wasm function call.");
        }
    }
);

test_contract_call_response_events!(
    test_print_tuple,
    "print",
    "print-tuple",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::Tuple(
                TupleData::from_data(vec![
                    ("key1".into(), Value::Int(1)),
                    ("key2".into(), Value::Bool(true))
                ])
                .unwrap()
            )
        );
    },
    |event_batches: &Vec<EventBatch>| {
        assert_eq!(event_batches.len(), 1);
        assert_eq!(event_batches[0].events.len(), 1);
        if let StacksTransactionEvent::SmartContractEvent(event) = &event_batches[0].events[0] {
            let (ref contract, ref label) = &event.key;
            assert_eq!(
                contract,
                &QualifiedContractIdentifier::local("print").unwrap()
            );
            assert_eq!(label, "print");
            assert_eq!(
                event.value,
                Value::Tuple(
                    TupleData::from_data(vec![
                        ("key1".into(), Value::Int(1)),
                        ("key2".into(), Value::Bool(true))
                    ])
                    .unwrap()
                )
            );
        } else {
            panic!("Unexpected event received from Wasm function call.");
        }
    }
);

test_contract_call_response!(test_tuple, "tuple", "simple", |response: ResponseData| {
    assert!(response.committed);
    assert_eq!(
        *response.data,
        Value::Tuple(
            TupleData::from_data(vec![
                ("a".into(), Value::Int(1)),
                ("b".into(), Value::UInt(2))
            ])
            .unwrap()
        )
    );
});

test_contract_call_response!(
    test_tuple_out_of_order,
    "tuple",
    "out-of-order",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::Tuple(
                TupleData::from_data(vec![
                    ("a".into(), Value::Int(1)),
                    ("b".into(), Value::UInt(2))
                ])
                .unwrap()
            )
        );
    }
);

test_contract_call_response!(
    test_tuple_list_syntax,
    "tuple",
    "list-syntax",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::Tuple(
                TupleData::from_data(vec![
                    ("a".into(), Value::Int(1)),
                    ("b".into(), Value::UInt(2))
                ])
                .unwrap()
            )
        );
    }
);

test_contract_call_response!(
    test_tuple_strings,
    "tuple",
    "strings",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::Tuple(
                TupleData::from_data(vec![
                    (
                        "one".into(),
                        Value::string_ascii_from_bytes("one".to_string().into_bytes()).unwrap()
                    ),
                    (
                        "two".into(),
                        Value::string_ascii_from_bytes("two".to_string().into_bytes()).unwrap()
                    ),
                    (
                        "three".into(),
                        Value::string_ascii_from_bytes("three".to_string().into_bytes()).unwrap()
                    )
                ])
                .unwrap()
            )
        );
    }
);

test_contract_call_response!(
    test_tuple_nested,
    "tuple",
    "nested",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::Tuple(
                TupleData::from_data(vec![
                    ("a".into(), Value::Int(1)),
                    (
                        "b".into(),
                        Value::Tuple(
                            TupleData::from_data(vec![
                                ("c".into(), Value::Int(2)),
                                ("d".into(), Value::Int(3))
                            ])
                            .unwrap()
                        )
                    )
                ])
                .unwrap()
            )
        );
    }
);

test_contract_call_response!(
    test_tuple_get_first,
    "tuple",
    "get-first",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Int(42));
    }
);

test_contract_call_response!(
    test_tuple_get_last,
    "tuple",
    "get-last",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::string_ascii_from_bytes(
                "Great ideas often receive violent opposition from mediocre minds."
                    .to_string()
                    .into_bytes()
            )
            .unwrap()
        );
    }
);

test_contract_call_response!(
    test_tuple_get_only,
    "tuple",
    "get-only",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::buff_from(0x12345678i32.to_be_bytes().to_vec()).unwrap()
        );
    }
);

test_contract_call_response!(
    test_tuple_merge,
    "tuple",
    "tuple-merge",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::Tuple(
                TupleData::from_data(vec![
                    ("a".into(), Value::Int(1)),
                    ("b".into(), Value::Bool(false))
                ])
                .unwrap()
            )
        );
    }
);

test_contract_call_response!(
    test_tuple_merge_multiple,
    "tuple",
    "tuple-merge-multiple",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::Tuple(
                TupleData::from_data(vec![
                    ("a".into(), Value::Int(1)),
                    (
                        "b".into(),
                        Value::string_ascii_from_bytes("ok".to_string().into_bytes()).unwrap()
                    ),
                    ("c".into(), Value::Bool(false)),
                    ("d".into(), Value::buff_from(vec![]).unwrap())
                ])
                .unwrap()
            )
        );
    }
);

test_contract_call_response!(
    test_tuple_merge_overwrite,
    "tuple",
    "tuple-merge-overwrite",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::Tuple(
                TupleData::from_data(vec![
                    ("a".into(), Value::UInt(42)),
                    (
                        "b".into(),
                        Value::string_ascii_from_bytes("goodbye".to_string().into_bytes()).unwrap()
                    )
                ])
                .unwrap()
            )
        );
    }
);

test_contract_call_response!(
    test_buff_to_uint_be,
    "buffer-to-integer",
    "buff_to_uint_be",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::UInt(171643470492608469511538647592439832082)
        )
    }
);

test_contract_call_response!(
    test_buff_to_int_be,
    "buffer-to-integer",
    "buff_to_int_be",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::Int(-168638896428329993951835959839328379374),
        )
    }
);

test_contract_call_response!(
    test_buff_to_uint_le,
    "buffer-to-integer",
    "buff_to_uint_le",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::UInt(25079978013418778635005664149300846977)
        )
    }
);

test_contract_call_response!(
    test_buff_to_int_le,
    "buffer-to-integer",
    "buff_to_int_le",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::Int(25079978013418778635005664149300846977),
        )
    }
);

test_contract_call_response!(
    test_not_false,
    "not",
    "assert-truthy",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_not_true,
    "not",
    "assert-falsy",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(test_xor_int, "xor", "xor-int", |response: ResponseData| {
    assert!(response.committed);
    assert_eq!(*response.data, Value::Int(9));
});

test_contract_call_response!(
    test_xor_uint,
    "xor",
    "xor-uint",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::UInt(14));
    }
);

test_contract_call_response!(
    test_xor_neg_int,
    "xor",
    "xor-neg-int",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Int(7));
    }
);

test_contract_call_response!(
    test_one_int_equality,
    "equal",
    "one-int-equal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_one_uint_equality,
    "equal",
    "one-uint-equal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_zero_int_equality,
    "equal",
    "two-zero-int-equal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_zero_uint_equality,
    "equal",
    "two-zero-uint-equal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_two_int_equality,
    "equal",
    "two-int-equal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_two_uint_equality,
    "equal",
    "two-uint-equal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_two_int_unequality,
    "equal",
    "two-int-unequal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_two_uint_unequality,
    "equal",
    "two-uint-unequal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_int_equality,
    "equal",
    "int-equal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_uint_equality,
    "equal",
    "uint-equal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_int_unequality,
    "equal",
    "int-unequal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_int_unequality_2,
    "equal",
    "int-unequal-2",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_uint_unequality,
    "equal",
    "uint-unequal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_uint_unequality_2,
    "equal",
    "uint-unequal-2",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_buffer_equal,
    "equal",
    "buf-equal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_buffer_equal_2,
    "equal",
    "buf-equal-2",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_buffer_unequal,
    "equal",
    "buf-unequal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_buffer_unequal_2,
    "equal",
    "buf-unequal-2",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_buffer_unequal_3,
    "equal",
    "buf-unequal-3",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_str_ascii_equal,
    "equal",
    "str-ascii-equal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_str_ascii_unequal,
    "equal",
    "str-ascii-unequal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_str_utf8_equal,
    "equal",
    "str-utf8-equal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_str_utf8_unequal,
    "equal",
    "str-utf8-unequal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_principal_equal,
    "equal",
    "principal-equal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_principal_unequal,
    "equal",
    "principal-unequal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_call_principal_equal,
    "equal",
    "call-principal-equal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_call_principal_unequal,
    "equal",
    "call-principal-unequal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_call_principal_unequal_2,
    "equal",
    "call-principal-unequal-2",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_call_optional_equal,
    "equal",
    "call-optional-equal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_call_optional_none_equal,
    "equal",
    "call-optional-none-equal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_call_optional_unequal,
    "equal",
    "call-optional-unequal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_call_optional_some_and_none_unequal,
    "equal",
    "call-optional-some-and-none-unequal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_call_response_ok_equal,
    "equal",
    "call-response-ok-equal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_call_response_err_equal,
    "equal",
    "call-response-err-equal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_call_response_ok_err_unequal,
    "equal",
    "call-response-ok-err-unequal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_call_response_ok_unequal,
    "equal",
    "call-response-ok-unequal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_call_response_err_unequal,
    "equal",
    "call-response-err-unequal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_call_response_ok_err_same_value_unequal,
    "equal",
    "call-response-ok-err-same-value-unequal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_call_one_tuple_equal,
    "equal",
    "call-one-tuple-equal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_call_one_tuple_unequal,
    "equal",
    "call-one-tuple-unequal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_call_tuple_equal,
    "equal",
    "call-tuple-equal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_call_tuple_unequal,
    "equal",
    "call-tuple-unequal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_call_big_tuple_equal,
    "equal",
    "call-big-tuple-equal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_call_big_tuple_slightly_unequal,
    "equal",
    "call-big-tuple-slightly-unequal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_call_big_tuple_unequal,
    "equal",
    "call-big-tuple-unequal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_call_tuple_recursive_equal,
    "equal",
    "call-tuple-recursive-equal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_call_tuple_recursive_unequal,
    "equal",
    "call-tuple-recursive-unequal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_call_list_int_equal,
    "equal",
    "call-list-int-equal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_call_list_str_equal,
    "equal",
    "call-list-str-equal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_call_list_unequal_length,
    "equal",
    "call-list-unequal-length",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_call_list_unequal_length_2,
    "equal",
    "call-list-unequal-length-2",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_call_list_unequal_first_element,
    "equal",
    "call-list-unequal-first-element",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_call_list_unequal_mid_element,
    "equal",
    "call-list-unequal-mid-element",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_call_list_unequal_last_element,
    "equal",
    "call-list-unequal-last-element",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_call_bool_equal,
    "equal",
    "call-bool-equal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_call_bool_unequal,
    "equal",
    "call-bool-unequal",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_append,
    "sequences",
    "list-append",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::cons_list_unsanitized(vec![Value::Int(1), Value::Int(2), Value::Int(3)])
                .unwrap()
        );
    }
);

test_contract_call_response!(
    test_append_strings,
    "sequences",
    "list-append-strings",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::cons_list_unsanitized(vec![
                Value::string_ascii_from_bytes("hello".to_string().into_bytes()).unwrap(),
                Value::string_ascii_from_bytes("world".to_string().into_bytes()).unwrap(),
                Value::string_ascii_from_bytes("!".to_string().into_bytes()).unwrap(),
            ])
            .unwrap()
        );
    }
);

test_contract_call_response!(
    test_append_empty,
    "sequences",
    "list-append-empty",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::cons_list_unsanitized(vec![Value::Bool(true)]).unwrap()
        );
    }
);

test_contract_call_response!(
    test_list_as_max_len_some,
    "sequences",
    "list-as-max-len-some",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::some(Value::cons_list_unsanitized(vec![Value::Int(1), Value::Int(2)]).unwrap())
                .unwrap()
        );
    }
);

test_contract_call_response!(
    test_list_as_max_len_none,
    "sequences",
    "list-as-max-len-none",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::none());
    }
);

test_contract_call_response!(
    test_list_as_max_len_empty,
    "sequences",
    "list-as-max-len-empty",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::some(Value::cons_list_unsanitized(vec![]).unwrap()).unwrap()
        );
    }
);

test_contract_call_response!(
    test_buffer_as_max_len,
    "sequences",
    "buffer-as-max-len",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::some(Value::buff_from(vec![0x12, 0x34, 0x56]).unwrap()).unwrap()
        );
    }
);

test_contract_call_response!(
    test_string_as_max_len,
    "sequences",
    "string-as-max-len",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::some(Value::string_ascii_from_bytes("hello".to_string().into_bytes()).unwrap())
                .unwrap()
        );
    }
);

test_contract_call_response!(
    test_string_utf8_as_max_len,
    "sequences",
    "string-utf8-as-max-len",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::some(Value::string_utf8_from_bytes("hello🦊".into()).unwrap()).unwrap()
        );
    }
);

test_contract_call_response!(
    test_list_concat,
    "sequences",
    "list-concat",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::cons_list_unsanitized(vec![
                Value::Int(1),
                Value::Int(2),
                Value::Int(3),
                Value::Int(4)
            ])
            .unwrap()
        );
    }
);

test_contract_call_response!(
    test_string_concat,
    "sequences",
    "string-concat",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::string_ascii_from_bytes("hello world".to_string().into_bytes()).unwrap()
        );
    }
);

test_contract_call_response!(
    test_string_utf8_concat,
    "sequences",
    "string-utf8-concat",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::string_utf8_from_bytes("hello world".into()).unwrap()
        );
    }
);

test_contract_call_response!(
    test_string_utf8_concat_b,
    "sequences",
    "string-utf8-concat-b",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::string_utf8_from_bytes("hello world🦊".into()).unwrap()
        );
    }
);

test_contract_call_response!(
    test_buffer_concat,
    "sequences",
    "buffer-concat",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::buff_from(vec![0x12, 0x34, 0x56, 0x78, 0x9a, 0xbc]).unwrap()
        );
    }
);

test_contract_call_response!(
    test_list_len,
    "sequences",
    "list-len",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::UInt(3));
    }
);

test_contract_call_response!(
    test_string_len,
    "sequences",
    "string-len",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::UInt(3));
    }
);

test_contract_call_response!(
    test_string_utf8_len,
    "sequences",
    "string-utf8-len",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::UInt(3));
    }
);

test_contract_call_response!(
    test_string_utf8_len_b,
    "sequences",
    "string-utf8-len-b",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::UInt(4));
    }
);

test_contract_call_response!(
    test_buffer_len,
    "sequences",
    "buffer-len",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::UInt(3));
    }
);

test_contract_call_response!(
    test_list_len_0,
    "sequences",
    "list-len-0",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::UInt(0));
    }
);

test_contract_call_response!(
    test_string_len_0,
    "sequences",
    "string-len-0",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::UInt(0));
    }
);

test_contract_call_response!(
    test_buffer_len_0,
    "sequences",
    "buffer-len-0",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::UInt(0));
    }
);

test_contract_call_response!(
    test_list_element_at,
    "sequences",
    "list-element-at",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::some(Value::Int(2)).unwrap());
    }
);

test_contract_call_response!(
    test_string_element_at,
    "sequences",
    "string-element-at",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::some(Value::string_ascii_from_bytes(vec![b'o']).unwrap()).unwrap()
        );
    }
);

test_contract_call_response!(
    test_string_utf8_element_at,
    "sequences",
    "string-utf8-element-at",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::some(Value::string_utf8_from_bytes(vec![b'o']).unwrap()).unwrap()
        );
    }
);

test_contract_call_response!(
    test_buffer_element_at,
    "sequences",
    "buffer-element-at",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::some(Value::buff_from_byte(0x56)).unwrap()
        );
    }
);

test_contract_call_response!(
    test_list_element_at_alias,
    "sequences",
    "list-element-at?",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::some(Value::Int(2)).unwrap());
    }
);

test_contract_call_response!(
    test_string_element_at_alias,
    "sequences",
    "string-element-at?",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::some(Value::string_ascii_from_bytes(vec![b'o']).unwrap()).unwrap()
        );
    }
);

test_contract_call_response!(
    test_string_utf8_element_at_alias,
    "sequences",
    "string-utf8-element-at?",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::some(Value::string_utf8_from_bytes(vec![b'o']).unwrap()).unwrap()
        );
    }
);

test_contract_call_response!(
    test_string_utf8_element_at_alias_b,
    "sequences",
    "string-utf8-element-at-b?",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::some(Value::string_utf8_from_bytes("🦊".into()).unwrap()).unwrap()
        );
    }
);

test_contract_call_response!(
    test_buffer_element_at_alias,
    "sequences",
    "buffer-element-at?",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::some(Value::buff_from_byte(0x56)).unwrap()
        );
    }
);

test_contract_call_response!(
    test_list_element_at_none,
    "sequences",
    "list-element-at-none",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::none());
    }
);

test_contract_call_response!(
    test_string_element_at_none,
    "sequences",
    "string-element-at-none",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::none());
    }
);

test_contract_call_response!(
    test_string_utf8_element_at_none,
    "sequences",
    "string-utf8-element-at-none",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::none());
    }
);

test_contract_call_response!(
    test_buffer_element_at_none,
    "sequences",
    "buffer-element-at-none",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::none());
    }
);

test_contract_call_response!(
    test_element_at_upper_offset,
    "sequences",
    "element-at-upper-offset",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::none());
    }
);

test_contract_call_response!(
    test_list_replace_at,
    "sequences",
    "list-replace-at",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::some(
                Value::cons_list_unsanitized(vec![Value::Int(1), Value::Int(4), Value::Int(3)])
                    .unwrap()
            )
            .unwrap()
        );
    }
);

test_contract_call_response!(
    test_string_replace_at,
    "sequences",
    "string-replace-at",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::some(Value::string_ascii_from_bytes("jello".to_string().into_bytes()).unwrap())
                .unwrap()
        );
    }
);

test_contract_call_response!(
    test_string_utf8_replace_at,
    "sequences",
    "string-utf8-replace-at",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::some(Value::string_utf8_from_bytes("jello".into()).unwrap()).unwrap()
        );
    }
);

test_contract_call_response!(
    test_string_utf8_replace_at_b,
    "sequences",
    "string-utf8-replace-at-b",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::some(Value::string_utf8_from_bytes("heelo🦊".into()).unwrap()).unwrap()
        );
    }
);

test_contract_call_response!(
    test_buffer_replace_at,
    "sequences",
    "buffer-replace-at",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::some(
                Value::buff_from(vec![0xfe, 0xdc, 0xba, 0x98, 0x67, 0x54, 0x32, 0x10]).unwrap()
            )
            .unwrap()
        );
    }
);

test_contract_call_response!(
    test_list_replace_at_none,
    "sequences",
    "list-replace-at-none",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::none());
    }
);

test_contract_call_response!(
    test_string_replace_at_none,
    "sequences",
    "string-replace-at-none",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::none());
    }
);

test_contract_call_response!(
    test_string_utf8_replace_at_none,
    "sequences",
    "string-utf8-replace-at-none",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::none());
    }
);

test_contract_call_response!(
    test_buffer_replace_at_none,
    "sequences",
    "buffer-replace-at-none",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::none());
    }
);

test_contract_call_response!(
    test_replace_at_check_original,
    "sequences",
    "replace-at-check-original",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::some(Value::string_ascii_from_bytes(vec![b'h']).unwrap()).unwrap()
        );
    }
);

test_contract_call_response!(
    test_list_slice,
    "sequences",
    "list-slice",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::some(
                Value::cons_list_unsanitized(vec![Value::Int(2), Value::Int(3), Value::Int(4)])
                    .unwrap()
            )
            .unwrap()
        );
    }
);

test_contract_call_response!(
    test_string_slice,
    "sequences",
    "string-slice",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::some(Value::string_ascii_from_bytes(b"l".to_vec()).unwrap()).unwrap()
        );
    }
);

test_contract_call_response!(
    test_string_utf8_slice,
    "sequences",
    "string-utf8-slice",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::some(Value::string_utf8_from_bytes(b"l".to_vec()).unwrap()).unwrap()
        );
    }
);

test_contract_call_response!(
    test_buffer_slice,
    "sequences",
    "buffer-slice",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::some(Value::buff_from(vec![0x76, 0x54, 0x32]).unwrap()).unwrap()
        );
    }
);

test_contract_call_response!(
    test_list_slice_none,
    "sequences",
    "list-slice-none",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::none());
    }
);

test_contract_call_response!(
    test_string_slice_none,
    "sequences",
    "string-slice-none",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::none());
    }
);

test_contract_call_response!(
    test_string_utf8_slice_none,
    "sequences",
    "string-utf8-slice-none",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::none());
    }
);

test_contract_call_response!(
    test_buffer_slice_none,
    "sequences",
    "buffer-slice-none",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::none());
    }
);

test_contract_call_response!(
    test_list_slice_empty,
    "sequences",
    "list-slice-empty",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::some(Value::cons_list_unsanitized(vec![]).unwrap()).unwrap()
        );
    }
);

test_contract_call_response!(
    test_string_slice_empty,
    "sequences",
    "string-slice-empty",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::some(Value::string_ascii_from_bytes(vec![]).unwrap()).unwrap()
        );
    }
);

test_contract_call_response!(
    test_string_utf8_slice_empty,
    "sequences",
    "string-utf8-slice-empty",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::some(Value::string_utf8_from_bytes(vec![]).unwrap()).unwrap()
        );
    }
);

test_contract_call_response!(
    test_buffer_slice_empty,
    "sequences",
    "buffer-slice-empty",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::some(Value::buff_from(vec![]).unwrap()).unwrap()
        );
    }
);

test_contract_call_response!(
    test_less_than_buffer,
    "cmp-buffer",
    "less-buffer",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_greater_than_buffer,
    "cmp-buffer",
    "greater-buffer",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_less_or_equal_buffer,
    "cmp-buffer",
    "less-or-equal-buffer",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_greater_or_equal_buffer,
    "cmp-buffer",
    "greater-or-equal-buffer",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_less_than_string_ascii,
    "cmp-buffer",
    "less-string-ascii",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_less_than_string_utf8_a,
    "cmp-buffer",
    "less-string-utf8-a",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_less_than_string_utf8_b,
    "cmp-buffer",
    "less-string-utf8-b",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_greater_than_string_ascii,
    "cmp-buffer",
    "greater-string-ascii",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_less_or_equal_string_ascii,
    "cmp-buffer",
    "less-or-equal-string-ascii",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_less_or_equal_string_utf8,
    "cmp-buffer",
    "less-or-equal-string-utf8",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_greater_or_equal_string_ascii,
    "cmp-buffer",
    "greater-or-equal-string-ascii",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_greater_or_equal_string_utf8,
    "cmp-buffer",
    "greater-or-equal-string-utf8",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_less_than_buffer_diff_len,
    "cmp-buffer",
    "less-buffer-diff-len",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_greater_than_buffer_diff_len,
    "cmp-buffer",
    "greater-buffer-diff-len",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_less_or_equal_buffer_diff_len,
    "cmp-buffer",
    "less-or-equal-buffer-diff-len",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_greater_or_equal_buffer_diff_len,
    "cmp-buffer",
    "greater-or-equal-buffer-diff-len",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_less_than_string_ascii_diff_len,
    "cmp-buffer",
    "less-string-ascii-diff-len",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_less_than_string_utf8_diff_len,
    "cmp-buffer",
    "less-string-utf8-diff-len",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_greater_than_string_ascii_diff_len,
    "cmp-buffer",
    "greater-string-ascii-diff-len",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_less_or_equal_string_ascii_diff_len,
    "cmp-buffer",
    "less-or-equal-string-ascii-diff-len",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_greater_or_equal_string_ascii_diff_len,
    "cmp-buffer",
    "greater-or-equal-string-ascii-diff-len",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_less_than_same_buffer,
    "cmp-buffer",
    "less-same-buffer",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_greater_than_same_buffer,
    "cmp-buffer",
    "greater-same-buffer",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_less_or_equal_same_buffer,
    "cmp-buffer",
    "less-or-equal-same-buffer",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_greater_or_equal_same_buffer,
    "cmp-buffer",
    "greater-or-equal-same-buffer",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_less_than_same_string_ascii,
    "cmp-buffer",
    "less-same-string-ascii",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_greater_than_same_string_ascii,
    "cmp-buffer",
    "greater-same-string-ascii",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_less_or_equal_same_string_ascii,
    "cmp-buffer",
    "less-or-equal-same-string-ascii",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_greater_or_equal_same_string_ascii,
    "cmp-buffer",
    "greater-or-equal-same-string-ascii",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_ok_truthy,
    "responses",
    "ok-truthy",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_ok_falsy,
    "responses",
    "ok-falsy",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_err_truthy,
    "responses",
    "err-truthy",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_err_falsy,
    "responses",
    "err-falsy",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_is_some_truthy,
    "options",
    "some-truthy",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_is_some_falsy,
    "options",
    "some-falsy",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_is_none_truthy,
    "options",
    "none-truthy",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(true));
    }
);

test_contract_call_response!(
    test_is_none_falsy,
    "options",
    "none-falsy",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Bool(false));
    }
);

test_contract_call_response!(
    test_let_ints,
    "let",
    "let-ints",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Int(3));
    }
);

test_contract_call_response!(
    test_nested_lets,
    "let",
    "nested-lets",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Int(43));
    }
);

test_contract_call_response!(
    test_let_use_binding,
    "let",
    "let-use-binding",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Int(23));
    }
);

test_contract_call_response!(
    test_default_to_value,
    "default-to",
    "default-to-value",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Int(767));
    }
);

test_contract_call_response!(
    test_default_to_some,
    "default-to",
    "default-to-some",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Int(42));
    }
);

test_contract_call_response!(
    test_default_to_some_string,
    "default-to",
    "default-to-some-string",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::string_ascii_from_bytes(b"C".to_vec()).unwrap()
        );
    }
);

test_contract_call_response!(
    test_default_to_list,
    "default-to",
    "default-to-list",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(
            *response.data,
            Value::cons_list_unsanitized(vec![Value::Int(1), Value::Int(2), Value::Int(3)])
                .unwrap()
        );
    }
);

test_contract_call_response!(
    test_memory_out_of_bounds,
    "memory-oob",
    "memory-out-of-bounds",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Int(1));
    }
);

test_contract_call_response!(
    test_memory_out_of_bounds_runtime,
    "memory-oob-runtime",
    "memory-out-of-bounds-runtime",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::UInt(12));
    }
);

//
// Runtime error tests
//

test_contract_call_error!(
    test_division_by_zero_error,
    "runtime-errors",
    "division-by-zero-error",
    |error: Error| {
        assert_eq!(
            error,
            Error::Runtime(RuntimeErrorType::DivisionByZero, Some(Vec::new()))
        );
    }
);

test_contract_call_error!(
    test_power_argument_error,
    "runtime-errors",
    "power-argument-error",
    |error: Error| {
        assert_eq!(
            error,
            Error::Runtime(
                RuntimeErrorType::Arithmetic(
                    "Power argument to (pow ...) must be a u32 integer".to_string()
                ),
                Some(Vec::new())
            )
        );
    }
);

test_contract_call_error!(
    test_square_root_argument_error,
    "runtime-errors",
    "square-root-argument-error",
    |error: Error| {
        assert_eq!(
            error,
            Error::Runtime(
                RuntimeErrorType::Arithmetic("sqrti must be passed a positive integer".to_string()),
                Some(Vec::new())
            )
        );
    }
);

test_contract_call_error!(
    test_log2_argument_error,
    "runtime-errors",
    "log2-argument-error",
    |error: Error| {
        assert_eq!(
            error,
            Error::Runtime(
                RuntimeErrorType::Arithmetic("log2 must be passed a positive integer".to_string()),
                Some(Vec::new())
            )
        );
    }
);

test_contract_call_error!(
    test_overflow_error,
    "runtime-errors",
    "overflow-error",
    |error: Error| {
        assert_eq!(
            error,
            Error::Runtime(RuntimeErrorType::ArithmeticOverflow, Some(Vec::new()))
        );
    }
);

test_contract_call_error!(
    test_underflow_error,
    "runtime-errors",
    "underflow-error",
    |error: Error| {
        assert_eq!(
            error,
            Error::Runtime(RuntimeErrorType::ArithmeticUnderflow, Some(Vec::new()))
        );
    }
);

test_contract_call_error!(
    test_root_cause_error_case,
    "root-cause-error-case",
    "foo",
    |error: Error| {
        assert_eq!(
            error,
            Error::Runtime(
                RuntimeErrorType::UnknownBlockHeaderHash(BlockHeaderHash([0xff; 32])),
                None
            )
        );
    }
);

test_contract_call_response!(
    test_foo,
    "constant-expr",
    "get-foo",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::UInt(4));
    }
);

test_contract_call_response!(
    test_bar,
    "constant-literal",
    "get-bar",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Int(42));
    }
);

test_contract_call_response!(
    test_private_call,
    "private-call",
    "im-a-private-func",
    |response: ResponseData| {
        assert!(response.committed);
        assert_eq!(*response.data, Value::Int(42));
    }
);

test_multi_contract_call_response!(
    test_string_ascii,
    ["print"],
    "print",
    "test-string-ascii",
    &[Value::string_ascii_from_bytes(b"abc".to_vec()).unwrap(),],
    |response: ResponseData| {
        assert!(response.committed);
        println!("response: {:?}", response);
    }
);

test_multi_contract_call_response!(
    test_list_string_ascii,
    ["print"],
    "print",
    "test-list-string-ascii",
    &[Value::cons_list_unsanitized(vec![
        Value::string_ascii_from_bytes(b"hello".to_vec()).unwrap(),
        Value::string_ascii_from_bytes(b"world".to_vec()).unwrap()
    ])
    .unwrap(),],
    |response: ResponseData| {
        assert!(response.committed);
        println!("response: {:?}", response);
    }
);

test_multi_contract_call_response!(
    test_string_utf8,
    ["print"],
    "print",
    "test-string-utf8",
    &[Value::string_utf8_from_string_utf8_literal("abc".to_owned()).unwrap(),],
    |response: ResponseData| {
        assert!(response.committed);
        println!("response: {:?}", response);
    }
);

test_multi_contract_call_response!(
    test_list_string_utf8,
    ["print"],
    "print",
    "test-list-string-utf8",
    &[Value::cons_list_unsanitized(vec![
        Value::string_utf8_from_string_utf8_literal("hello".to_owned()).unwrap(),
        Value::string_utf8_from_string_utf8_literal("bbb".to_owned()).unwrap(),
        Value::string_utf8_from_string_utf8_literal("ccc".to_owned()).unwrap(),
    ])
    .unwrap(),],
    |response: ResponseData| {
        assert!(response.committed);
        println!("response: {:?}", response);
    }
);
