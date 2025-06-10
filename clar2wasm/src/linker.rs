use clarity::vm::analysis::CheckErrors;
use clarity::vm::callables::{DefineType, DefinedFunction};
use clarity::vm::costs::{constants as cost_constants, CostTracker};
use clarity::vm::database::{ClarityDatabase, STXBalance, StoreType};
use clarity::vm::errors::{Error, RuntimeErrorType, WasmError};
use clarity::vm::functions::crypto::{pubkey_to_address_v1, pubkey_to_address_v2};
use clarity::vm::types::{
    AssetIdentifier, BuffData, BufferLength, FunctionType, ListTypeData, PrincipalData,
    SequenceData, SequenceSubtype, StacksAddressExtensions, TraitIdentifier, TupleData,
    TupleTypeSignature, TypeSignature, BUFF_1, BUFF_32, BUFF_33,
};
use clarity::vm::{ClarityName, ClarityVersion, Environment, SymbolicExpression, Value};
use stacks_common::types::chainstate::StacksBlockId;
use stacks_common::util::hash::{Keccak256Hash, Sha512Sum, Sha512Trunc256Sum};
use stacks_common::util::secp256k1::{secp256k1_recover, secp256k1_verify, Secp256k1PublicKey};
use wasmtime::{Caller, Engine, Instance, Linker, Memory, Module, Store};

use crate::cost::CostLinker;
use crate::initialize::ClarityWasmContext;
use crate::wasm_utils::*;

/// Link the host interface functions for into the Wasm module.
pub fn link_host_functions(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    link_define_function_fn(linker)?;
    link_define_variable_fn(linker)?;
    link_define_ft_fn(linker)?;
    link_define_nft_fn(linker)?;
    link_define_map_fn(linker)?;
    link_define_trait_fn(linker)?;
    link_impl_trait_fn(linker)?;

    link_get_variable_fn(linker)?;
    link_set_variable_fn(linker)?;
    link_tx_sender_fn(linker)?;
    link_contract_caller_fn(linker)?;
    link_tx_sponsor_fn(linker)?;
    link_block_height_fn(linker)?;
    link_stacks_block_height_fn(linker)?;
    link_tenure_height_fn(linker)?;
    link_burn_block_height_fn(linker)?;
    link_stx_liquid_supply_fn(linker)?;
    link_is_in_regtest_fn(linker)?;
    link_is_in_mainnet_fn(linker)?;
    link_chain_id_fn(linker)?;
    link_enter_as_contract_fn(linker)?;
    link_exit_as_contract_fn(linker)?;
    link_stx_get_balance_fn(linker)?;
    link_stx_account_fn(linker)?;
    link_stx_burn_fn(linker)?;
    link_stx_transfer_fn(linker)?;
    link_ft_get_supply_fn(linker)?;
    link_ft_get_balance_fn(linker)?;
    link_ft_burn_fn(linker)?;
    link_ft_mint_fn(linker)?;
    link_ft_transfer_fn(linker)?;
    link_nft_get_owner_fn(linker)?;
    link_nft_burn_fn(linker)?;
    link_nft_mint_fn(linker)?;
    link_nft_transfer_fn(linker)?;
    link_map_get_fn(linker)?;
    link_map_set_fn(linker)?;
    link_map_insert_fn(linker)?;
    link_map_delete_fn(linker)?;
    link_get_stacks_block_info_header_hash_property_fn(linker)?;
    link_get_stacks_block_info_time_property_fn(linker)?;
    link_get_stacks_block_info_identity_header_hash_property_fn(linker)?;
    link_get_tenure_info_burnchain_header_hash_property_fn(linker)?;
    link_get_tenure_info_miner_address_property_fn(linker)?;
    link_get_tenure_info_vrf_seed_property_fn(linker)?;
    link_get_tenure_info_time_property_fn(linker)?;
    link_get_tenure_info_block_reward_property_fn(linker)?;
    link_get_tenure_info_miner_spend_total_property_fn(linker)?;
    link_get_tenure_info_miner_spend_winner_property_fn(linker)?;
    link_get_block_info_time_property_fn(linker)?;
    link_get_block_info_vrf_seed_property_fn(linker)?;
    link_get_block_info_header_hash_property_fn(linker)?;
    link_get_block_info_burnchain_header_hash_property_fn(linker)?;
    link_get_block_info_identity_header_hash_property_fn(linker)?;
    link_get_block_info_miner_address_property_fn(linker)?;
    link_get_block_info_miner_spend_winner_property_fn(linker)?;
    link_get_block_info_miner_spend_total_property_fn(linker)?;
    link_get_block_info_block_reward_property_fn(linker)?;
    link_get_burn_block_info_header_hash_property_fn(linker)?;
    link_get_burn_block_info_pox_addrs_property_fn(linker)?;
    link_contract_call_fn(linker)?;
    link_begin_public_call_fn(linker)?;
    link_begin_read_only_call_fn(linker)?;
    link_commit_call_fn(linker)?;
    link_roll_back_call_fn(linker)?;
    link_print_fn(linker)?;
    link_enter_at_block_fn(linker)?;
    link_exit_at_block_fn(linker)?;
    link_keccak256_fn(linker)?;
    link_sha512_fn(linker)?;
    link_sha512_256_fn(linker)?;
    link_secp256k1_recover_fn(linker)?;
    link_secp256k1_verify_fn(linker)?;
    link_principal_of_fn(linker)?;
    link_save_constant_fn(linker)?;
    link_load_constant_fn(linker)?;
    link_skip_list(linker)?;

    link_log(linker)?;
    link_debug_msg(linker)
}

/// Link host interface function, `define_variable`, into the Wasm module.
/// This function is called for all variable definitions (`define-data-var`).
fn link_define_variable_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "define_variable",
            |mut caller: Caller<'_, ClarityWasmContext>,
             name_offset: i32,
             name_length: i32,
             mut value_offset: i32,
             mut value_length: i32| {
                // TODO: Include this cost
                // runtime_cost(ClarityCostFunction::CreateVar, global_context, value_type.size())?;

                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let epoch = caller.data_mut().global_context.epoch_id;

                // Read the variable name string from the memory
                let name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;

                // Retrieve the type of this variable
                let value_type = caller
                    .data()
                    .contract_analysis
                    .ok_or(Error::Wasm(WasmError::DefineFunctionCalledInRunMode))?
                    .get_persisted_variable_type(name.as_str())
                    .ok_or(Error::Unchecked(CheckErrors::DefineVariableBadSignature))?
                    .clone();

                let contract = caller.data().contract_context().contract_identifier.clone();

                // Read the initial value from the memory
                if is_in_memory_type(&value_type) {
                    (value_offset, value_length) =
                        read_indirect_offset_and_length(memory, &mut caller, value_offset)?;
                }
                let value = read_from_wasm(
                    memory,
                    &mut caller,
                    &value_type,
                    value_offset,
                    value_length,
                    epoch,
                )?;

                caller
                    .data_mut()
                    .contract_context_mut()?
                    .persisted_names
                    .insert(ClarityName::try_from(name.clone())?);

                caller
                    .data_mut()
                    .global_context
                    .add_memory(value_type.type_size()? as u64)
                    .map_err(Error::from)?;

                caller
                    .data_mut()
                    .global_context
                    .add_memory(value.size()? as u64)
                    .map_err(Error::from)?;

                // Create the variable in the global context
                let data_types = caller.data_mut().global_context.database.create_variable(
                    &contract,
                    name.as_str(),
                    value_type,
                )?;

                // Store the variable in the global context
                caller.data_mut().global_context.database.set_variable(
                    &contract,
                    name.as_str(),
                    value,
                    &data_types,
                    &epoch,
                )?;

                // Save the metadata for this variable in the contract context
                caller
                    .data_mut()
                    .contract_context_mut()?
                    .meta_data_var
                    .insert(ClarityName::from(name.as_str()), data_types);

                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "define_variable".to_string(),
                e,
            ))
        })
}

fn link_define_ft_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "define_ft",
            |mut caller: Caller<'_, ClarityWasmContext>,
             name_offset: i32,
             name_length: i32,
             supply_indicator: i32,
             supply_lo: i64,
             supply_hi: i64| {
                // runtime_cost(ClarityCostFunction::CreateFt, global_context, 0)?;

                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let contract_identifier = caller
                    .data_mut()
                    .contract_context()
                    .contract_identifier
                    .clone();

                let name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;
                let cname = ClarityName::try_from(name.clone())?;

                let total_supply = if supply_indicator == 1 {
                    Some(((supply_hi as u128) << 64) | supply_lo as u128)
                } else {
                    None
                };

                caller
                    .data_mut()
                    .contract_context_mut()?
                    .persisted_names
                    .insert(cname.clone());

                caller
                    .data_mut()
                    .global_context
                    .add_memory(TypeSignature::UIntType.type_size()? as u64)
                    .map_err(Error::from)?;
                let data_type = caller
                    .data_mut()
                    .global_context
                    .database
                    .create_fungible_token(&contract_identifier, &name, &total_supply)?;

                caller
                    .data_mut()
                    .contract_context_mut()?
                    .meta_ft
                    .insert(cname, data_type);

                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "define_ft".to_string(),
                e,
            ))
        })
}

fn link_define_nft_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "define_nft",
            |mut caller: Caller<'_, ClarityWasmContext>, name_offset: i32, name_length: i32| {
                // runtime_cost(ClarityCostFunction::CreateNft, global_context, asset_type.size())?;

                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let contract_identifier = caller
                    .data_mut()
                    .contract_context()
                    .contract_identifier
                    .clone();

                let name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;
                let cname = ClarityName::try_from(name.clone())?;

                // Get the type of this NFT from the contract analysis
                let asset_type = caller
                    .data()
                    .contract_analysis
                    .ok_or(Error::Wasm(WasmError::DefineFunctionCalledInRunMode))?
                    .non_fungible_tokens
                    .get(&cname)
                    .ok_or(Error::Unchecked(CheckErrors::DefineNFTBadSignature))?;

                caller
                    .data_mut()
                    .contract_context_mut()?
                    .persisted_names
                    .insert(cname.clone());

                caller
                    .data_mut()
                    .global_context
                    .add_memory(asset_type.type_size()? as u64)
                    .map_err(Error::from)?;

                let data_type = caller
                    .data_mut()
                    .global_context
                    .database
                    .create_non_fungible_token(&contract_identifier, &name, asset_type)?;

                caller
                    .data_mut()
                    .contract_context_mut()?
                    .meta_nft
                    .insert(cname, data_type);

                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "define_nft".to_string(),
                e,
            ))
        })
}

fn link_define_map_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "define_map",
            |mut caller: Caller<'_, ClarityWasmContext>, name_offset: i32, name_length: i32| {
                // runtime_cost(
                //     ClarityCostFunction::CreateMap,
                //     global_context,
                //     u64::from(key_type.size()).cost_overflow_add(u64::from(value_type.size()))?,
                // )?;

                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let contract_identifier = caller
                    .data_mut()
                    .contract_context()
                    .contract_identifier
                    .clone();

                let name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;
                let cname = ClarityName::try_from(name.clone())?;

                let (key_type, value_type) = caller
                    .data()
                    .contract_analysis
                    .ok_or(Error::Wasm(WasmError::DefineFunctionCalledInRunMode))?
                    .get_map_type(&name)
                    .ok_or(Error::Unchecked(CheckErrors::BadMapTypeDefinition))?;

                caller
                    .data_mut()
                    .contract_context_mut()?
                    .persisted_names
                    .insert(cname.clone());

                caller
                    .data_mut()
                    .global_context
                    .add_memory(key_type.type_size()? as u64)
                    .map_err(Error::from)?;
                caller
                    .data_mut()
                    .global_context
                    .add_memory(value_type.type_size()? as u64)
                    .map_err(Error::from)?;

                let data_type = caller.data_mut().global_context.database.create_map(
                    &contract_identifier,
                    &name,
                    key_type.clone(),
                    value_type.clone(),
                )?;

                caller
                    .data_mut()
                    .contract_context_mut()?
                    .meta_data_map
                    .insert(cname, data_type);

                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "define_map".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `define_function`, into the Wasm module.
/// This function is called for all function definitions.
fn link_define_function_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "define_function",
            |mut caller: Caller<'_, ClarityWasmContext>,
             kind: i32,
             name_offset: i32,
             name_length: i32| {
                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                // Read the variable name string from the memory
                let function_name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;
                let function_cname = ClarityName::try_from(function_name.clone())?;

                // Retrieve the kind of function
                let (define_type, function_type) = match kind {
                    0 => (
                        DefineType::ReadOnly,
                        caller
                            .data()
                            .contract_analysis
                            .ok_or(Error::Wasm(WasmError::DefineFunctionCalledInRunMode))?
                            .get_read_only_function_type(&function_name)
                            .ok_or(Error::Unchecked(CheckErrors::UnknownFunction(
                                function_name.clone(),
                            )))?,
                    ),
                    1 => (
                        DefineType::Public,
                        caller
                            .data()
                            .contract_analysis
                            .ok_or(Error::Wasm(WasmError::DefineFunctionCalledInRunMode))?
                            .get_public_function_type(&function_name)
                            .ok_or(Error::Unchecked(CheckErrors::UnknownFunction(
                                function_name.clone(),
                            )))?,
                    ),
                    2 => (
                        DefineType::Private,
                        caller
                            .data()
                            .contract_analysis
                            .ok_or(Error::Wasm(WasmError::DefineFunctionCalledInRunMode))?
                            .get_private_function(&function_name)
                            .ok_or(Error::Unchecked(CheckErrors::UnknownFunction(
                                function_name.clone(),
                            )))?,
                    ),
                    _ => Err(Error::Wasm(WasmError::InvalidFunctionKind(kind)))?,
                };

                let fixed_type = match function_type {
                    FunctionType::Fixed(fixed_type) => fixed_type,
                    _ => Err(Error::Unchecked(CheckErrors::DefineFunctionBadSignature))?,
                };

                let function = DefinedFunction::new(
                    fixed_type
                        .args
                        .iter()
                        .map(|arg| (arg.name.clone(), arg.signature.clone()))
                        .collect(),
                    // TODO: We don't actually need the body here, so we
                    // should be able to remove it. For now, this is a
                    // placeholder.
                    SymbolicExpression::literal_value(Value::Int(0)),
                    define_type,
                    &function_cname,
                    &caller
                        .data()
                        .contract_context()
                        .contract_identifier
                        .to_string(),
                    Some(fixed_type.returns.clone()),
                );

                // Insert this function into the context
                caller
                    .data_mut()
                    .contract_context_mut()?
                    .functions
                    .insert(function_cname, function);

                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "define_function".to_string(),
                e,
            ))
        })
}

fn link_define_trait_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "define_trait",
            |mut caller: Caller<'_, ClarityWasmContext>, name_offset: i32, name_length: i32| {
                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;
                let cname = ClarityName::try_from(name.clone())?;

                let trait_def = caller
                    .data()
                    .contract_analysis
                    .ok_or(Error::Wasm(WasmError::DefineFunctionCalledInRunMode))?
                    .get_defined_trait(name.as_str())
                    .ok_or(Error::Unchecked(CheckErrors::DefineTraitBadSignature))?;

                caller
                    .data_mut()
                    .contract_context_mut()?
                    .defined_traits
                    .insert(cname, trait_def.clone());

                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "define_map".to_string(),
                e,
            ))
        })
}

fn link_impl_trait_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "impl_trait",
            |mut caller: Caller<'_, ClarityWasmContext>, name_offset: i32, name_length: i32| {
                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let trait_id_string =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;
                let trait_id = TraitIdentifier::parse_fully_qualified(trait_id_string.as_str())?;

                caller
                    .data_mut()
                    .contract_context_mut()?
                    .implemented_traits
                    .insert(trait_id);

                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "define_map".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_variable`, into the Wasm module.
/// This function is called for all variable lookups (`var-get`).
fn link_get_variable_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_variable",
            |mut caller: Caller<'_, ClarityWasmContext>,
             name_offset: i32,
             name_length: i32,
             return_offset: i32,
             _return_length: i32| {
                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                // Retrieve the variable name for this identifier
                let var_name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;

                let contract = caller.data().contract_context().contract_identifier.clone();
                let epoch = caller.data_mut().global_context.epoch_id;

                // Retrieve the metadata for this variable
                let data_types = caller
                    .data()
                    .contract_context()
                    .meta_data_var
                    .get(var_name.as_str())
                    .ok_or(CheckErrors::NoSuchDataVariable(var_name.to_string()))?
                    .clone();

                // We would like to call `lookup_variable_with_size`, but since it
                // returns `Ok(none)` even if the variable is missing, we have no way
                // to distinguish between a valid `none` and a missing variable.
                // So here we replicate `lookup_variable_with_size` impl.
                let key = ClarityDatabase::make_key_for_trip(
                    &contract,
                    StoreType::Variable,
                    var_name.as_str(),
                );
                let fetch_result = caller.data_mut().global_context.database.get_value(
                    &key,
                    &data_types.value_type,
                    &epoch,
                )?;

                // TODO: Include this cost
                // let _result_size = match &fetch_result {
                //     Ok(data) => data.serialized_byte_len,
                //     Err(_e) => data_types.value_type.size()? as u64,
                // };
                // runtime_cost(ClarityCostFunction::FetchVar, env, result_size)?;

                let value = fetch_result.map(|data| data.value).ok_or(Error::Unchecked(
                    CheckErrors::NoSuchDataVariable(var_name.to_string()),
                ))?;

                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                write_to_wasm(
                    &mut caller,
                    memory,
                    &data_types.value_type,
                    return_offset,
                    return_offset + get_type_size(&data_types.value_type),
                    &value,
                    true,
                )?;

                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_variable".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `set_variable`, into the Wasm module.
/// This function is called for all variable assignments (`var-set`).
fn link_set_variable_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "set_variable",
            |mut caller: Caller<'_, ClarityWasmContext>,
             name_offset: i32,
             name_length: i32,
             mut value_offset: i32,
             mut value_length: i32| {
                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let epoch = caller.data_mut().global_context.epoch_id;

                // Retrieve the variable name for this identifier
                let var_name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;

                let contract = caller.data().contract_context().contract_identifier.clone();

                let data_types = caller
                    .data()
                    .contract_context()
                    .meta_data_var
                    .get(var_name.as_str())
                    .ok_or(Error::Unchecked(CheckErrors::NoSuchDataVariable(
                        var_name.to_string(),
                    )))?
                    .clone();

                // TODO: Include this cost
                // runtime_cost(
                //     ClarityCostFunction::SetVar,
                //     env,
                //     data_types.value_type.size(),
                // )?;

                // Read in the value from the Wasm memory
                if is_in_memory_type(&data_types.value_type) {
                    (value_offset, value_length) =
                        read_indirect_offset_and_length(memory, &mut caller, value_offset)?;
                }
                let value = read_from_wasm(
                    memory,
                    &mut caller,
                    &data_types.value_type,
                    value_offset,
                    value_length,
                    epoch,
                )?;

                // TODO: Include this cost
                // env.add_memory(value.get_memory_use())?;

                // Store the variable in the global context
                caller.data_mut().global_context.database.set_variable(
                    &contract,
                    var_name.as_str(),
                    value,
                    &data_types,
                    &epoch,
                )?;

                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "set_variable".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `tx_sender`, into the Wasm module.
/// This function is called for use of the builtin variable, `tx-sender`.
fn link_tx_sender_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "tx_sender",
            |mut caller: Caller<'_, ClarityWasmContext>,
             return_offset: i32,
             _return_length: i32| {
                let sender = caller
                    .data()
                    .sender
                    .clone()
                    .ok_or(Error::Runtime(RuntimeErrorType::NoSenderInContext, None))?;

                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let (_, bytes_written) = write_to_wasm(
                    &mut caller,
                    memory,
                    &TypeSignature::PrincipalType,
                    return_offset,
                    return_offset,
                    &Value::Principal(sender),
                    false,
                )?;

                Ok((return_offset, bytes_written))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "tx_sender".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `contract_caller`, into the Wasm module.
/// This function is called for use of the builtin variable, `contract-caller`.
fn link_contract_caller_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "contract_caller",
            |mut caller: Caller<'_, ClarityWasmContext>,
             return_offset: i32,
             _return_length: i32| {
                let contract_caller = caller
                    .data()
                    .caller
                    .clone()
                    .ok_or(Error::Runtime(RuntimeErrorType::NoCallerInContext, None))?;

                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let (_, bytes_written) = write_to_wasm(
                    &mut caller,
                    memory,
                    &TypeSignature::PrincipalType,
                    return_offset,
                    return_offset,
                    &Value::Principal(contract_caller),
                    false,
                )?;

                Ok((return_offset, bytes_written))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "contract_caller".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `tx_sponsor`, into the Wasm module.
/// This function is called for use of the builtin variable, `tx-sponsor`.
fn link_tx_sponsor_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "tx_sponsor",
            |mut caller: Caller<'_, ClarityWasmContext>,
             return_offset: i32,
             _return_length: i32| {
                let opt_sponsor = caller.data().sponsor.clone();
                if let Some(sponsor) = opt_sponsor {
                    let memory = caller
                        .get_export("memory")
                        .and_then(|export| export.into_memory())
                        .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                    let (_, bytes_written) = write_to_wasm(
                        &mut caller,
                        memory,
                        &TypeSignature::PrincipalType,
                        return_offset,
                        return_offset,
                        &Value::Principal(sponsor),
                        false,
                    )?;

                    Ok((1i32, return_offset, bytes_written))
                } else {
                    Ok((0i32, return_offset, 0i32))
                }
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "tx_sponsor".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `block_height`, into the Wasm module.
/// This function is called for use of the builtin variable, `block-height`.
fn link_block_height_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "block_height",
            |mut caller: Caller<'_, ClarityWasmContext>| {
                let height = caller
                    .data_mut()
                    .global_context
                    .database
                    .get_current_block_height();
                Ok((height as i64, 0i64))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "block_height".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `stacks_block_height`, into the Wasm module.
/// This function is called for use of the builtin variable, `stacks_block-height`.
fn link_stacks_block_height_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "stacks_block_height",
            |mut caller: Caller<'_, ClarityWasmContext>| {
                let height = caller
                    .data_mut()
                    .global_context
                    .database
                    .get_current_block_height();
                Ok((height as i64, 0i64))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "stacks_block_height".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `tenure_height`, into the Wasm module.
/// This function is called for use of the builtin variable, `tenure-height`.
fn link_tenure_height_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "tenure_height",
            |mut caller: Caller<'_, ClarityWasmContext>| {
                let height = caller
                    .data_mut()
                    .global_context
                    .database
                    .get_tenure_height()?;
                Ok((height as i64, 0i64))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "tenure_height".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `burn_block_height`, into the Wasm module.
/// This function is called for use of the builtin variable,
/// `burn-block-height`.
fn link_burn_block_height_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "burn_block_height",
            |mut caller: Caller<'_, ClarityWasmContext>| {
                let height = caller
                    .data_mut()
                    .global_context
                    .database
                    .get_current_burnchain_block_height()?;
                Ok((height as i64, 0i64))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "burn_block_height".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `stx_liquid_supply`, into the Wasm module.
/// This function is called for use of the builtin variable,
/// `stx-liquid-supply`.
fn link_stx_liquid_supply_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "stx_liquid_supply",
            |mut caller: Caller<'_, ClarityWasmContext>| {
                let supply = caller
                    .data_mut()
                    .global_context
                    .database
                    .get_total_liquid_ustx()?;
                let upper = (supply >> 64) as u64;
                let lower = supply as u64;
                Ok((lower as i64, upper as i64))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "stx_liquid_supply".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `is_in_regtest`, into the Wasm module.
/// This function is called for use of the builtin variable,
/// `is-in-regtest`.
fn link_is_in_regtest_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "is_in_regtest",
            |caller: Caller<'_, ClarityWasmContext>| {
                if caller.data().global_context.database.is_in_regtest() {
                    Ok(1i32)
                } else {
                    Ok(0i32)
                }
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "is_in_regtest".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `is_in_mainnet`, into the Wasm module.
/// This function is called for use of the builtin variable,
/// `is-in-mainnet`.
fn link_is_in_mainnet_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "is_in_mainnet",
            |caller: Caller<'_, ClarityWasmContext>| {
                if caller.data().global_context.mainnet {
                    Ok(1i32)
                } else {
                    Ok(0i32)
                }
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "is_in_mainnet".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `chain_id`, into the Wasm module.
/// This function is called for use of the builtin variable,
/// `chain-id`.
fn link_chain_id_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "chain_id",
            |caller: Caller<'_, ClarityWasmContext>| {
                let chain_id = caller.data().global_context.chain_id;
                Ok((chain_id as i64, 0i64))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "chain_id".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `enter_as_contract`, into the Wasm module.
/// This function is called before processing the inner-expression of
/// `as-contract`.
fn link_enter_as_contract_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "enter_as_contract",
            |mut caller: Caller<'_, ClarityWasmContext>| {
                let contract_principal: PrincipalData = caller
                    .data()
                    .contract_context()
                    .contract_identifier
                    .clone()
                    .into();
                caller.data_mut().push_sender(contract_principal.clone());
                caller.data_mut().push_caller(contract_principal);
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "enter_as_contract".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `exit_as_contract`, into the Wasm module.
/// This function is after before processing the inner-expression of
/// `as-contract`, and is used to restore the caller and sender.
fn link_exit_as_contract_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "exit_as_contract",
            |mut caller: Caller<'_, ClarityWasmContext>| {
                caller.data_mut().pop_sender()?;
                caller.data_mut().pop_caller()?;
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "exit_as_contract".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `stx_get_balance`, into the Wasm module.
/// This function is called for the clarity expression, `stx-get-balance`.
fn link_stx_get_balance_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "stx_get_balance",
            |mut caller: Caller<'_, ClarityWasmContext>,
             principal_offset: i32,
             principal_length: i32| {
                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let epoch = caller.data_mut().global_context.epoch_id;

                // Read the principal from the Wasm memory
                let value = read_from_wasm(
                    memory,
                    &mut caller,
                    &TypeSignature::PrincipalType,
                    principal_offset,
                    principal_length,
                    epoch,
                )?;
                let principal = value_as_principal(&value)?;

                let balance = {
                    let mut snapshot = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_stx_balance_snapshot(principal)?;
                    snapshot.get_available_balance()?
                };
                let high = (balance >> 64) as u64;
                let low = (balance & 0xffff_ffff_ffff_ffff) as u64;
                Ok((low, high))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "stx_get_balance".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `stx_account`, into the Wasm module.
/// This function is called for the clarity expression, `stx-account`.
fn link_stx_account_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "stx_account",
            |mut caller: Caller<'_, ClarityWasmContext>,
             principal_offset: i32,
             principal_length: i32| {
                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let epoch = caller.data_mut().global_context.epoch_id;

                // Read the principal from the Wasm memory
                let value = read_from_wasm(
                    memory,
                    &mut caller,
                    &TypeSignature::PrincipalType,
                    principal_offset,
                    principal_length,
                    epoch,
                )?;
                let principal = value_as_principal(&value)?;

                let account = {
                    let mut snapshot = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_stx_balance_snapshot(principal)?;
                    snapshot.canonical_balance_repr()?
                };
                let v1_unlock_ht = caller
                    .data_mut()
                    .global_context
                    .database
                    .get_v1_unlock_height();
                let v2_unlock_ht = caller
                    .data_mut()
                    .global_context
                    .database
                    .get_v2_unlock_height()?;
                let v3_unlock_ht = caller
                    .data_mut()
                    .global_context
                    .database
                    .get_v3_unlock_height()?;

                let locked = account.amount_locked();
                let locked_high = (locked >> 64) as u64;
                let locked_low = (locked & 0xffff_ffff_ffff_ffff) as u64;
                let unlock_height =
                    account.effective_unlock_height(v1_unlock_ht, v2_unlock_ht, v3_unlock_ht);
                let unlocked = account.amount_unlocked();
                let unlocked_high = (unlocked >> 64) as u64;
                let unlocked_low = (unlocked & 0xffff_ffff_ffff_ffff) as u64;

                // Return value is a tuple: `{locked: uint, unlock-height: uint, unlocked: uint}`
                Ok((
                    locked_low,
                    locked_high,
                    unlock_height as i64,
                    0i64,
                    unlocked_low,
                    unlocked_high,
                ))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "stx_account".to_string(),
                e,
            ))
        })
}

fn link_stx_burn_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "stx_burn",
            |mut caller: Caller<'_, ClarityWasmContext>,
             amount_lo: i64,
             amount_hi: i64,
             principal_offset: i32,
             principal_length: i32| {
                let amount = ((amount_hi as u128) << 64) | ((amount_lo as u64) as u128);

                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let epoch = caller.data_mut().global_context.epoch_id;

                // Read the principal from the Wasm memory
                let value = read_from_wasm(
                    memory,
                    &mut caller,
                    &TypeSignature::PrincipalType,
                    principal_offset,
                    principal_length,
                    epoch,
                )?;
                let from = value_as_principal(&value)?;

                if amount == 0 {
                    return Ok((0i32, 0i32, StxErrorCodes::NON_POSITIVE_AMOUNT as i64, 0i64));
                }

                if Some(from) != caller.data().sender.as_ref() {
                    return Ok((
                        0i32,
                        0i32,
                        StxErrorCodes::SENDER_IS_NOT_TX_SENDER as i64,
                        0i64,
                    ));
                }

                caller
                    .data_mut()
                    .global_context
                    .add_memory(TypeSignature::PrincipalType.size()? as u64)
                    .map_err(Error::from)?;
                caller
                    .data_mut()
                    .global_context
                    .add_memory(STXBalance::unlocked_and_v1_size as u64)
                    .map_err(Error::from)?;

                let mut burner_snapshot = caller
                    .data_mut()
                    .global_context
                    .database
                    .get_stx_balance_snapshot(from)?;
                if !burner_snapshot.can_transfer(amount)? {
                    return Ok((0i32, 0i32, StxErrorCodes::NOT_ENOUGH_BALANCE as i64, 0i64));
                }

                burner_snapshot.debit(amount)?;
                burner_snapshot.save()?;

                caller
                    .data_mut()
                    .global_context
                    .database
                    .decrement_ustx_liquid_supply(amount)?;

                caller
                    .data_mut()
                    .global_context
                    .log_stx_burn(from, amount)?;
                caller
                    .data_mut()
                    .register_stx_burn_event(from.clone(), amount)?;

                // (ok true)
                Ok((1i32, 1i32, 0i64, 0i64))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "stx_burn".to_string(),
                e,
            ))
        })
}

fn link_stx_transfer_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "stx_transfer",
            |mut caller: Caller<'_, ClarityWasmContext>,
             amount_lo: i64,
             amount_hi: i64,
             sender_offset: i32,
             sender_length: i32,
             recipient_offset: i32,
             recipient_length: i32,
             memo_offset: i32,
             memo_length: i32| {
                let amount = ((amount_hi as u128) << 64) | ((amount_lo as u64) as u128);

                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let epoch = caller.data_mut().global_context.epoch_id;

                // Read the sender principal from the Wasm memory
                let value = read_from_wasm(
                    memory,
                    &mut caller,
                    &TypeSignature::PrincipalType,
                    sender_offset,
                    sender_length,
                    epoch,
                )?;
                let sender = value_as_principal(&value)?;

                // Read the to principal from the Wasm memory
                let value = read_from_wasm(
                    memory,
                    &mut caller,
                    &TypeSignature::PrincipalType,
                    recipient_offset,
                    recipient_length,
                    epoch,
                )?;
                let recipient = value_as_principal(&value)?;

                // Read the memo from the Wasm memory
                let memo = if memo_length > 0 {
                    let value = read_from_wasm(
                        memory,
                        &mut caller,
                        &TypeSignature::SequenceType(SequenceSubtype::BufferType(
                            BufferLength::try_from(memo_length as u32)?,
                        )),
                        memo_offset,
                        memo_length,
                        epoch,
                    )?;
                    value_as_buffer(value)?
                } else {
                    BuffData::empty()
                };

                if amount == 0 {
                    return Ok((0i32, 0i32, StxErrorCodes::NON_POSITIVE_AMOUNT as i64, 0i64));
                }

                if sender == recipient {
                    return Ok((0i32, 0i32, StxErrorCodes::SENDER_IS_RECIPIENT as i64, 0i64));
                }

                if Some(sender) != caller.data().sender.as_ref() {
                    return Ok((
                        0i32,
                        0i32,
                        StxErrorCodes::SENDER_IS_NOT_TX_SENDER as i64,
                        0i64,
                    ));
                }

                // loading sender/recipient principals and balances
                caller
                    .data_mut()
                    .global_context
                    .add_memory(TypeSignature::PrincipalType.size()? as u64)
                    .map_err(Error::from)?;
                caller
                    .data_mut()
                    .global_context
                    .add_memory(TypeSignature::PrincipalType.size()? as u64)
                    .map_err(Error::from)?;
                // loading sender's locked amount and height
                // TODO: this does not count the inner stacks block header load, but arguably,
                // this could be optimized away, so it shouldn't penalize the caller.
                caller
                    .data_mut()
                    .global_context
                    .add_memory(STXBalance::unlocked_and_v1_size as u64)
                    .map_err(Error::from)?;
                caller
                    .data_mut()
                    .global_context
                    .add_memory(STXBalance::unlocked_and_v1_size as u64)
                    .map_err(Error::from)?;

                let mut sender_snapshot = caller
                    .data_mut()
                    .global_context
                    .database
                    .get_stx_balance_snapshot(sender)?;
                if !sender_snapshot.can_transfer(amount)? {
                    return Ok((0i32, 0i32, StxErrorCodes::NOT_ENOUGH_BALANCE as i64, 0i64));
                }

                sender_snapshot.transfer_to(recipient, amount)?;

                caller
                    .data_mut()
                    .global_context
                    .log_stx_transfer(sender, amount)?;
                caller.data_mut().register_stx_transfer_event(
                    sender.clone(),
                    recipient.clone(),
                    amount,
                    memo,
                )?;

                // (ok true)
                Ok((1i32, 1i32, 0i64, 0i64))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "stx_transfer".to_string(),
                e,
            ))
        })
}

fn link_ft_get_supply_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "ft_get_supply",
            |mut caller: Caller<'_, ClarityWasmContext>, name_offset: i32, name_length: i32| {
                let contract_identifier =
                    caller.data().contract_context().contract_identifier.clone();

                // runtime_cost(ClarityCostFunction::FtSupply, env, 0)?;

                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                // Retrieve the token name
                let token_name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;

                let supply = caller
                    .data_mut()
                    .global_context
                    .database
                    .get_ft_supply(&contract_identifier, &token_name)?;

                let high = (supply >> 64) as u64;
                let low = (supply & 0xffff_ffff_ffff_ffff) as u64;
                Ok((low, high))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "ft_get_supply".to_string(),
                e,
            ))
        })
}

fn link_ft_get_balance_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "ft_get_balance",
            |mut caller: Caller<'_, ClarityWasmContext>,
             name_offset: i32,
             name_length: i32,
             owner_offset: i32,
             owner_length: i32| {
                // runtime_cost(ClarityCostFunction::FtBalance, env, 0)?;

                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                // Retrieve the token name
                let name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;
                let token_name = ClarityName::try_from(name.clone())?;

                let contract_identifier =
                    caller.data().contract_context().contract_identifier.clone();
                let epoch = caller.data_mut().global_context.epoch_id;

                // Read the owner principal from the Wasm memory
                let value = read_from_wasm(
                    memory,
                    &mut caller,
                    &TypeSignature::PrincipalType,
                    owner_offset,
                    owner_length,
                    epoch,
                )?;
                let owner = value_as_principal(&value)?;

                let ft_info = caller
                    .data()
                    .contract_context()
                    .meta_ft
                    .get(&token_name)
                    .ok_or(CheckErrors::NoSuchFT(token_name.to_string()))?
                    .clone();

                let balance = caller.data_mut().global_context.database.get_ft_balance(
                    &contract_identifier,
                    token_name.as_str(),
                    owner,
                    Some(&ft_info),
                )?;

                let high = (balance >> 64) as u64;
                let low = (balance & 0xffff_ffff_ffff_ffff) as u64;
                Ok((low, high))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "ft_get_balance".to_string(),
                e,
            ))
        })
}

fn link_ft_burn_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "ft_burn",
            |mut caller: Caller<'_, ClarityWasmContext>,
             name_offset: i32,
             name_length: i32,
             amount_lo: i64,
             amount_hi: i64,
             sender_offset: i32,
             sender_length: i32| {
                // runtime_cost(ClarityCostFunction::FtBurn, env, 0)?;

                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let contract_identifier =
                    caller.data().contract_context().contract_identifier.clone();
                let epoch = caller.data_mut().global_context.epoch_id;

                // Retrieve the token name
                let name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;
                let token_name = ClarityName::try_from(name.clone())?;

                // Compute the amount
                let amount = ((amount_hi as u128) << 64) | ((amount_lo as u64) as u128);

                // Read the sender principal from the Wasm memory
                let value = read_from_wasm(
                    memory,
                    &mut caller,
                    &TypeSignature::PrincipalType,
                    sender_offset,
                    sender_length,
                    epoch,
                )?;
                let burner = value_as_principal(&value)?;

                if amount == 0 {
                    return Ok((
                        0i32,
                        0i32,
                        BurnTokenErrorCodes::NOT_ENOUGH_BALANCE_OR_NON_POSITIVE as i64,
                        0i64,
                    ));
                }

                let burner_bal = caller.data_mut().global_context.database.get_ft_balance(
                    &contract_identifier,
                    token_name.as_str(),
                    burner,
                    None,
                )?;

                if amount > burner_bal {
                    return Ok((
                        0i32,
                        0i32,
                        BurnTokenErrorCodes::NOT_ENOUGH_BALANCE_OR_NON_POSITIVE as i64,
                        0i64,
                    ));
                }

                caller
                    .data_mut()
                    .global_context
                    .database
                    .checked_decrease_token_supply(
                        &contract_identifier,
                        token_name.as_str(),
                        amount,
                    )?;

                let final_burner_bal = burner_bal - amount;

                caller.data_mut().global_context.database.set_ft_balance(
                    &contract_identifier,
                    token_name.as_str(),
                    burner,
                    final_burner_bal,
                )?;

                let asset_identifier = AssetIdentifier {
                    contract_identifier: contract_identifier.clone(),
                    asset_name: token_name.clone(),
                };
                caller.data_mut().register_ft_burn_event(
                    burner.clone(),
                    amount,
                    asset_identifier,
                )?;

                caller
                    .data_mut()
                    .global_context
                    .add_memory(TypeSignature::PrincipalType.size()? as u64)
                    .map_err(Error::from)?;
                caller
                    .data_mut()
                    .global_context
                    .add_memory(TypeSignature::UIntType.size()? as u64)
                    .map_err(Error::from)?;

                caller.data_mut().global_context.log_token_transfer(
                    burner,
                    &contract_identifier,
                    &token_name,
                    amount,
                )?;

                // (ok true)
                Ok((1i32, 1i32, 0i64, 0i64))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "ft_burn".to_string(),
                e,
            ))
        })
}

fn link_ft_mint_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "ft_mint",
            |mut caller: Caller<'_, ClarityWasmContext>,
             name_offset: i32,
             name_length: i32,
             amount_lo: i64,
             amount_hi: i64,
             sender_offset: i32,
             sender_length: i32| {
                // runtime_cost(ClarityCostFunction::FtBurn, env, 0)?;

                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let contract_identifier =
                    caller.data().contract_context().contract_identifier.clone();
                let epoch = caller.data_mut().global_context.epoch_id;

                // Retrieve the token name
                let name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;
                let token_name = ClarityName::try_from(name.clone())?;

                // Compute the amount
                let amount = ((amount_hi as u128) << 64) | ((amount_lo as u64) as u128);

                // Read the sender principal from the Wasm memory
                let value = read_from_wasm(
                    memory,
                    &mut caller,
                    &TypeSignature::PrincipalType,
                    sender_offset,
                    sender_length,
                    epoch,
                )?;
                let to_principal = value_as_principal(&value)?;

                if amount == 0 {
                    return Ok((
                        0i32,
                        0i32,
                        MintTokenErrorCodes::NON_POSITIVE_AMOUNT as i64,
                        0i64,
                    ));
                }

                let ft_info = caller
                    .data()
                    .contract_context()
                    .meta_ft
                    .get(token_name.as_str())
                    .ok_or(CheckErrors::NoSuchFT(token_name.to_string()))?
                    .clone();

                caller
                    .data_mut()
                    .global_context
                    .database
                    .checked_increase_token_supply(
                        &contract_identifier,
                        token_name.as_str(),
                        amount,
                        &ft_info,
                    )?;

                let to_bal = caller.data_mut().global_context.database.get_ft_balance(
                    &contract_identifier,
                    token_name.as_str(),
                    to_principal,
                    Some(&ft_info),
                )?;

                let final_to_bal = to_bal
                    .checked_add(amount)
                    .ok_or(Error::Runtime(RuntimeErrorType::ArithmeticOverflow, None))?;

                caller
                    .data_mut()
                    .global_context
                    .add_memory(TypeSignature::PrincipalType.size()? as u64)
                    .map_err(Error::from)?;
                caller
                    .data_mut()
                    .global_context
                    .add_memory(TypeSignature::UIntType.size()? as u64)
                    .map_err(Error::from)?;

                caller.data_mut().global_context.database.set_ft_balance(
                    &contract_identifier,
                    token_name.as_str(),
                    to_principal,
                    final_to_bal,
                )?;

                let asset_identifier = AssetIdentifier {
                    contract_identifier: contract_identifier.clone(),
                    asset_name: token_name.clone(),
                };
                caller.data_mut().register_ft_mint_event(
                    to_principal.clone(),
                    amount,
                    asset_identifier,
                )?;

                // (ok true)
                Ok((1i32, 1i32, 0i64, 0i64))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "ft_mint".to_string(),
                e,
            ))
        })
}

fn link_ft_transfer_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "ft_transfer",
            |mut caller: Caller<'_, ClarityWasmContext>,
             name_offset: i32,
             name_length: i32,
             amount_lo: i64,
             amount_hi: i64,
             sender_offset: i32,
             sender_length: i32,
             recipient_offset: i32,
             recipient_length: i32| {
                // runtime_cost(ClarityCostFunction::FtTransfer, env, 0)?;

                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let contract_identifier =
                    caller.data().contract_context().contract_identifier.clone();

                let epoch = caller.data_mut().global_context.epoch_id;

                // Retrieve the token name
                let name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;
                let token_name = ClarityName::try_from(name.clone())?;

                // Compute the amount
                let amount = ((amount_hi as u128) << 64) | ((amount_lo as u64) as u128);

                // Read the sender principal from the Wasm memory
                let value = read_from_wasm(
                    memory,
                    &mut caller,
                    &TypeSignature::PrincipalType,
                    sender_offset,
                    sender_length,
                    epoch,
                )?;
                let from_principal = value_as_principal(&value)?;

                // Read the recipient principal from the Wasm memory
                let value = read_from_wasm(
                    memory,
                    &mut caller,
                    &TypeSignature::PrincipalType,
                    recipient_offset,
                    recipient_length,
                    epoch,
                )?;
                let to_principal = value_as_principal(&value)?;

                if amount == 0 {
                    return Ok((
                        0i32,
                        0i32,
                        TransferTokenErrorCodes::NON_POSITIVE_AMOUNT as i64,
                        0i64,
                    ));
                }

                if from_principal == to_principal {
                    return Ok((
                        0i32,
                        0i32,
                        TransferTokenErrorCodes::SENDER_IS_RECIPIENT as i64,
                        0i64,
                    ));
                }

                let ft_info = caller
                    .data()
                    .contract_context()
                    .meta_ft
                    .get(&token_name)
                    .ok_or(CheckErrors::NoSuchFT(token_name.to_string()))?
                    .clone();

                let from_bal = caller.data_mut().global_context.database.get_ft_balance(
                    &contract_identifier,
                    token_name.as_str(),
                    from_principal,
                    Some(&ft_info),
                )?;

                if from_bal < amount {
                    return Ok((
                        0i32,
                        0i32,
                        TransferTokenErrorCodes::NOT_ENOUGH_BALANCE as i64,
                        0i64,
                    ));
                }

                let final_from_bal = from_bal - amount;

                let to_bal = caller.data_mut().global_context.database.get_ft_balance(
                    &contract_identifier,
                    token_name.as_str(),
                    to_principal,
                    Some(&ft_info),
                )?;

                let final_to_bal = to_bal
                    .checked_add(amount)
                    .ok_or(RuntimeErrorType::ArithmeticOverflow)?;

                caller
                    .data_mut()
                    .global_context
                    .add_memory(TypeSignature::PrincipalType.size()? as u64)
                    .map_err(Error::from)?;
                caller
                    .data_mut()
                    .global_context
                    .add_memory(TypeSignature::PrincipalType.size()? as u64)
                    .map_err(Error::from)?;
                caller
                    .data_mut()
                    .global_context
                    .add_memory(TypeSignature::UIntType.size()? as u64)
                    .map_err(Error::from)?;
                caller
                    .data_mut()
                    .global_context
                    .add_memory(TypeSignature::UIntType.size()? as u64)
                    .map_err(Error::from)?;

                caller.data_mut().global_context.database.set_ft_balance(
                    &contract_identifier,
                    &token_name,
                    from_principal,
                    final_from_bal,
                )?;
                caller.data_mut().global_context.database.set_ft_balance(
                    &contract_identifier,
                    token_name.as_str(),
                    to_principal,
                    final_to_bal,
                )?;

                caller.data_mut().global_context.log_token_transfer(
                    from_principal,
                    &contract_identifier,
                    &token_name,
                    amount,
                )?;

                let asset_identifier = AssetIdentifier {
                    contract_identifier: contract_identifier.clone(),
                    asset_name: token_name.clone(),
                };
                caller.data_mut().register_ft_transfer_event(
                    from_principal.clone(),
                    to_principal.clone(),
                    amount,
                    asset_identifier,
                )?;

                // (ok true)
                Ok((1i32, 1i32, 0i64, 0i64))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "ft_transfer".to_string(),
                e,
            ))
        })
}

fn link_nft_get_owner_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "nft_get_owner",
            |mut caller: Caller<'_, ClarityWasmContext>,
             name_offset: i32,
             name_length: i32,
             mut asset_offset: i32,
             mut asset_length: i32,
             return_offset: i32,
             _return_length: i32| {
                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let contract_identifier =
                    caller.data().contract_context().contract_identifier.clone();
                let epoch = caller.data_mut().global_context.epoch_id;

                // Retrieve the token name
                let name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;
                let asset_name = ClarityName::try_from(name.clone())?;

                let nft_metadata = caller
                    .data()
                    .contract_context()
                    .meta_nft
                    .get(&asset_name)
                    .ok_or(CheckErrors::NoSuchNFT(asset_name.to_string()))?
                    .clone();

                let expected_asset_type = &nft_metadata.key_type;

                // Read in the NFT identifier from the Wasm memory
                if is_in_memory_type(expected_asset_type) {
                    (asset_offset, asset_length) =
                        read_indirect_offset_and_length(memory, &mut caller, asset_offset)?;
                }
                let asset = read_from_wasm(
                    memory,
                    &mut caller,
                    expected_asset_type,
                    asset_offset,
                    asset_length,
                    epoch,
                )?;

                let _asset_size = asset.serialized_size()? as u64;

                // runtime_cost(ClarityCostFunction::NftOwner, env, asset_size)?;

                if !expected_asset_type.admits(&caller.data().global_context.epoch_id, &asset)? {
                    return Err(
                        CheckErrors::TypeValueError(expected_asset_type.clone(), asset).into(),
                    );
                }

                match caller.data_mut().global_context.database.get_nft_owner(
                    &contract_identifier,
                    asset_name.as_str(),
                    &asset,
                    expected_asset_type,
                ) {
                    Ok(owner) => {
                        // Write the principal to the return buffer
                        let memory = caller
                            .get_export("memory")
                            .and_then(|export| export.into_memory())
                            .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                        let (_, bytes_written) = write_to_wasm(
                            caller,
                            memory,
                            &TypeSignature::PrincipalType,
                            return_offset,
                            return_offset,
                            &Value::Principal(owner),
                            false,
                        )?;

                        Ok((1i32, return_offset, bytes_written))
                    }
                    Err(Error::Runtime(RuntimeErrorType::NoSuchToken, _)) => Ok((0i32, 0i32, 0i32)),
                    Err(e) => Err(e)?,
                }
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "nft_get_owner".to_string(),
                e,
            ))
        })
}

fn link_nft_burn_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "nft_burn",
            |mut caller: Caller<'_, ClarityWasmContext>,
             name_offset: i32,
             name_length: i32,
             mut asset_offset: i32,
             mut asset_length: i32,
             sender_offset: i32,
             sender_length: i32| {
                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let contract_identifier =
                    caller.data().contract_context().contract_identifier.clone();

                let epoch = caller.data_mut().global_context.epoch_id;

                // Retrieve the token name
                let name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;
                let asset_name = ClarityName::try_from(name.clone())?;

                let nft_metadata = caller
                    .data()
                    .contract_context()
                    .meta_nft
                    .get(&asset_name)
                    .ok_or(CheckErrors::NoSuchNFT(asset_name.to_string()))?
                    .clone();

                let expected_asset_type = &nft_metadata.key_type;

                // Read in the NFT identifier from the Wasm memory
                if is_in_memory_type(expected_asset_type) {
                    (asset_offset, asset_length) =
                        read_indirect_offset_and_length(memory, &mut caller, asset_offset)?;
                }
                let asset = read_from_wasm(
                    memory,
                    &mut caller,
                    expected_asset_type,
                    asset_offset,
                    asset_length,
                    epoch,
                )?;

                // Read the sender principal from the Wasm memory
                let value = read_from_wasm(
                    memory,
                    &mut caller,
                    &TypeSignature::PrincipalType,
                    sender_offset,
                    sender_length,
                    epoch,
                )?;
                let sender_principal = value_as_principal(&value)?;

                let asset_size = asset.serialized_size()? as u64;

                // runtime_cost(ClarityCostFunction::NftBurn, env, asset_size)?;

                if !expected_asset_type.admits(&caller.data().global_context.epoch_id, &asset)? {
                    return Err(
                        CheckErrors::TypeValueError(expected_asset_type.clone(), asset).into(),
                    );
                }

                let owner = match caller.data_mut().global_context.database.get_nft_owner(
                    &contract_identifier,
                    asset_name.as_str(),
                    &asset,
                    expected_asset_type,
                ) {
                    Err(Error::Runtime(RuntimeErrorType::NoSuchToken, _)) => {
                        return Ok((0i32, 0i32, BurnAssetErrorCodes::DOES_NOT_EXIST as i64, 0i64));
                    }
                    Ok(owner) => Ok(owner),
                    Err(e) => Err(e),
                }?;

                if &owner != sender_principal {
                    return Ok((0i32, 0i32, BurnAssetErrorCodes::NOT_OWNED_BY as i64, 0i64));
                }

                caller
                    .data_mut()
                    .global_context
                    .add_memory(TypeSignature::PrincipalType.size()? as u64)
                    .map_err(Error::from)?;
                caller
                    .data_mut()
                    .global_context
                    .add_memory(asset_size)
                    .map_err(Error::from)?;

                caller.data_mut().global_context.database.burn_nft(
                    &contract_identifier,
                    asset_name.as_str(),
                    &asset,
                    expected_asset_type,
                    &epoch,
                )?;

                caller.data_mut().global_context.log_asset_transfer(
                    sender_principal,
                    &contract_identifier,
                    &asset_name,
                    asset.clone(),
                )?;

                let asset_identifier = AssetIdentifier {
                    contract_identifier,
                    asset_name: asset_name.clone(),
                };
                caller.data_mut().register_nft_burn_event(
                    sender_principal.clone(),
                    asset,
                    asset_identifier,
                )?;

                // (ok true)
                Ok((1i32, 132, 0i64, 0i64))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "nft_burn".to_string(),
                e,
            ))
        })
}

fn link_nft_mint_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "nft_mint",
            |mut caller: Caller<'_, ClarityWasmContext>,
             name_offset: i32,
             name_length: i32,
             mut asset_offset: i32,
             mut asset_length: i32,
             recipient_offset: i32,
             recipient_length: i32| {
                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let contract_identifier =
                    caller.data().contract_context().contract_identifier.clone();

                let epoch = caller.data_mut().global_context.epoch_id;

                // Retrieve the token name
                let name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;
                let asset_name = ClarityName::try_from(name.clone())?;

                let nft_metadata = caller
                    .data()
                    .contract_context()
                    .meta_nft
                    .get(&asset_name)
                    .ok_or(CheckErrors::NoSuchNFT(asset_name.to_string()))?
                    .clone();

                let expected_asset_type = &nft_metadata.key_type;

                // Read in the NFT identifier from the Wasm memory
                if is_in_memory_type(expected_asset_type) {
                    (asset_offset, asset_length) =
                        read_indirect_offset_and_length(memory, &mut caller, asset_offset)?;
                }
                let asset = read_from_wasm(
                    memory,
                    &mut caller,
                    expected_asset_type,
                    asset_offset,
                    asset_length,
                    epoch,
                )?;

                // Read the recipient principal from the Wasm memory
                let value = read_from_wasm(
                    memory,
                    &mut caller,
                    &TypeSignature::PrincipalType,
                    recipient_offset,
                    recipient_length,
                    epoch,
                )?;
                let to_principal = value_as_principal(&value)?;

                let asset_size = asset.serialized_size()? as u64;
                // runtime_cost(ClarityCostFunction::NftMint, env, asset_size)?;

                if !expected_asset_type.admits(&caller.data().global_context.epoch_id, &asset)? {
                    return Err(
                        CheckErrors::TypeValueError(expected_asset_type.clone(), asset).into(),
                    );
                }

                match caller.data_mut().global_context.database.get_nft_owner(
                    &contract_identifier,
                    asset_name.as_str(),
                    &asset,
                    expected_asset_type,
                ) {
                    Err(Error::Runtime(RuntimeErrorType::NoSuchToken, _)) => Ok(()),
                    Ok(_owner) => {
                        return Ok((0i32, 0i32, MintAssetErrorCodes::ALREADY_EXIST as i64, 0i64))
                    }
                    Err(e) => Err(e),
                }?;

                caller
                    .data_mut()
                    .global_context
                    .add_memory(TypeSignature::PrincipalType.size()? as u64)
                    .map_err(Error::from)?;
                caller
                    .data_mut()
                    .global_context
                    .add_memory(asset_size)
                    .map_err(Error::from)?;

                caller.data_mut().global_context.database.set_nft_owner(
                    &contract_identifier,
                    asset_name.as_str(),
                    &asset,
                    to_principal,
                    expected_asset_type,
                    &epoch,
                )?;

                let asset_identifier = AssetIdentifier {
                    contract_identifier,
                    asset_name: asset_name.clone(),
                };
                caller.data_mut().register_nft_mint_event(
                    to_principal.clone(),
                    asset,
                    asset_identifier,
                )?;

                // (ok true)
                Ok((1i32, 132, 0i64, 0i64))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "nft_mint".to_string(),
                e,
            ))
        })
}

fn link_nft_transfer_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "nft_transfer",
            |mut caller: Caller<'_, ClarityWasmContext>,
             name_offset: i32,
             name_length: i32,
             mut asset_offset: i32,
             mut asset_length: i32,
             sender_offset: i32,
             sender_length: i32,
             recipient_offset: i32,
             recipient_length: i32| {
                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let contract_identifier =
                    caller.data().contract_context().contract_identifier.clone();

                let epoch = caller.data_mut().global_context.epoch_id;

                // Retrieve the token name
                let name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;
                let asset_name = ClarityName::try_from(name.clone())?;

                let nft_metadata = caller
                    .data()
                    .contract_context()
                    .meta_nft
                    .get(&asset_name)
                    .ok_or(CheckErrors::NoSuchNFT(asset_name.to_string()))?
                    .clone();

                let expected_asset_type = &nft_metadata.key_type;

                // Read in the NFT identifier from the Wasm memory
                if is_in_memory_type(expected_asset_type) {
                    (asset_offset, asset_length) =
                        read_indirect_offset_and_length(memory, &mut caller, asset_offset)?;
                }
                let asset = read_from_wasm(
                    memory,
                    &mut caller,
                    expected_asset_type,
                    asset_offset,
                    asset_length,
                    epoch,
                )?;

                // Read the sender principal from the Wasm memory
                let value = read_from_wasm(
                    memory,
                    &mut caller,
                    &TypeSignature::PrincipalType,
                    sender_offset,
                    sender_length,
                    epoch,
                )?;
                let from_principal = value_as_principal(&value)?;

                // Read the recipient principal from the Wasm memory
                let value = read_from_wasm(
                    memory,
                    &mut caller,
                    &TypeSignature::PrincipalType,
                    recipient_offset,
                    recipient_length,
                    epoch,
                )?;
                let to_principal = value_as_principal(&value)?;

                let asset_size = asset.serialized_size()? as u64;
                // runtime_cost(ClarityCostFunction::NftTransfer, env, asset_size)?;

                if !expected_asset_type.admits(&caller.data().global_context.epoch_id, &asset)? {
                    return Err(
                        CheckErrors::TypeValueError(expected_asset_type.clone(), asset).into(),
                    );
                }

                if from_principal == to_principal {
                    return Ok((
                        0i32,
                        0i32,
                        TransferAssetErrorCodes::SENDER_IS_RECIPIENT as i64,
                        0i64,
                    ));
                }

                let current_owner = match caller.data_mut().global_context.database.get_nft_owner(
                    &contract_identifier,
                    asset_name.as_str(),
                    &asset,
                    expected_asset_type,
                ) {
                    Ok(owner) => Ok(owner),
                    Err(Error::Runtime(RuntimeErrorType::NoSuchToken, _)) => {
                        return Ok((
                            0i32,
                            0i32,
                            TransferAssetErrorCodes::DOES_NOT_EXIST as i64,
                            0i64,
                        ))
                    }
                    Err(e) => Err(e),
                }?;

                if current_owner != *from_principal {
                    return Ok((
                        0i32,
                        0i32,
                        TransferAssetErrorCodes::NOT_OWNED_BY as i64,
                        0i64,
                    ));
                }

                caller
                    .data_mut()
                    .global_context
                    .add_memory(TypeSignature::PrincipalType.size()? as u64)
                    .map_err(Error::from)?;
                caller
                    .data_mut()
                    .global_context
                    .add_memory(asset_size)
                    .map_err(Error::from)?;

                caller.data_mut().global_context.database.set_nft_owner(
                    &contract_identifier,
                    asset_name.as_str(),
                    &asset,
                    to_principal,
                    expected_asset_type,
                    &epoch,
                )?;

                caller.data_mut().global_context.log_asset_transfer(
                    from_principal,
                    &contract_identifier,
                    &asset_name,
                    asset.clone(),
                )?;

                let asset_identifier = AssetIdentifier {
                    contract_identifier,
                    asset_name,
                };
                caller.data_mut().register_nft_transfer_event(
                    from_principal.clone(),
                    to_principal.clone(),
                    asset,
                    asset_identifier,
                )?;

                // (ok true)
                Ok((1i32, 132, 0i64, 0i64))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "nft_transfer".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `map_get`, into the Wasm module.
/// This function is called for the `map-get?` expression.
fn link_map_get_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "map_get",
            |mut caller: Caller<'_, ClarityWasmContext>,
             name_offset: i32,
             name_length: i32,
             mut key_offset: i32,
             mut key_length: i32,
             return_offset: i32,
             _return_length: i32| {
                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                // Retrieve the map name
                let map_name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;

                let contract = caller.data().contract_context().contract_identifier.clone();
                let epoch = caller.data_mut().global_context.epoch_id;

                // Retrieve the metadata for this map
                let data_types = caller
                    .data()
                    .contract_context()
                    .meta_data_map
                    .get(map_name.as_str())
                    .ok_or(CheckErrors::NoSuchMap(map_name.to_string()))?
                    .clone();

                // Read in the key from the Wasm memory
                if is_in_memory_type(&data_types.key_type) {
                    (key_offset, key_length) =
                        read_indirect_offset_and_length(memory, &mut caller, key_offset)?;
                }
                let key = read_from_wasm(
                    memory,
                    &mut caller,
                    &data_types.key_type,
                    key_offset,
                    key_length,
                    epoch,
                )?;

                let result = caller
                    .data_mut()
                    .global_context
                    .database
                    .fetch_entry_with_size(&contract, &map_name, &key, &data_types, &epoch);

                let _result_size = match &result {
                    Ok(data) => data.serialized_byte_len,
                    Err(_e) => (data_types.value_type.size()? + data_types.key_type.size()?) as u64,
                };

                // runtime_cost(ClarityCostFunction::FetchEntry, env, result_size)?;

                let value = result.map(|data| data.value)?;

                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let ty = TypeSignature::OptionalType(Box::new(data_types.value_type));
                write_to_wasm(
                    &mut caller,
                    memory,
                    &ty,
                    return_offset,
                    return_offset + get_type_size(&ty),
                    &value,
                    true,
                )?;

                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "map_get".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `map_set`, into the Wasm module.
/// This function is called for the `map-set` expression.
fn link_map_set_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "map_set",
            |mut caller: Caller<'_, ClarityWasmContext>,
             name_offset: i32,
             name_length: i32,
             mut key_offset: i32,
             mut key_length: i32,
             mut value_offset: i32,
             mut value_length: i32| {
                if caller.data().global_context.is_read_only() {
                    return Err(CheckErrors::WriteAttemptedInReadOnly.into());
                }

                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let epoch = caller.data_mut().global_context.epoch_id;

                // Retrieve the map name
                let map_name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;

                let contract = caller.data().contract_context().contract_identifier.clone();

                let data_types = caller
                    .data()
                    .contract_context()
                    .meta_data_map
                    .get(map_name.as_str())
                    .ok_or(Error::Unchecked(CheckErrors::NoSuchMap(
                        map_name.to_string(),
                    )))?
                    .clone();

                // Read in the key from the Wasm memory
                if is_in_memory_type(&data_types.key_type) {
                    (key_offset, key_length) =
                        read_indirect_offset_and_length(memory, &mut caller, key_offset)?;
                }
                let key = read_from_wasm(
                    memory,
                    &mut caller,
                    &data_types.key_type,
                    key_offset,
                    key_length,
                    epoch,
                )?;

                // Read in the value from the Wasm memory
                if is_in_memory_type(&data_types.value_type) {
                    (value_offset, value_length) =
                        read_indirect_offset_and_length(memory, &mut caller, value_offset)?;
                }
                let value = read_from_wasm(
                    memory,
                    &mut caller,
                    &data_types.value_type,
                    value_offset,
                    value_length,
                    epoch,
                )?;

                // Store the value in the map in the global context
                let result = caller.data_mut().global_context.database.set_entry(
                    &contract,
                    map_name.as_str(),
                    key,
                    value,
                    &data_types,
                    &epoch,
                );

                let result_size = match &result {
                    Ok(data) => data.serialized_byte_len,
                    Err(_e) => (data_types.value_type.size()? + data_types.key_type.size()?) as u64,
                };

                // runtime_cost(ClarityCostFunction::SetEntry, env, result_size)?;

                caller
                    .data_mut()
                    .global_context
                    .add_memory(result_size)
                    .map_err(Error::from)?;

                let value = result.map(|data| data.value)?;
                if let Value::Bool(true) = value {
                    Ok(1i32)
                } else {
                    Ok(0i32)
                }
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "map_set".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `map_insert`, into the Wasm module.
/// This function is called for the `map-insert` expression.
fn link_map_insert_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "map_insert",
            |mut caller: Caller<'_, ClarityWasmContext>,
             name_offset: i32,
             name_length: i32,
             mut key_offset: i32,
             mut key_length: i32,
             mut value_offset: i32,
             mut value_length: i32| {
                if caller.data().global_context.is_read_only() {
                    return Err(CheckErrors::WriteAttemptedInReadOnly.into());
                }

                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let epoch = caller.data_mut().global_context.epoch_id;

                // Retrieve the map name
                let map_name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;

                let contract = caller.data().contract_context().contract_identifier.clone();

                let data_types = caller
                    .data()
                    .contract_context()
                    .meta_data_map
                    .get(map_name.as_str())
                    .ok_or(Error::Unchecked(CheckErrors::NoSuchMap(
                        map_name.to_string(),
                    )))?
                    .clone();

                // Read in the key from the Wasm memory
                if is_in_memory_type(&data_types.key_type) {
                    (key_offset, key_length) =
                        read_indirect_offset_and_length(memory, &mut caller, key_offset)?;
                }
                let key = read_from_wasm(
                    memory,
                    &mut caller,
                    &data_types.key_type,
                    key_offset,
                    key_length,
                    epoch,
                )?;

                // Read in the value from the Wasm memory
                if is_in_memory_type(&data_types.value_type) {
                    (value_offset, value_length) =
                        read_indirect_offset_and_length(memory, &mut caller, value_offset)?;
                }
                let value = read_from_wasm(
                    memory,
                    &mut caller,
                    &data_types.value_type,
                    value_offset,
                    value_length,
                    epoch,
                )?;

                // Insert the value into the map
                let result = caller.data_mut().global_context.database.insert_entry(
                    &contract,
                    map_name.as_str(),
                    key,
                    value,
                    &data_types,
                    &epoch,
                );

                let result_size = match &result {
                    Ok(data) => data.serialized_byte_len,
                    Err(_e) => (data_types.value_type.size()? + data_types.key_type.size()?) as u64,
                };

                // runtime_cost(ClarityCostFunction::SetEntry, env, result_size)?;

                caller
                    .data_mut()
                    .global_context
                    .add_memory(result_size)
                    .map_err(Error::from)?;

                let value = result.map(|data| data.value)?;
                if let Value::Bool(true) = value {
                    Ok(1i32)
                } else {
                    Ok(0i32)
                }
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "map_insert".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `map_delete`, into the Wasm module.
/// This function is called for the `map-delete` expression.
fn link_map_delete_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "map_delete",
            |mut caller: Caller<'_, ClarityWasmContext>,
             name_offset: i32,
             name_length: i32,
             mut key_offset: i32,
             mut key_length: i32| {
                if caller.data().global_context.is_read_only() {
                    return Err(CheckErrors::WriteAttemptedInReadOnly.into());
                }

                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                // Retrieve the map name
                let map_name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;

                let contract = caller.data().contract_context().contract_identifier.clone();
                let epoch = caller.data_mut().global_context.epoch_id;

                let data_types = caller
                    .data()
                    .contract_context()
                    .meta_data_map
                    .get(map_name.as_str())
                    .ok_or(Error::Unchecked(CheckErrors::NoSuchMap(
                        map_name.to_string(),
                    )))?
                    .clone();

                // Read in the key from the Wasm memory
                if is_in_memory_type(&data_types.key_type) {
                    (key_offset, key_length) =
                        read_indirect_offset_and_length(memory, &mut caller, key_offset)?;
                }
                let key = read_from_wasm(
                    memory,
                    &mut caller,
                    &data_types.key_type,
                    key_offset,
                    key_length,
                    epoch,
                )?;

                // Delete the key from the map in the global context
                let result = caller.data_mut().global_context.database.delete_entry(
                    &contract,
                    map_name.as_str(),
                    &key,
                    &data_types,
                    &epoch,
                );

                let result_size = match &result {
                    Ok(data) => data.serialized_byte_len,
                    Err(_e) => (data_types.value_type.size()? + data_types.key_type.size()?) as u64,
                };

                // runtime_cost(ClarityCostFunction::SetEntry, env, result_size)?;

                caller
                    .data_mut()
                    .global_context
                    .add_memory(result_size)
                    .map_err(Error::from)?;

                let value = result.map(|data| data.value)?;
                if let Value::Bool(true) = value {
                    Ok(1i32)
                } else {
                    Ok(0i32)
                }
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "map_delete".to_string(),
                e,
            ))
        })
}

fn check_height_valid(
    caller: &mut Caller<'_, ClarityWasmContext>,
    memory: Memory,
    height_lo: i64,
    height_hi: i64,
    return_offset: i32,
) -> Result<Option<u32>, Error> {
    let height = ((height_hi as u128) << 64) | ((height_lo as u64) as u128);

    let height_value = match u32::try_from(height) {
        Ok(result) => result,
        _ => {
            // Write a 0 to the return buffer for `none`
            write_to_wasm(
                caller,
                memory,
                &TypeSignature::BoolType,
                return_offset,
                return_offset + get_type_size(&TypeSignature::BoolType),
                &Value::Bool(false),
                true,
            )?;
            return Ok(None);
        }
    };

    let current_block_height = caller
        .data_mut()
        .global_context
        .database
        .get_current_block_height();
    if height_value >= current_block_height {
        // Write a 0 to the return buffer for `none`
        write_to_wasm(
            caller,
            memory,
            &TypeSignature::BoolType,
            return_offset,
            return_offset + get_type_size(&TypeSignature::BoolType),
            &Value::Bool(false),
            true,
        )?;
        return Ok(None);
    }
    Ok(Some(height_value))
}

/// Link host interface function, `get_block_info_time`, into the Wasm module.
/// This function is called for the `get-block-info? time` expression.
fn link_get_block_info_time_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_block_info_time_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                if let Some(height_value) =
                    check_height_valid(&mut caller, memory, height_lo, height_hi, return_offset)?
                {
                    let block_time = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_block_time(height_value)?;
                    let (result, result_ty) =
                        (Value::UInt(block_time as u128), TypeSignature::UIntType);
                    let ty = TypeSignature::OptionalType(Box::new(result_ty));
                    write_to_wasm(
                        &mut caller,
                        memory,
                        &ty,
                        return_offset,
                        return_offset + get_type_size(&ty),
                        &Value::some(result)?,
                        true,
                    )?;
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_block_info_time_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_block_info_vrf_seed`, into the Wasm module.
/// This function is called for the `get-block-info? vrf-seed` expression.
fn link_get_block_info_vrf_seed_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_block_info_vrf_seed_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                if let Some(height_value) =
                    check_height_valid(&mut caller, memory, height_lo, height_hi, return_offset)?
                {
                    let vrf_seed = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_block_vrf_seed(height_value)?;
                    let data = vrf_seed.as_bytes().to_vec();
                    let len = data.len() as u32;
                    let (result, result_ty) = (
                        Value::Sequence(SequenceData::Buffer(BuffData { data })),
                        TypeSignature::SequenceType(SequenceSubtype::BufferType(
                            BufferLength::try_from(len)?,
                        )),
                    );
                    let ty = TypeSignature::OptionalType(Box::new(result_ty));

                    write_to_wasm(
                        &mut caller,
                        memory,
                        &ty,
                        return_offset,
                        return_offset + get_type_size(&ty),
                        &Value::some(result)?,
                        true,
                    )?;
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_block_info_vrf_seed_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_block_info_header_hash`, into the Wasm module.
/// This function is called for the `get-block-info? header-hash` expression.
fn link_get_block_info_header_hash_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_block_info_header_hash_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                if let Some(height_value) =
                    check_height_valid(&mut caller, memory, height_lo, height_hi, return_offset)?
                {
                    let header_hash = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_block_header_hash(height_value)?;
                    let data = header_hash.as_bytes().to_vec();
                    let len = data.len() as u32;
                    let (result, result_ty) = (
                        Value::Sequence(SequenceData::Buffer(BuffData { data })),
                        TypeSignature::SequenceType(SequenceSubtype::BufferType(
                            BufferLength::try_from(len)?,
                        )),
                    );
                    let ty = TypeSignature::OptionalType(Box::new(result_ty));

                    write_to_wasm(
                        &mut caller,
                        memory,
                        &ty,
                        return_offset,
                        return_offset + get_type_size(&ty),
                        &Value::some(result)?,
                        true,
                    )?;
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_block_info_header_hash_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_block_info_burnchain_header_hash`, into the Wasm module.
/// This function is called for the `get-block-info? burnchain-header-hash` expression.
fn link_get_block_info_burnchain_header_hash_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_block_info_burnchain_header_hash_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                if let Some(height_value) =
                    check_height_valid(&mut caller, memory, height_lo, height_hi, return_offset)?
                {
                    let burnchain_header_hash = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_burnchain_block_header_hash(height_value)?;
                    let data = burnchain_header_hash.as_bytes().to_vec();
                    let len = data.len() as u32;
                    let (result, result_ty) = (
                        Value::Sequence(SequenceData::Buffer(BuffData { data })),
                        TypeSignature::SequenceType(SequenceSubtype::BufferType(
                            BufferLength::try_from(len)?,
                        )),
                    );
                    let ty = TypeSignature::OptionalType(Box::new(result_ty));

                    write_to_wasm(
                        &mut caller,
                        memory,
                        &ty,
                        return_offset,
                        return_offset + get_type_size(&ty),
                        &Value::some(result)?,
                        true,
                    )?;
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_block_info_burnchain_header_hash_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_block_info_id_header_hash`, into the Wasm module.
/// This function is called for the `get-block-info? id-header-hash` expression.
fn link_get_block_info_identity_header_hash_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_block_info_identity_header_hash_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                if let Some(height_value) =
                    check_height_valid(&mut caller, memory, height_lo, height_hi, return_offset)?
                {
                    let id_header_hash = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_index_block_header_hash(height_value)?;
                    let data = id_header_hash.as_bytes().to_vec();
                    let len = data.len() as u32;
                    let (result, result_ty) = (
                        Value::Sequence(SequenceData::Buffer(BuffData { data })),
                        TypeSignature::SequenceType(SequenceSubtype::BufferType(
                            BufferLength::try_from(len)?,
                        )),
                    );
                    let ty = TypeSignature::OptionalType(Box::new(result_ty));

                    write_to_wasm(
                        &mut caller,
                        memory,
                        &ty,
                        return_offset,
                        return_offset + get_type_size(&ty),
                        &Value::some(result)?,
                        true,
                    )?;
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_block_info_identity_header_hash_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_block_info_miner_address`, into the Wasm module.
/// This function is called for the `get-block-info? miner-address` expression.
fn link_get_block_info_miner_address_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_block_info_miner_address_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                if let Some(height_value) =
                    check_height_valid(&mut caller, memory, height_lo, height_hi, return_offset)?
                {
                    let miner_address = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_miner_address(height_value)?;
                    let (result, result_ty) =
                        (Value::from(miner_address), TypeSignature::PrincipalType);
                    let ty = TypeSignature::OptionalType(Box::new(result_ty));

                    write_to_wasm(
                        &mut caller,
                        memory,
                        &ty,
                        return_offset,
                        return_offset + get_type_size(&ty),
                        &Value::some(result)?,
                        true,
                    )?;
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_block_info_miner_address_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_block_info_miner_spend_winner`, into the Wasm module.
/// This function is called for the `get-block-info? miner-spend-winner` expression.
fn link_get_block_info_miner_spend_winner_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_block_info_miner_spend_winner_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                if let Some(height_value) =
                    check_height_valid(&mut caller, memory, height_lo, height_hi, return_offset)?
                {
                    let winner_spend = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_miner_spend_winner(height_value)?;
                    let (result, result_ty) = (Value::UInt(winner_spend), TypeSignature::UIntType);
                    let ty = TypeSignature::OptionalType(Box::new(result_ty));

                    write_to_wasm(
                        &mut caller,
                        memory,
                        &ty,
                        return_offset,
                        return_offset + get_type_size(&ty),
                        &Value::some(result)?,
                        true,
                    )?;
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_block_info_miner_spend_winner_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_block_info_miner_spend_total`, into the Wasm module.
/// This function is called for the `get-block-info? miner-spend-total` expression.
fn link_get_block_info_miner_spend_total_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_block_info_miner_spend_total_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                if let Some(height_value) =
                    check_height_valid(&mut caller, memory, height_lo, height_hi, return_offset)?
                {
                    let total_spend = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_miner_spend_total(height_value)?;
                    let (result, result_ty) = (Value::UInt(total_spend), TypeSignature::UIntType);
                    let ty = TypeSignature::OptionalType(Box::new(result_ty));

                    write_to_wasm(
                        &mut caller,
                        memory,
                        &ty,
                        return_offset,
                        return_offset + get_type_size(&ty),
                        &Value::some(result)?,
                        true,
                    )?;
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_block_info_miner_spend_total_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_block_info_block_reward`, into the Wasm module.
/// This function is called for the `get-block-info? block-reward` expression.
fn link_get_block_info_block_reward_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_block_info_block_reward_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                if let Some(height_value) =
                    check_height_valid(&mut caller, memory, height_lo, height_hi, return_offset)?
                {
                    let block_reward_opt = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_block_reward(height_value)?;
                    let (result, result_ty) = (
                        match block_reward_opt {
                            Some(x) => Value::UInt(x),
                            None => {
                                // Write a 0 to the return buffer for `none`
                                write_to_wasm(
                                    &mut caller,
                                    memory,
                                    &TypeSignature::BoolType,
                                    return_offset,
                                    return_offset + get_type_size(&TypeSignature::BoolType),
                                    &Value::Bool(false),
                                    true,
                                )?;
                                return Ok(());
                            }
                        },
                        TypeSignature::UIntType,
                    );
                    let ty = TypeSignature::OptionalType(Box::new(result_ty));

                    write_to_wasm(
                        &mut caller,
                        memory,
                        &ty,
                        return_offset,
                        return_offset + get_type_size(&ty),
                        &Value::some(result)?,
                        true,
                    )?;
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_block_info_block_reward_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_burn_block_info_header_hash_property`, into the Wasm module.
/// This function is called for the `get-burn-block-info? header-hash` expression.
fn link_get_burn_block_info_header_hash_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_burn_block_info_header_hash_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;
                let height = ((height_hi as u128) << 64) | ((height_lo as u64) as u128);

                // Note: we assume that we will not have a height bigger than u32::MAX.
                let height_value = match u32::try_from(height) {
                    Ok(result) => result,
                    _ => {
                        // Write a 0 to the return buffer for `none`
                        write_to_wasm(
                            &mut caller,
                            memory,
                            &TypeSignature::BoolType,
                            return_offset,
                            return_offset + get_type_size(&TypeSignature::BoolType),
                            &Value::Bool(false),
                            true,
                        )?;
                        return Ok(());
                    }
                };
                let burnchain_header_hash_opt = caller
                    .data_mut()
                    .global_context
                    .database
                    .get_burnchain_block_header_hash_for_burnchain_height(height_value)?;
                let (result, result_ty) = (
                    match burnchain_header_hash_opt {
                        Some(burnchain_header_hash) => {
                            Value::some(Value::Sequence(SequenceData::Buffer(BuffData {
                                data: burnchain_header_hash.as_bytes().to_vec(),
                            })))?
                        }
                        None => Value::none(),
                    },
                    TypeSignature::OptionalType(Box::new(BUFF_32.clone())),
                );

                write_to_wasm(
                    &mut caller,
                    memory,
                    &result_ty,
                    return_offset,
                    return_offset + get_type_size(&result_ty),
                    &result,
                    true,
                )?;
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_burn_block_info_header_hash_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_burn_block_info_pox_addrs_property`, into the Wasm module.
/// This function is called for the `get-burn-block-info? pox-addrs` expression.
fn link_get_burn_block_info_pox_addrs_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_burn_block_info_pox_addrs_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let height = ((height_hi as u128) << 64) | ((height_lo as u64) as u128);

                // Note: we assume that we will not have a height bigger than u32::MAX.
                let height_value = match u32::try_from(height) {
                    Ok(result) => result,
                    _ => {
                        // Write a 0 to the return buffer for `none`
                        write_to_wasm(
                            &mut caller,
                            memory,
                            &TypeSignature::BoolType,
                            return_offset,
                            return_offset + get_type_size(&TypeSignature::BoolType),
                            &Value::Bool(false),
                            true,
                        )?;
                        return Ok(());
                    }
                };

                let pox_addrs_and_payout = caller
                    .data_mut()
                    .global_context
                    .database
                    .get_pox_payout_addrs_for_burnchain_height(height_value)?;
                let addr_ty: TypeSignature = TupleTypeSignature::try_from(vec![
                    ("hashbytes".into(), BUFF_32.clone()),
                    ("version".into(), BUFF_1.clone()),
                ])?
                .into();
                let addrs_ty = TypeSignature::list_of(addr_ty.clone(), 2)?;
                let tuple_ty = TupleTypeSignature::try_from(vec![
                    ("addrs".into(), addrs_ty),
                    ("payout".into(), TypeSignature::UIntType),
                ])?;
                let value = match pox_addrs_and_payout {
                    Some((addrs, payout)) => {
                        Value::some(Value::Tuple(TupleData::from_data(vec![
                            (
                                "addrs".into(),
                                Value::list_with_type(
                                    &caller.data_mut().global_context.epoch_id,
                                    addrs.into_iter().map(Value::Tuple).collect(),
                                    ListTypeData::new_list(addr_ty, 2)?,
                                )?,
                            ),
                            ("payout".into(), Value::UInt(payout)),
                        ])?))?
                    }
                    None => Value::none(),
                };
                let ty = TypeSignature::OptionalType(Box::new(tuple_ty.into()));

                write_to_wasm(
                    &mut caller,
                    memory,
                    &ty,
                    return_offset,
                    return_offset + get_type_size(&ty),
                    &value,
                    true,
                )?;
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_burn_block_info_pox_addrs_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_stacks_block_info_time`, into the Wasm module.
/// This function is called for the `get-stacks-block-info? id-header-hash` expression.
fn link_get_stacks_block_info_time_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_stacks_block_info_time_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;
                // Get the memory from the caller
                if let Some(height_value) =
                    check_height_valid(&mut caller, memory, height_lo, height_hi, return_offset)?
                {
                    let block_time = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_block_time(height_value)?;
                    let (result, result_ty) =
                        (Value::UInt(block_time as u128), TypeSignature::UIntType);
                    let ty = TypeSignature::OptionalType(Box::new(result_ty));
                    write_to_wasm(
                        &mut caller,
                        memory,
                        &ty,
                        return_offset,
                        return_offset + get_type_size(&ty),
                        &Value::some(result)?,
                        true,
                    )?;
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_stacks_block_info_time_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_stacks_block_info_header_hash`, into the Wasm module.
/// This function is called for the `get-stacks-block-info? header-hash` expression.
fn link_get_stacks_block_info_header_hash_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_stacks_block_info_header_hash_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                // Get the memory from the caller
                if let Some(height_value) =
                    check_height_valid(&mut caller, memory, height_lo, height_hi, return_offset)?
                {
                    let header_hash = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_block_header_hash(height_value)?;
                    let data = header_hash.as_bytes().to_vec();
                    let len = data.len() as u32;
                    let (result, result_ty) = (
                        Value::Sequence(SequenceData::Buffer(BuffData { data })),
                        TypeSignature::SequenceType(SequenceSubtype::BufferType(
                            BufferLength::try_from(len)?,
                        )),
                    );
                    let ty = TypeSignature::OptionalType(Box::new(result_ty));
                    write_to_wasm(
                        &mut caller,
                        memory,
                        &ty,
                        return_offset,
                        return_offset + get_type_size(&ty),
                        &Value::some(result)?,
                        true,
                    )?;
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_stacks_block_info_header_hash_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_stacks_block_info_identity_header_hash_`, into the Wasm module.
/// This function is called for the `get-stacks-block-info? time` expression.
fn link_get_stacks_block_info_identity_header_hash_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_stacks_block_info_identity_header_hash_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                if let Some(height_value) =
                    check_height_valid(&mut caller, memory, height_lo, height_hi, return_offset)?
                {
                    let id_header_hash = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_index_block_header_hash(height_value)?;
                    let data = id_header_hash.as_bytes().to_vec();
                    let len = data.len() as u32;
                    let (result, result_ty) = (
                        Value::Sequence(SequenceData::Buffer(BuffData { data })),
                        TypeSignature::SequenceType(SequenceSubtype::BufferType(
                            BufferLength::try_from(len)?,
                        )),
                    );
                    let ty = TypeSignature::OptionalType(Box::new(result_ty));

                    write_to_wasm(
                        &mut caller,
                        memory,
                        &ty,
                        return_offset,
                        return_offset + get_type_size(&ty),
                        &Value::some(result)?,
                        true,
                    )?;
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_stacks_block_info_identity_header_hash_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_tenure_info_burnchain_header_hash`, into the Wasm module.
/// This function is called for the `get-tenure-info? burnchain-header-hash` expression.
fn link_get_tenure_info_burnchain_header_hash_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_tenure_info_burnchain_header_hash_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                if let Some(height_value) =
                    check_height_valid(&mut caller, memory, height_lo, height_hi, return_offset)?
                {
                    let burnchain_header_hash = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_burnchain_block_header_hash(height_value)?;
                    let data = burnchain_header_hash.as_bytes().to_vec();
                    let len = data.len() as u32;
                    let (result, result_ty) = (
                        Value::Sequence(SequenceData::Buffer(BuffData { data })),
                        TypeSignature::SequenceType(SequenceSubtype::BufferType(
                            BufferLength::try_from(len)?,
                        )),
                    );
                    let ty = TypeSignature::OptionalType(Box::new(result_ty));

                    write_to_wasm(
                        &mut caller,
                        memory,
                        &ty,
                        return_offset,
                        return_offset + get_type_size(&ty),
                        &Value::some(result)?,
                        true,
                    )?;
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_tenure_info_burnchain_header_hash_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_tenure_info_miner_address`, into the Wasm module.
/// This function is called for the `get-tenure-info? miner-address` expression.
fn link_get_tenure_info_miner_address_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_tenure_info_miner_address_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                if let Some(height_value) =
                    check_height_valid(&mut caller, memory, height_lo, height_hi, return_offset)?
                {
                    let miner_address = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_miner_address(height_value)?;
                    let (result, result_ty) =
                        (Value::from(miner_address), TypeSignature::PrincipalType);
                    let ty = TypeSignature::OptionalType(Box::new(result_ty));

                    write_to_wasm(
                        &mut caller,
                        memory,
                        &ty,
                        return_offset,
                        return_offset + get_type_size(&ty),
                        &Value::some(result)?,
                        true,
                    )?;
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_tenure_info_miner_address_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_tenure_info_time`, into the Wasm module.
/// This function is called for the `get-tenure-info? time` expression.
fn link_get_tenure_info_time_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_tenure_info_time_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                if let Some(height_value) =
                    check_height_valid(&mut caller, memory, height_lo, height_hi, return_offset)?
                {
                    let block_time = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_burn_block_time(height_value, None)?;
                    let (result, result_ty) =
                        (Value::UInt(block_time as u128), TypeSignature::UIntType);
                    let ty = TypeSignature::OptionalType(Box::new(result_ty));
                    write_to_wasm(
                        &mut caller,
                        memory,
                        &ty,
                        return_offset,
                        return_offset + get_type_size(&ty),
                        &Value::some(result)?,
                        true,
                    )?;
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_tenure_info_time_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_tenure_info_vrf_seed_property`, into the Wasm module.
/// This function is called for the `get-tenure-info? vrf-seed` expression.
fn link_get_tenure_info_vrf_seed_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_tenure_info_vrf_seed_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                if let Some(height_value) =
                    check_height_valid(&mut caller, memory, height_lo, height_hi, return_offset)?
                {
                    let vrf_seed = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_block_vrf_seed(height_value)?;
                    let data = vrf_seed.as_bytes().to_vec();
                    let len = data.len() as u32;
                    let (result, result_ty) = (
                        Value::Sequence(SequenceData::Buffer(BuffData { data })),
                        TypeSignature::SequenceType(SequenceSubtype::BufferType(
                            BufferLength::try_from(len)?,
                        )),
                    );
                    let ty = TypeSignature::OptionalType(Box::new(result_ty));

                    write_to_wasm(
                        &mut caller,
                        memory,
                        &ty,
                        return_offset,
                        return_offset + get_type_size(&ty),
                        &Value::some(result)?,
                        true,
                    )?;
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_tenure_info_vrf_seed_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_tenure_info_block_reward`, into the Wasm module.
/// This function is called for the `get-tenure-info? block-reward` expression.
fn link_get_tenure_info_block_reward_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_tenure_info_block_reward_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                if let Some(height_value) =
                    check_height_valid(&mut caller, memory, height_lo, height_hi, return_offset)?
                {
                    let block_reward_opt = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_block_reward(height_value)?;
                    let (result, result_ty) = (
                        match block_reward_opt {
                            Some(x) => Value::UInt(x),
                            None => {
                                // Write a 0 to the return buffer for `none`
                                write_to_wasm(
                                    &mut caller,
                                    memory,
                                    &TypeSignature::BoolType,
                                    return_offset,
                                    return_offset + get_type_size(&TypeSignature::BoolType),
                                    &Value::Bool(false),
                                    true,
                                )?;
                                return Ok(());
                            }
                        },
                        TypeSignature::UIntType,
                    );
                    let ty = TypeSignature::OptionalType(Box::new(result_ty));

                    write_to_wasm(
                        &mut caller,
                        memory,
                        &ty,
                        return_offset,
                        return_offset + get_type_size(&ty),
                        &Value::some(result)?,
                        true,
                    )?;
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_tenure_info_block_reward_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_tenure_info_miner_spend_total`, into the Wasm module.
/// This function is called for the `get-tenure-info? miner-spend-total` expression.
fn link_get_tenure_info_miner_spend_total_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_tenure_info_miner_spend_total_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                if let Some(height_value) =
                    check_height_valid(&mut caller, memory, height_lo, height_hi, return_offset)?
                {
                    let total_spend = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_miner_spend_total(height_value)?;
                    let (result, result_ty) = (Value::UInt(total_spend), TypeSignature::UIntType);
                    let ty = TypeSignature::OptionalType(Box::new(result_ty));

                    write_to_wasm(
                        &mut caller,
                        memory,
                        &ty,
                        return_offset,
                        return_offset + get_type_size(&ty),
                        &Value::some(result)?,
                        true,
                    )?;
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_tenure_info_miner_spend_total_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_tenure_info_miner_spend_winner`, into the Wasm module.
/// This function is called for the `get-tenure-info? miner-spend-winner` expression.
fn link_get_tenure_info_miner_spend_winner_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_tenure_info_miner_spend_winner_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                if let Some(height_value) =
                    check_height_valid(&mut caller, memory, height_lo, height_hi, return_offset)?
                {
                    let winner_spend = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_miner_spend_winner(height_value)?;
                    let (result, result_ty) = (Value::UInt(winner_spend), TypeSignature::UIntType);
                    let ty = TypeSignature::OptionalType(Box::new(result_ty));

                    write_to_wasm(
                        &mut caller,
                        memory,
                        &ty,
                        return_offset,
                        return_offset + get_type_size(&ty),
                        &Value::some(result)?,
                        true,
                    )?;
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_tenure_info_miner_spend_winner_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `contract_call`, into the Wasm module.
/// This function is called for `contract-call?`s.
fn link_contract_call_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "contract_call",
            |mut caller: Caller<'_, ClarityWasmContext>,
             trait_id_offset: i32,
             trait_id_length: i32,
             contract_offset: i32,
             contract_length: i32,
             function_offset: i32,
             function_length: i32,
             args_offset: i32,
             _args_length: i32,
             return_offset: i32,
             _return_length: i32| {
                // the second part of the contract_call cost (i.e., the load contract cost)
                //   is checked in `execute_contract`, and the function _application_ cost
                //   is checked in callables::DefinedFunction::execute_apply.
                // runtime_cost(ClarityCostFunction::ContractCall, env, 0)?;

                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let epoch = caller.data_mut().global_context.epoch_id;

                // Read the contract identifier from the Wasm memory
                let contract_val = read_from_wasm(
                    memory,
                    &mut caller,
                    &TypeSignature::PrincipalType,
                    contract_offset,
                    contract_length,
                    epoch,
                )?;
                let contract_id = match &contract_val {
                    Value::Principal(PrincipalData::Contract(contract_id)) => contract_id,
                    _ => {
                        return Err(CheckErrors::ContractCallExpectName.into());
                    }
                };

                // Read the function name from the Wasm memory
                let function_name = read_identifier_from_wasm(
                    memory,
                    &mut caller,
                    function_offset,
                    function_length,
                )?;

                // Retrieve the contract context for the contract we're calling
                let mut contract = caller
                    .data_mut()
                    .global_context
                    .database
                    .get_contract(contract_id)?;

                // Retrieve the function we're calling
                let function = contract
                    .contract_context
                    .functions
                    .get(function_name.as_str())
                    .ok_or(CheckErrors::NoSuchPublicFunction(
                        contract_id.to_string(),
                        function_name.to_string(),
                    ))?;

                let mut args = Vec::new();
                let mut args_sizes = Vec::new();
                let mut arg_offset = args_offset;
                // Read the arguments from the Wasm memory
                for arg_ty in function.get_arg_types() {
                    let arg =
                        read_from_wasm_indirect(memory, &mut caller, arg_ty, arg_offset, epoch)?;
                    args_sizes.push(arg.size()? as u64);
                    args.push(arg);

                    arg_offset += get_type_size(arg_ty);
                }

                let caller_contract: PrincipalData = caller
                    .data()
                    .contract_context()
                    .contract_identifier
                    .clone()
                    .into();
                caller.data_mut().push_caller(caller_contract.clone());

                let mut call_stack = caller.data().call_stack.clone();
                let sender = caller.data().sender.clone();
                let sponsor = caller.data().sponsor.clone();

                let short_circuit_cost = caller
                    .data_mut()
                    .global_context
                    .cost_track
                    .short_circuit_contract_call(
                        contract_id,
                        &ClarityName::try_from(function_name.clone())?,
                        &args_sizes,
                    )?;

                let mut env = Environment {
                    global_context: caller.data_mut().global_context,
                    contract_context: &contract.contract_context,
                    call_stack: &mut call_stack,
                    sender,
                    caller: Some(caller_contract),
                    sponsor,
                };

                let result = if short_circuit_cost {
                    env.run_free(|free_env| {
                        free_env.execute_contract_from_wasm(contract_id, &function_name, &args)
                    })
                } else {
                    env.execute_contract_from_wasm(contract_id, &function_name, &args)
                }?;

                // Write the result to the return buffer
                let return_ty = if trait_id_length == 0 {
                    // This is a direct call
                    function
                        .get_return_type()
                        .as_ref()
                        .ok_or(CheckErrors::DefineFunctionBadSignature)?
                } else {
                    // This is a dynamic call
                    let trait_id =
                        read_bytes_from_wasm(memory, &mut caller, trait_id_offset, trait_id_length)
                            .and_then(|bs| trait_identifier_from_bytes(&bs))?;
                    contract = if &trait_id.contract_identifier == contract_id {
                        contract
                    } else {
                        caller
                            .data_mut()
                            .global_context
                            .database
                            .get_contract(&trait_id.contract_identifier)?
                    };
                    contract
                        .contract_context
                        .defined_traits
                        .get(trait_id.name.as_str())
                        .and_then(|trait_functions| trait_functions.get(function_name.as_str()))
                        .map(|f_ty| &f_ty.returns)
                        .ok_or(CheckErrors::DefineFunctionBadSignature)?
                };

                write_to_wasm(
                    &mut caller,
                    memory,
                    return_ty,
                    return_offset,
                    return_offset + get_type_size(return_ty),
                    &result,
                    true,
                )?;

                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "contract_call".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `begin_public_call`, into the Wasm module.
/// This function is called before a local call to a public function.
fn link_begin_public_call_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "begin_public_call",
            |mut caller: Caller<'_, ClarityWasmContext>| {
                caller.data_mut().global_context.begin();
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "begin_public_call".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `begin_read_only_call`, into the Wasm module.
/// This function is called before a local call to a public function.
fn link_begin_read_only_call_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "begin_read_only_call",
            |mut caller: Caller<'_, ClarityWasmContext>| {
                caller.data_mut().global_context.begin_read_only();
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "begin_read_only_call".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `commit_call`, into the Wasm module.
/// This function is called after a local call to a public function to commit
/// it's changes into the global context.
fn link_commit_call_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "commit_call",
            |mut caller: Caller<'_, ClarityWasmContext>| {
                caller.data_mut().global_context.commit()?;
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "commit_call".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `roll_back_call`, into the Wasm module.
/// This function is called after a local call to roll back it's changes from
/// the global context. It is called when a public function errors, or a
/// read-only call completes.
fn link_roll_back_call_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "roll_back_call",
            |mut caller: Caller<'_, ClarityWasmContext>| {
                caller.data_mut().global_context.roll_back()?;
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "roll_back_call".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `print`, into the Wasm module.
/// This function is called for all contract print statements (`print`).
fn link_print_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "print",
            |mut caller: Caller<'_, ClarityWasmContext>,
             value_offset: i32,
             _value_length: i32,
             serialized_ty_offset: i32,
             serialized_ty_length: i32| {
                // runtime_cost(ClarityCostFunction::Print, env, input.size())?;

                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let serialized_ty = read_identifier_from_wasm(
                    memory,
                    &mut caller,
                    serialized_ty_offset,
                    serialized_ty_length,
                )?;

                let epoch = caller.data().global_context.epoch_id;
                let version = caller.data().contract_context().get_clarity_version();

                let value_ty = signature_from_string(&serialized_ty, *version, epoch)?;
                let clarity_val =
                    read_from_wasm_indirect(memory, &mut caller, &value_ty, value_offset, epoch)?;

                caller.data_mut().register_print_event(clarity_val)?;

                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| Error::Wasm(WasmError::UnableToLinkHostFunction("print".to_string(), e)))
}

/// Link host interface function, `enter_at_block`, into the Wasm module.
/// This function is called before evaluating the inner expression of an
/// `at-block` expression.
fn link_enter_at_block_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "enter_at_block",
            |mut caller: Caller<'_, ClarityWasmContext>,
             block_hash_offset: i32,
             block_hash_length: i32| {
                // runtime_cost(ClarityCostFunction::AtBlock, env, 0)?;

                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;
                let epoch = caller.data_mut().global_context.epoch_id;

                let block_hash = read_from_wasm(
                    memory,
                    &mut caller,
                    &BUFF_32,
                    block_hash_offset,
                    block_hash_length,
                    epoch,
                )?;

                let bhh = match block_hash {
                    Value::Sequence(SequenceData::Buffer(BuffData { data })) => {
                        if data.len() != 32 {
                            return Err(RuntimeErrorType::BadBlockHash(data).into());
                        }
                        StacksBlockId::from(data.as_slice())
                    }
                    x => return Err(CheckErrors::TypeValueError(BUFF_32.clone(), x).into()),
                };

                caller
                    .data_mut()
                    .global_context
                    .add_memory(cost_constants::AT_BLOCK_MEMORY)
                    .map_err(Error::from)?;

                caller.data_mut().global_context.begin_read_only();

                let prev_bhh = caller
                    .data_mut()
                    .global_context
                    .database
                    .set_block_hash(bhh, false)?;

                caller.data_mut().push_at_block(prev_bhh);

                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "enter_at_block".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `exit_at_block`, into the Wasm module.
/// This function is called after evaluating the inner expression of an
/// `at-block` expression, resetting the state back to the current block.
fn link_exit_at_block_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "exit_at_block",
            |mut caller: Caller<'_, ClarityWasmContext>| {
                // Pop back to the current block
                let bhh = caller.data_mut().pop_at_block()?;
                caller
                    .data_mut()
                    .global_context
                    .database
                    .set_block_hash(bhh, true)?;

                // Roll back any changes that occurred during the `at-block`
                // expression. This is precautionary, since only read-only
                // operations are allowed during an `at-block` expression.
                caller.data_mut().global_context.roll_back()?;

                caller
                    .data_mut()
                    .global_context
                    .drop_memory(cost_constants::AT_BLOCK_MEMORY)?;

                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "exit_at_block".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `keccak256`, into the Wasm module.
/// This function is called for the Clarity expression, `keccak256`.
fn link_keccak256_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "keccak256",
            |mut caller: Caller<'_, ClarityWasmContext>,
             buffer_offset: i32,
             buffer_length: i32,
             return_offset: i32,
             return_length: i32| {
                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                // Read the bytes from the memory
                let bytes =
                    read_bytes_from_wasm(memory, &mut caller, buffer_offset, buffer_length)?;

                let hash = Keccak256Hash::from_data(&bytes);

                // Write the hash to the return buffer
                memory.write(&mut caller, return_offset as usize, hash.as_bytes())?;

                Ok((return_offset, return_length))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "keccak256".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `sha512`, into the Wasm module.
/// This function is called for the Clarity expression, `sha512`.
fn link_sha512_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "sha512",
            |mut caller: Caller<'_, ClarityWasmContext>,
             buffer_offset: i32,
             buffer_length: i32,
             return_offset: i32,
             return_length: i32| {
                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                // Read the bytes from the memory
                let bytes =
                    read_bytes_from_wasm(memory, &mut caller, buffer_offset, buffer_length)?;

                let hash = Sha512Sum::from_data(&bytes);

                // Write the hash to the return buffer
                memory.write(&mut caller, return_offset as usize, hash.as_bytes())?;

                Ok((return_offset, return_length))
            },
        )
        .map(|_| ())
        .map_err(|e| Error::Wasm(WasmError::UnableToLinkHostFunction("sha512".to_string(), e)))
}

/// Link host interface function, `sha512_256`, into the Wasm module.
/// This function is called for the Clarity expression, `sha512/256`.
fn link_sha512_256_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "sha512_256",
            |mut caller: Caller<'_, ClarityWasmContext>,
             buffer_offset: i32,
             buffer_length: i32,
             return_offset: i32,
             return_length: i32| {
                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                // Read the bytes from the memory
                let bytes =
                    read_bytes_from_wasm(memory, &mut caller, buffer_offset, buffer_length)?;

                let hash = Sha512Trunc256Sum::from_data(&bytes);

                // Write the hash to the return buffer
                memory.write(&mut caller, return_offset as usize, hash.as_bytes())?;

                Ok((return_offset, return_length))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "sha512_256".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `secp256k1_recover`, into the Wasm module.
/// This function is called for the Clarity expression, `secp256k1-recover?`.
fn link_secp256k1_recover_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "secp256k1_recover",
            |mut caller: Caller<'_, ClarityWasmContext>,
             msg_offset: i32,
             msg_length: i32,
             sig_offset: i32,
             sig_length: i32,
             return_offset: i32,
             _return_length: i32| {
                // runtime_cost(ClarityCostFunction::Secp256k1recover, env, 0)?;

                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let ret_ty = TypeSignature::new_response(BUFF_33.clone(), TypeSignature::UIntType)?;
                let repr_size = get_type_size(&ret_ty);

                // Read the message bytes from the memory
                let msg_bytes = read_bytes_from_wasm(memory, &mut caller, msg_offset, msg_length)?;
                // To match the interpreter behavior, if the message is the
                // wrong length, throw a runtime type error.
                if msg_bytes.len() != 32 {
                    return Err(CheckErrors::TypeValueError(
                        BUFF_32.clone(),
                        Value::buff_from(msg_bytes)?,
                    )
                    .into());
                }

                // Read the signature bytes from the memory
                let sig_bytes = read_bytes_from_wasm(memory, &mut caller, sig_offset, sig_length)?;
                // To match the interpreter behavior, if the signature is the
                // wrong length, return a Clarity error.
                if sig_bytes.len() != 65 || sig_bytes[64] > 3 {
                    let result = Value::err_uint(2);
                    write_to_wasm(
                        caller,
                        memory,
                        &ret_ty,
                        return_offset,
                        return_offset + repr_size,
                        &result,
                        true,
                    )?;
                    return Ok(());
                }

                let result = match secp256k1_recover(&msg_bytes, &sig_bytes) {
                    Ok(pubkey) => Value::okay(Value::buff_from(pubkey.to_vec())?)?,
                    _ => Value::err_uint(1),
                };

                // Write the result to the return buffer
                write_to_wasm(
                    caller,
                    memory,
                    &ret_ty,
                    return_offset,
                    return_offset + repr_size,
                    &result,
                    true,
                )?;

                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "secp256k1_recover".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `secp256k1_verify`, into the Wasm module.
/// This function is called for the Clarity expression, `secp256k1-verify`.
fn link_secp256k1_verify_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "secp256k1_verify",
            |mut caller: Caller<'_, ClarityWasmContext>,
             msg_offset: i32,
             msg_length: i32,
             sig_offset: i32,
             sig_length: i32,
             pk_offset: i32,
             pk_length: i32| {
                // runtime_cost(ClarityCostFunction::Secp256k1verify, env, 0)?;

                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                // Read the message bytes from the memory
                let msg_bytes = read_bytes_from_wasm(memory, &mut caller, msg_offset, msg_length)?;
                // To match the interpreter behavior, if the message is the
                // wrong length, throw a runtime type error.
                if msg_bytes.len() != 32 {
                    return Err(CheckErrors::TypeValueError(
                        BUFF_32.clone(),
                        Value::buff_from(msg_bytes)?,
                    )
                    .into());
                }

                // Read the signature bytes from the memory
                let sig_bytes = read_bytes_from_wasm(memory, &mut caller, sig_offset, sig_length)?;
                // To match the interpreter behavior, if the signature is the
                // wrong length, return a Clarity error.
                if sig_bytes.len() < 64
                    || sig_bytes.len() > 65
                    || sig_bytes.len() == 65 && sig_bytes[64] > 3
                {
                    return Ok(0i32);
                }

                // Read the public-key bytes from the memory
                let pk_bytes = read_bytes_from_wasm(memory, &mut caller, pk_offset, pk_length)?;
                // To match the interpreter behavior, if the public key is the
                // wrong length, throw a runtime type error.
                if pk_bytes.len() != 33 {
                    return Err(CheckErrors::TypeValueError(
                        BUFF_33.clone(),
                        Value::buff_from(pk_bytes)?,
                    )
                    .into());
                }

                Ok(secp256k1_verify(&msg_bytes, &sig_bytes, &pk_bytes).map_or(0i32, |_| 1i32))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "secp256k1_verify".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `principal_of`, into the Wasm module.
/// This function is called for the Clarity expression, `principal-of?`.
fn link_principal_of_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "principal_of",
            |mut caller: Caller<'_, ClarityWasmContext>,
             key_offset: i32,
             key_length: i32,
             principal_offset: i32| {
                // runtime_cost(ClarityCostFunction::PrincipalOf, env, 0)?;

                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let epoch = caller.data_mut().global_context.epoch_id;

                // Read the public key from the memory
                let key_val = read_from_wasm(
                    memory,
                    &mut caller,
                    &BUFF_33.clone(),
                    key_offset,
                    key_length,
                    epoch,
                )?;

                let pub_key = match key_val {
                    Value::Sequence(SequenceData::Buffer(BuffData { ref data })) => {
                        if data.len() != 33 {
                            return Err(
                                CheckErrors::TypeValueError(BUFF_33.clone(), key_val).into()
                            );
                        }
                        data
                    }
                    _ => return Err(CheckErrors::TypeValueError(BUFF_33.clone(), key_val).into()),
                };

                if let Ok(pub_key) = Secp256k1PublicKey::from_slice(pub_key) {
                    // Note: Clarity1 had a bug in how the address is computed (issues/2619).
                    // We want to preserve the old behavior unless the version is greater.
                    let addr = if *caller.data().contract_context().get_clarity_version()
                        > ClarityVersion::Clarity1
                    {
                        pubkey_to_address_v2(pub_key, caller.data().global_context.mainnet)?
                    } else {
                        pubkey_to_address_v1(pub_key)?
                    };
                    let principal = addr.to_account_principal();

                    // Write the principal to the return buffer
                    write_to_wasm(
                        &mut caller,
                        memory,
                        &TypeSignature::PrincipalType,
                        principal_offset,
                        principal_offset,
                        &Value::Principal(principal),
                        false,
                    )?;

                    // (ok principal)
                    Ok((
                        1i32,
                        principal_offset,
                        STANDARD_PRINCIPAL_BYTES as i32,
                        0i64,
                        0i64,
                    ))
                } else {
                    // (err u1)
                    Ok((0i32, 0i32, 0i32, 1i64, 0i64))
                }
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "secp256k1_verify".to_string(),
                e,
            ))
        })
}

fn link_save_constant_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "save_constant",
            |mut caller: Caller<'_, ClarityWasmContext>,
             name_offset: i32,
             name_length: i32,
             value_offset: i32,
             _value_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let epoch = caller.data_mut().global_context.epoch_id;

                // Get constant name from the memory.
                let const_name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;
                let cname = ClarityName::from(const_name.as_str());

                // Get constant value type.
                let value_ty = caller
                    .data()
                    .contract_analysis
                    .ok_or(Error::Wasm(WasmError::DefinesNotFound))?
                    .get_variable_type(const_name.as_str())
                    .ok_or(Error::Wasm(WasmError::DefinesNotFound))?;

                let value =
                    read_from_wasm_indirect(memory, &mut caller, value_ty, value_offset, epoch)?;

                // Insert constant name and expression value into a persistent data structure.
                caller
                    .data_mut()
                    .contract_context_mut()?
                    .variables
                    .insert(cname, value);

                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "save_constant".to_string(),
                e,
            ))
        })
}

fn link_load_constant_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "load_constant",
            |mut caller: Caller<'_, ClarityWasmContext>,
             name_offset: i32,
             name_length: i32,
             value_offset: i32,
             _value_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                // Read constant name from the memory.
                let const_name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;

                // Constant value
                let value = caller
                    .data()
                    .contract_context()
                    .variables
                    .get(&ClarityName::from(const_name.as_str()))
                    .ok_or(CheckErrors::UndefinedVariable(const_name.to_string()))?
                    .clone();

                // Constant value type
                let ty = TypeSignature::type_of(&value)?;

                write_to_wasm(
                    &mut caller,
                    memory,
                    &ty,
                    value_offset,
                    value_offset + get_type_size(&ty),
                    &value,
                    true,
                )?;

                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "load_constant".to_string(),
                e,
            ))
        })
}

fn link_skip_list<T>(linker: &mut Linker<T>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "skip_list",
            |mut caller: Caller<'_, T>, offset_beg: i32, offset_end: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                // we will read the remaining serialized buffer here, and start it with the list type prefix
                let mut serialized_buffer = vec![0u8; (offset_end - offset_beg) as usize + 1];
                serialized_buffer[0] = clarity::vm::types::serialization::TypePrefix::List as u8;
                memory
                    .read(
                        &mut caller,
                        offset_beg as usize,
                        &mut serialized_buffer[1..],
                    )
                    .map_err(|e| Error::Wasm(WasmError::Runtime(e.into())))?;

                match Value::deserialize_read_count(&mut serialized_buffer.as_slice(), None, false)
                {
                    Ok((_, bytes_read)) => Ok(offset_beg + bytes_read as i32 - 1),
                    Err(_) => Ok(0),
                }
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "skip_list".to_string(),
                e,
            ))
        })
}

/// Link host-interface function, `log`, into the Wasm module.
/// This function is used for debugging the Wasm, and should not be called in
/// production.
fn link_log<T>(linker: &mut Linker<T>) -> Result<(), Error> {
    linker
        .func_wrap("", "log", |_: Caller<'_, T>, param: i64| {
            println!("log: {param}");
        })
        .map(|_| ())
        .map_err(|e| Error::Wasm(WasmError::UnableToLinkHostFunction("log".to_string(), e)))
}

/// Link host-interface function, `debug_msg`, into the Wasm module.
/// This function is used for debugging the Wasm, and should not be called in
/// production.
fn link_debug_msg<T>(linker: &mut Linker<T>) -> Result<(), Error> {
    linker
        .func_wrap("", "debug_msg", |_caller: Caller<'_, T>, param: i32| {
            crate::debug_msg::recall(param, |s| println!("DEBUG: {s}"))
        })
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "debug_msg".to_string(),
                e,
            ))
        })
}

pub fn dummy_linker(engine: &Engine) -> Result<Linker<()>, wasmtime::Error> {
    let mut linker = Linker::new(engine);

    link_skip_list(&mut linker)?;

    // Link in the host interface functions.
    linker.func_wrap(
        "clarity",
        "define_function",
        |_kind: i32, _name_offset: i32, _name_length: i32| {
            println!("define-function");
        },
    )?;

    linker.func_wrap(
        "clarity",
        "define_variable",
        |_name_offset: i32, _name_length: i32, _value_offset: i32, _value_length: i32| {
            println!("define-data-var");
        },
    )?;

    linker.func_wrap(
        "clarity",
        "define_ft",
        |_name_offset: i32,
         _name_length: i32,
         _supply_indicator: i32,
         _supply_lo: i64,
         _supply_hi: i64| {
            println!("define-ft");
        },
    )?;

    linker.func_wrap(
        "clarity",
        "define_nft",
        |_name_offset: i32, _name_length: i32| {
            println!("define-ft");
        },
    )?;

    linker.func_wrap(
        "clarity",
        "define_map",
        |_name_offset: i32, _name_length: i32| {
            println!("define-map");
        },
    )?;

    linker.func_wrap(
        "clarity",
        "define_trait",
        |_name_offset: i32, _name_length: i32| {
            println!("define-trait");
        },
    )?;

    linker.func_wrap(
        "clarity",
        "impl_trait",
        |_name_offset: i32, _name_length: i32| {
            println!("impl-trait");
        },
    )?;

    linker.func_wrap(
        "clarity",
        "get_variable",
        |_name_offset: i32, _name_length: i32, _return_offset: i32, _return_length: i32| {
            println!("var-get");
        },
    )?;

    linker.func_wrap(
        "clarity",
        "set_variable",
        |_name_offset: i32, _name_length: i32, _value_offset: i32, _value_length: i32| {
            println!("var-set");
        },
    )?;

    linker.func_wrap(
        "clarity",
        "print",
        |_value_offset: i32,
         _value_length: i32,
         _serialized_ty_offset: i32,
         _serialized_ty_length: i32| {
            println!("print");
        },
    )?;

    linker.func_wrap(
        "clarity",
        "tx_sender",
        |_return_offset: i32, _return_length: i32| {
            println!("tx-sender");
            Ok((0i32, 0i32))
        },
    )?;

    linker.func_wrap(
        "clarity",
        "contract_caller",
        |_return_offset: i32, _return_length: i32| {
            println!("tx-sender");
            Ok((0i32, 0i32))
        },
    )?;

    linker.func_wrap(
        "clarity",
        "tx_sponsor",
        |_return_offset: i32, _return_length: i32| {
            println!("tx-sponsor");
            Ok((0i32, 0i32, 0i32))
        },
    )?;

    linker.func_wrap("clarity", "block_height", |_: Caller<'_, ()>| {
        println!("block-height");
        Ok((0i64, 0i64))
    })?;

    linker.func_wrap("clarity", "stacks_block_height", |_: Caller<'_, ()>| {
        println!("stacks-block-height");
        Ok((0i64, 0i64))
    })?;

    linker.func_wrap("clarity", "tenure_height", |_: Caller<'_, ()>| {
        println!("tenure-height");
        Ok((0i64, 0i64))
    })?;

    linker.func_wrap("clarity", "burn_block_height", |_: Caller<'_, ()>| {
        println!("burn-block-height");
        Ok((0i64, 0i64))
    })?;

    linker.func_wrap("clarity", "stx_liquid_supply", |_: Caller<'_, ()>| {
        println!("stx-liquid-supply");
        Ok((0i64, 0i64))
    })?;

    linker.func_wrap("clarity", "is_in_regtest", |_: Caller<'_, ()>| {
        println!("is-in-regtest");
        Ok(0i32)
    })?;

    linker.func_wrap("clarity", "is_in_mainnet", |_: Caller<'_, ()>| {
        println!("is-in-mainnet");
        Ok(0i32)
    })?;

    linker.func_wrap("clarity", "chain_id", |_: Caller<'_, ()>| {
        println!("chain-id");
        Ok((0i64, 0i64))
    })?;

    linker.func_wrap("clarity", "enter_as_contract", |_: Caller<'_, ()>| {
        println!("as-contract: enter");
        Ok(())
    })?;

    linker.func_wrap("clarity", "exit_as_contract", |_: Caller<'_, ()>| {
        println!("as-contract: exit");
        Ok(())
    })?;

    linker.func_wrap(
        "clarity",
        "enter_at_block",
        |_block_hash_offset: i32, _block_hash_length: i32| {
            println!("at-block: enter");
            Ok(())
        },
    )?;

    linker.func_wrap("clarity", "exit_at_block", |_: Caller<'_, ()>| {
        println!("at-block: exit");
        Ok(())
    })?;

    linker.func_wrap(
        "clarity",
        "stx_get_balance",
        |_principal_offset: i32, _principal_length: i32| Ok((0i64, 0i64)),
    )?;

    linker.func_wrap(
        "clarity",
        "stx_account",
        |_principal_offset: i32, _principal_length: i32| Ok((0i64, 0i64, 0i64, 0i64, 0i64, 0i64)),
    )?;

    linker.func_wrap(
        "clarity",
        "stx_burn",
        |_amount_lo: i64, _amount_hi: i64, _principal_offset: i32, _principal_length: i32| {
            Ok((0i32, 0i32, 0i64, 0i64))
        },
    )?;

    linker.func_wrap(
        "clarity",
        "stx_transfer",
        |_amount_lo: i64,
         _amount_hi: i64,
         _from_offset: i32,
         _from_length: i32,
         _to_offset: i32,
         _to_length: i32,
         _memo_offset: i32,
         _memo_length: i32| { Ok((0i32, 0i32, 0i64, 0i64)) },
    )?;

    linker.func_wrap(
        "clarity",
        "ft_get_supply",
        |_name_offset: i32, _name_length: i32| Ok((0i64, 0i64)),
    )?;

    linker.func_wrap(
        "clarity",
        "ft_get_balance",
        |_name_offset: i32, _name_length: i32, _owner_offset: i32, _owner_length: i32| {
            Ok((0i64, 0i64))
        },
    )?;

    linker.func_wrap(
        "clarity",
        "ft_burn",
        |_name_offset: i32,
         _name_length: i32,
         _amount_lo: i64,
         _amount_hi: i64,
         _sender_offset: i32,
         _sender_length: i32| { Ok((0i32, 0i32, 0i64, 0i64)) },
    )?;

    linker.func_wrap(
        "clarity",
        "ft_mint",
        |_name_offset: i32,
         _name_length: i32,
         _amount_lo: i64,
         _amount_hi: i64,
         _sender_offset: i32,
         _sender_length: i32| { Ok((0i32, 0i32, 0i64, 0i64)) },
    )?;

    linker.func_wrap(
        "clarity",
        "ft_transfer",
        |_name_offset: i32,
         _name_length: i32,
         _amount_lo: i64,
         _amount_hi: i64,
         _sender_offset: i32,
         _sender_length: i32,
         _recipient_offset: i32,
         _recipient_length: i32| { Ok((0i32, 0i32, 0i64, 0i64)) },
    )?;

    linker.func_wrap(
        "clarity",
        "nft_get_owner",
        |_name_offset: i32,
         _name_length: i32,
         _asset_offset: i32,
         _asset_length: i32,
         _return_offset: i32,
         _return_length: i32| { Ok((0i32, 0i32, 0i32)) },
    )?;

    linker.func_wrap(
        "clarity",
        "nft_burn",
        |_name_offset: i32,
         _name_length: i32,
         _asset_offset: i32,
         _asset_length: i32,
         _sender_offset: i32,
         _sender_length: i32| { Ok((0i32, 0i32, 0i64, 0i64)) },
    )?;

    linker.func_wrap(
        "clarity",
        "nft_mint",
        |_name_offset: i32,
         _name_length: i32,
         _asset_offset: i32,
         _asset_length: i32,
         _recipient_offset: i32,
         _recipient_length: i32| { Ok((0i32, 0i32, 0i64, 0i64)) },
    )?;

    linker.func_wrap(
        "clarity",
        "nft_transfer",
        |_name_offset: i32,
         _name_length: i32,
         _asset_offset: i32,
         _asset_length: i32,
         _sender_offset: i32,
         _sender_length: i32,
         _recipient_offset: i32,
         _recipient_length: i32| { Ok((0i32, 0i32, 0i64, 0i64)) },
    )?;

    linker.func_wrap(
        "clarity",
        "map_get",
        |_name_offset: i32,
         _name_length: i32,
         _key_offset: i32,
         _key_length: i32,
         _return_offset: i32,
         _return_length: i32| { Ok(()) },
    )?;

    linker.func_wrap(
        "clarity",
        "map_set",
        |_name_offset: i32,
         _name_length: i32,
         _key_offset: i32,
         _key_length: i32,
         _value_offset: i32,
         _value_length: i32| { Ok(0i32) },
    )?;

    linker.func_wrap(
        "clarity",
        "map_insert",
        |_name_offset: i32,
         _name_length: i32,
         _key_offset: i32,
         _key_length: i32,
         _value_offset: i32,
         _value_length: i32| { Ok(0i32) },
    )?;

    linker.func_wrap(
        "clarity",
        "map_delete",
        |_name_offset: i32, _name_length: i32, _key_offset: i32, _key_length: i32| Ok(0i32),
    )?;

    linker.func_wrap(
        "clarity",
        "get_block_info_time_property",
        |_height_lo: i64, _height_hi: i64, _return_offset: i32, _return_length: i32| {
            println!("get_block_info_time_property");
            Ok(())
        },
    )?;

    linker.func_wrap(
        "clarity",
        "get_block_info_vrf_seed_property",
        |_height_lo: i64, _height_hi: i64, _return_offset: i32, _return_length: i32| {
            println!("get_block_info_vrf_seed_property");
            Ok(())
        },
    )?;

    linker.func_wrap(
        "clarity",
        "get_block_info_header_hash_property",
        |_height_lo: i64, _height_hi: i64, _return_offset: i32, _return_length: i32| {
            println!("get_block_info_header_hash_property");
            Ok(())
        },
    )?;

    linker.func_wrap(
        "clarity",
        "get_block_info_burnchain_header_hash_property",
        |_height_lo: i64, _height_hi: i64, _return_offset: i32, _return_length: i32| {
            println!("get_block_info_burnchain_header_hash_property");
            Ok(())
        },
    )?;

    linker.func_wrap(
        "clarity",
        "get_block_info_identity_header_hash_property",
        |_height_lo: i64, _height_hi: i64, _return_offset: i32, _return_length: i32| {
            println!("get_block_info_identity_header_hash_property");
            Ok(())
        },
    )?;

    linker.func_wrap(
        "clarity",
        "get_block_info_miner_address_property",
        |_height_lo: i64, _height_hi: i64, _return_offset: i32, _return_length: i32| {
            println!("get_block_info_miner_address_property");
            Ok(())
        },
    )?;

    linker.func_wrap(
        "clarity",
        "get_block_info_miner_spend_winner_property",
        |_height_lo: i64, _height_hi: i64, _return_offset: i32, _return_length: i32| {
            println!("get_block_info_miner_spend_winner_property");
            Ok(())
        },
    )?;

    linker.func_wrap(
        "clarity",
        "get_block_info_miner_spend_total_property",
        |_height_lo: i64, _height_hi: i64, _return_offset: i32, _return_length: i32| {
            println!("get_block_info_miner_spend_total_property");
            Ok(())
        },
    )?;

    linker.func_wrap(
        "clarity",
        "get_block_info_block_reward_property",
        |_height_lo: i64, _height_hi: i64, _return_offset: i32, _return_length: i32| {
            println!("get_block_info_block_reward_property");
            Ok(())
        },
    )?;

    linker.func_wrap(
        "clarity",
        "get_burn_block_info_header_hash_property",
        |_height_lo: i64, _height_hi: i64, _return_offset: i32, _return_length: i32| {
            println!("get_burn_block_info_header_hash_property");
            Ok(())
        },
    )?;

    linker.func_wrap(
        "clarity",
        "get_burn_block_info_pox_addrs_property",
        |_height_lo: i64, _height_hi: i64, _return_offset: i32, _return_length: i32| {
            println!("get_burn_block_info_pox_addrs_property");
            Ok(())
        },
    )?;

    linker.func_wrap(
        "clarity",
        "get_stacks_block_info_time_property",
        |_height_lo: i64, _height_hi: i64, _return_offset: i32, _return_length: i32| {
            println!("get_stacks_block_info_time_property");
            Ok(())
        },
    )?;

    linker.func_wrap(
        "clarity",
        "get_stacks_block_info_header_hash_property",
        |_height_lo: i64, _height_hi: i64, _return_offset: i32, _return_length: i32| {
            println!("get_stacks_block_info_header_hash_property");
            Ok(())
        },
    )?;

    linker.func_wrap(
        "clarity",
        "get_stacks_block_info_identity_header_hash_property",
        |_height_lo: i64, _height_hi: i64, _return_offset: i32, _return_length: i32| {
            println!("get_stacks_block_info_identity_header_hash_property");
            Ok(())
        },
    )?;

    linker.func_wrap(
        "clarity",
        "get_tenure_info_burnchain_header_hash_property",
        |_height_lo: i64, _height_hi: i64, _return_offset: i32, _return_length: i32| {
            println!("get_tenure_info_burnchain_header_hash_property");
            Ok(())
        },
    )?;

    linker.func_wrap(
        "clarity",
        "get_tenure_info_miner_address_property",
        |_height_lo: i64, _height_hi: i64, _return_offset: i32, _return_length: i32| {
            println!("get_tenure_info_miner_address_property");
            Ok(())
        },
    )?;

    linker.func_wrap(
        "clarity",
        "get_tenure_info_time_property",
        |_height_lo: i64, _height_hi: i64, _return_offset: i32, _return_length: i32| {
            println!("get_tenure_info_time_property");
            Ok(())
        },
    )?;

    linker.func_wrap(
        "clarity",
        "get_tenure_info_vrf_seed_property",
        |_height_lo: i64, _height_hi: i64, _return_offset: i32, _return_length: i32| {
            println!("get_tenure_info_vrf_seed_property");
            Ok(())
        },
    )?;

    linker.func_wrap(
        "clarity",
        "get_tenure_info_block_reward_property",
        |_height_lo: i64, _height_hi: i64, _return_offset: i32, _return_length: i32| {
            println!("get_tenure_info_block_reward_property");
            Ok(())
        },
    )?;

    linker.func_wrap(
        "clarity",
        "get_tenure_info_miner_spend_total_property",
        |_height_lo: i64, _height_hi: i64, _return_offset: i32, _return_length: i32| {
            println!("get_tenure_info_miner_spend_total_property");
            Ok(())
        },
    )?;

    linker.func_wrap(
        "clarity",
        "get_tenure_info_miner_spend_winner_property",
        |_height_lo: i64, _height_hi: i64, _return_offset: i32, _return_length: i32| {
            println!("get_tenure_info_miner_spend_winner_property");
            Ok(())
        },
    )?;

    linker.func_wrap(
        "clarity",
        "contract_call",
        |_contract_trait_offset: i32,
         _contract_trait_length: i32,
         _contract_offset: i32,
         _contract_length: i32,
         _function_offset: i32,
         _function_length: i32,
         _args_offset: i32,
         _args_length: i32,
         _return_offset: i32,
         _return_length: i32| {
            println!("contract_call");
            Ok(())
        },
    )?;

    linker.func_wrap("clarity", "begin_public_call", || {
        println!("begin_public_call");
        Ok(())
    })?;

    linker.func_wrap("clarity", "begin_read_only_call", || {
        println!("begin_read_only_call");
        Ok(())
    })?;

    linker.func_wrap("clarity", "commit_call", || {
        println!("commit_call");
        Ok(())
    })?;

    linker.func_wrap("clarity", "roll_back_call", || {
        println!("roll_back_call");
        Ok(())
    })?;

    linker.func_wrap(
        "clarity",
        "keccak256",
        |_buffer_offset: i32, _buffer_length: i32, _return_offset: i32, _return_length: i32| {
            println!("keccak256");
            Ok((_return_offset, _return_length))
        },
    )?;

    linker.func_wrap(
        "clarity",
        "sha512",
        |_buffer_offset: i32, _buffer_length: i32, _return_offset: i32, _return_length: i32| {
            println!("sha512");
            Ok((_return_offset, _return_length))
        },
    )?;

    linker.func_wrap(
        "clarity",
        "sha512_256",
        |_buffer_offset: i32, _buffer_length: i32, _return_offset: i32, _return_length: i32| {
            println!("sha512_256");
            Ok((_return_offset, _return_length))
        },
    )?;

    linker.func_wrap(
        "clarity",
        "secp256k1_recover",
        |_msg_offset: i32,
         _msg_length: i32,
         _sig_offset: i32,
         _sig_length: i32,
         _return_offset: i32,
         _return_length: i32| {
            println!("secp256k1_recover");
            Ok(())
        },
    )?;

    linker.func_wrap(
        "clarity",
        "secp256k1_verify",
        |_msg_offset: i32,
         _msg_length: i32,
         _sig_offset: i32,
         _sig_length: i32,
         _pk_offset: i32,
         _pk_length: i32| {
            println!("secp256k1_verify");
            Ok(0i32)
        },
    )?;

    linker.func_wrap(
        "clarity",
        "principal_of",
        |_key_offset: i32, _key_length: i32, _principal_offset: i32| {
            println!("secp256k1_verify");
            Ok((0i32, 0i32, 0i32, 0i64, 0i64))
        },
    )?;

    // Create a log function for debugging.
    linker.func_wrap("", "log", |param: i64| {
        println!("log: {param}");
    })?;

    // Create another log function for debugging.
    linker.func_wrap("", "debug_msg", |param: i32| {
        println!("log: {param}");
    })?;

    linker.func_wrap(
        "clarity",
        "save_constant",
        |_name_offset: i32, _name_length: i32, _value_offset: i32, _value_length: i32| {
            println!("save constant");
        },
    )?;

    linker.func_wrap(
        "clarity",
        "load_constant",
        |_name_offset: i32, _name_length: i32, _value_offset: i32, _value_length: i32| {
            println!("load constant");
        },
    )?;

    Ok(linker)
}

/// the standard.wat file and link in all of the host interface functions.
pub fn load_stdlib() -> Result<(Instance, Store<()>), wasmtime::Error> {
    let standard_lib = include_str!("standard/standard.wat");
    let engine = Engine::default();
    let mut store = Store::new(&engine, ());

    let mut linker = dummy_linker(&engine)?;
    linker.define_cost_globals(&mut store)?;

    let module = Module::new(&engine, standard_lib)?;
    let instance = linker.instantiate(&mut store, &module)?;
    Ok((instance, store))
}
