use clarity::vm::analysis::ContractAnalysis;
use clarity::vm::contexts::GlobalContext;
use clarity::vm::errors::{RuntimeError, VmExecutionError, WasmError};
use clarity::vm::events::*;
use clarity::vm::types::{AssetIdentifier, BuffData, PrincipalData, QualifiedContractIdentifier};
use clarity::vm::{CallStack, ContractContext, Value};
use stacks_common::types::chainstate::StacksBlockId;
use wasmtime::{Linker, Module, Store};

#[derive(Debug, Clone)]
pub enum AssetContext {
    AllAssetsUnsafe,
    Ft {
        contract: QualifiedContractIdentifier,
        token: String,
        allowed_amount: u128,
    },
    Nft {
        asset_identifier: AssetIdentifier,
        allowed_identifiers: Vec<clarity_types::Value>,
    },
    Stacking {
        allowed_amount: u128,
    },
    Stx {
        allowed_amount: u128,
    },
}

use crate::cost::{CostLinker, CostMeter};
use crate::linker::link_host_functions;
use crate::wasm_utils::*;
use crate::{error_mapping, AccessCostMeter};

// The context used when making calls into the Wasm module.
pub struct ClarityWasmContext<'a, 'b> {
    pub global_context: &'a mut GlobalContext<'b>,
    contract_context: Option<&'a ContractContext>,
    contract_context_mut: Option<&'a mut ContractContext>,
    pub call_stack: &'a mut CallStack,
    pub sender: Option<PrincipalData>,
    pub caller: Option<PrincipalData>,
    pub sponsor: Option<PrincipalData>,
    // Stack of senders, used for `as-contract` expressions.
    sender_stack: Vec<PrincipalData>,
    /// Stack of callers, used for `contract-call?` and `as-contract` expressions.
    caller_stack: Vec<PrincipalData>,
    /// Stack of block hashes, used for `at-block` expressions.
    bhh_stack: Vec<StacksBlockId>,
    /// Stack of asset contexts, used for `with-*` expressions.
    pub asset_context_stack: Vec<Vec<AssetContext>>,

    /// Contract analysis data, used for typing information, and only available
    /// when initializing a contract. Should always be `Some` when initializing
    /// a contract, and `None` otherwise.
    pub contract_analysis: Option<&'a ContractAnalysis>,
}

impl<'a, 'b> ClarityWasmContext<'a, 'b> {
    pub fn new_init(
        global_context: &'a mut GlobalContext<'b>,
        contract_context: &'a mut ContractContext,
        call_stack: &'a mut CallStack,
        sender: Option<PrincipalData>,
        caller: Option<PrincipalData>,
        sponsor: Option<PrincipalData>,
        contract_analysis: Option<&'a ContractAnalysis>,
    ) -> Self {
        ClarityWasmContext {
            global_context,
            contract_context: None,
            contract_context_mut: Some(contract_context),
            call_stack,
            sender,
            caller,
            sponsor,
            sender_stack: vec![],
            caller_stack: vec![],
            bhh_stack: vec![],
            asset_context_stack: vec![],
            contract_analysis,
        }
    }

    pub fn new_run(
        global_context: &'a mut GlobalContext<'b>,
        contract_context: &'a ContractContext,
        call_stack: &'a mut CallStack,
        sender: Option<PrincipalData>,
        caller: Option<PrincipalData>,
        sponsor: Option<PrincipalData>,
        contract_analysis: Option<&'a ContractAnalysis>,
    ) -> Self {
        ClarityWasmContext {
            global_context,
            contract_context: Some(contract_context),
            contract_context_mut: None,
            call_stack,
            sender,
            caller,
            sponsor,
            sender_stack: vec![],
            caller_stack: vec![],
            bhh_stack: vec![],
            asset_context_stack: vec![],
            contract_analysis,
        }
    }

    pub fn push_sender(&mut self, sender: PrincipalData) {
        if let Some(current) = self.sender.take() {
            self.sender_stack.push(current);
        }
        self.sender = Some(sender);
    }

    pub fn pop_sender(&mut self) -> Result<PrincipalData, VmExecutionError> {
        self.sender
            .take()
            .ok_or(RuntimeError::NoSenderInContext.into())
            .inspect(|_| {
                self.sender = self.sender_stack.pop();
            })
    }

    pub fn push_caller(&mut self, caller: PrincipalData) {
        if let Some(current) = self.caller.take() {
            self.caller_stack.push(current);
        }
        self.caller = Some(caller);
    }

    pub fn pop_caller(&mut self) -> Result<PrincipalData, VmExecutionError> {
        self.caller
            .take()
            .ok_or(RuntimeError::NoCallerInContext.into())
            .inspect(|_| {
                self.caller = self.caller_stack.pop();
            })
    }

    pub fn push_at_block(&mut self, bhh: StacksBlockId) {
        self.bhh_stack.push(bhh);
    }

    pub fn pop_at_block(&mut self) -> Result<StacksBlockId, VmExecutionError> {
        self.bhh_stack
            .pop()
            .ok_or(VmExecutionError::Wasm(WasmError::WasmGeneratorError(
                "Could not pop at_block".to_string(),
            )))
    }

    pub fn push_as_contract(&mut self) {
        self.asset_context_stack.push(Vec::new());
    }

    pub fn pop_as_contract(&mut self) {
        self.asset_context_stack.pop();
    }

    pub fn push_asset_context_unsafe(&mut self) {
        self.asset_context_stack
            .last()
            .unwrap()
            .to_owned()
            .push(AssetContext::AllAssetsUnsafe);
    }

    pub fn push_asset_context_ft(
        &mut self,
        contract: QualifiedContractIdentifier,
        token: String,
        allowed_amount: u128,
    ) {
        self.asset_context_stack
            .last()
            .unwrap()
            .to_owned()
            .push(AssetContext::Ft {
                contract,
                token,
                allowed_amount,
            });
    }

    pub fn push_asset_context_nft(
        &mut self,
        asset_identifier: AssetIdentifier,
        allowed_identifiers: Vec<clarity_types::Value>,
    ) {
        self.asset_context_stack
            .last()
            .unwrap()
            .to_owned()
            .push(AssetContext::Nft {
                asset_identifier,
                allowed_identifiers,
            });
    }

    pub fn push_asset_context_stacking(&mut self, allowed_amount: u128) {
        self.asset_context_stack
            .last()
            .unwrap()
            .to_owned()
            .push(AssetContext::Stacking { allowed_amount });
    }

    pub fn push_asset_context_stx(&mut self, allowed_amount: u128) {
        self.asset_context_stack
            .last()
            .unwrap()
            .to_owned()
            .push(AssetContext::Stx { allowed_amount });
    }

    /// Check if a transfer would exceed the allowance.
    /// Returns true if the transfer would exceed the allowance (should return err uindex).
    /// Returns false if the transfer is allowed.
    pub fn check_ft_allowance(
        &mut self,
        contract_id: &QualifiedContractIdentifier,
        token_name: String,
        amount: u128,
    ) -> Result<(bool, usize), VmExecutionError> {
        for contract_asset_contexts in self.asset_context_stack.iter() {
            for (index, context) in contract_asset_contexts.iter().enumerate() {
                if let AssetContext::Ft {
                    allowed_amount,
                    contract: allowed_contract,
                    token: allowed_token,
                } = context
                {
                    let matches_asset = *allowed_token == "*" || *allowed_token == token_name;

                    if matches_asset
                        && *allowed_contract == *contract_id
                        && amount > *allowed_amount
                    {
                        return Ok((true, index));
                    }
                }
            }
        }
        Ok((false, 0))
    }

    /// Check if an NFT transfer would exceed the allowance.
    /// Returns true if the transfer would exceed the allowance (should return err uindex).
    /// Returns false if the transfer is allowed, and updates the used count.
    pub fn check_nft_allowance(
        &mut self,
        asset_identifier: &AssetIdentifier,
        identifier_value: &clarity_types::Value,
    ) -> Result<(bool, usize), VmExecutionError> {
        for contract_asset_contexts in self.asset_context_stack.iter() {
            for (index, context) in contract_asset_contexts.iter().enumerate() {
                if let AssetContext::Nft {
                    asset_identifier: allowed_asset,
                    allowed_identifiers,
                } = context
                {
                    let matches_asset = allowed_asset.asset_name.as_str() == "*"
                        || allowed_asset.asset_name == asset_identifier.asset_name;

                    if matches_asset
                        && asset_identifier.contract_identifier == allowed_asset.contract_identifier
                        && !allowed_identifiers.iter().any(|id| id == identifier_value)
                    {
                        return Ok((true, index));
                    }
                }
            }
        }
        Ok((false, 0))
    }

    /// Check if an STX transfer would exceed the allowance.
    // Return true to indicate allowance exceeded (err index).
    /// Returns false if the transfer is allowed.
    pub fn check_stx_allowance(&mut self, amount: u128) -> Result<(bool, usize), VmExecutionError> {
        for contract_asset_contexts in self.asset_context_stack.iter() {
            for (index, context) in contract_asset_contexts.iter().enumerate() {
                if let AssetContext::Stx { allowed_amount } = context {
                    if amount > *allowed_amount {
                        return Ok((true, index));
                    }
                }
            }
        }
        Ok((false, 0))
    }

    /// Return an immutable reference to the contract_context
    pub fn contract_context(&self) -> &ContractContext {
        if let Some(contract_context) = &self.contract_context {
            contract_context
        } else if let Some(contract_context) = &self.contract_context_mut {
            contract_context
        } else {
            unreachable!("contract_context and contract_context_mut are both None")
        }
    }

    /// Return a mutable reference to the contract_context if we are currently
    /// initializing a contract, else, return an error.
    pub fn contract_context_mut(&mut self) -> Result<&mut ContractContext, VmExecutionError> {
        match &mut self.contract_context_mut {
            Some(contract_context) => Ok(contract_context),
            None => Err(VmExecutionError::Wasm(
                WasmError::DefineFunctionCalledInRunMode,
            )),
        }
    }

    pub fn push_to_event_batch(&mut self, event: StacksTransactionEvent) {
        if let Some(batch) = self.global_context.event_batches.last_mut() {
            batch.0.events.push(event);
        }
    }

    pub fn construct_print_transaction_event(
        contract_id: &QualifiedContractIdentifier,
        value: &Value,
    ) -> StacksTransactionEvent {
        let print_event = SmartContractEventData {
            key: (contract_id.clone(), "print".to_string()),
            value: value.clone(),
        };

        StacksTransactionEvent::SmartContractEvent(print_event)
    }

    pub fn register_print_event(&mut self, value: Value) -> Result<(), VmExecutionError> {
        let event = Self::construct_print_transaction_event(
            &self.contract_context().contract_identifier,
            &value,
        );

        self.push_to_event_batch(event);
        Ok(())
    }

    pub fn register_stx_transfer_event(
        &mut self,
        sender: PrincipalData,
        recipient: PrincipalData,
        amount: u128,
        memo: BuffData,
    ) -> Result<(), VmExecutionError> {
        let event_data = STXTransferEventData {
            sender,
            recipient,
            amount,
            memo,
        };
        let event = StacksTransactionEvent::STXEvent(STXEventType::STXTransferEvent(event_data));

        self.push_to_event_batch(event);
        Ok(())
    }

    pub fn register_stx_burn_event(
        &mut self,
        sender: PrincipalData,
        amount: u128,
    ) -> Result<(), VmExecutionError> {
        let event_data = STXBurnEventData { sender, amount };
        let event = StacksTransactionEvent::STXEvent(STXEventType::STXBurnEvent(event_data));

        self.push_to_event_batch(event);
        Ok(())
    }

    pub fn register_nft_transfer_event(
        &mut self,
        sender: PrincipalData,
        recipient: PrincipalData,
        value: Value,
        asset_identifier: AssetIdentifier,
    ) -> Result<(), VmExecutionError> {
        let event_data = NFTTransferEventData {
            sender,
            recipient,
            asset_identifier,
            value,
        };
        let event = StacksTransactionEvent::NFTEvent(NFTEventType::NFTTransferEvent(event_data));

        self.push_to_event_batch(event);
        Ok(())
    }

    pub fn register_nft_mint_event(
        &mut self,
        recipient: PrincipalData,
        value: Value,
        asset_identifier: AssetIdentifier,
    ) -> Result<(), VmExecutionError> {
        let event_data = NFTMintEventData {
            recipient,
            asset_identifier,
            value,
        };
        let event = StacksTransactionEvent::NFTEvent(NFTEventType::NFTMintEvent(event_data));

        self.push_to_event_batch(event);
        Ok(())
    }

    pub fn register_nft_burn_event(
        &mut self,
        sender: PrincipalData,
        value: Value,
        asset_identifier: AssetIdentifier,
    ) -> Result<(), VmExecutionError> {
        let event_data = NFTBurnEventData {
            sender,
            asset_identifier,
            value,
        };
        let event = StacksTransactionEvent::NFTEvent(NFTEventType::NFTBurnEvent(event_data));

        self.push_to_event_batch(event);
        Ok(())
    }

    pub fn register_ft_transfer_event(
        &mut self,
        sender: PrincipalData,
        recipient: PrincipalData,
        amount: u128,
        asset_identifier: AssetIdentifier,
    ) -> Result<(), VmExecutionError> {
        let event_data = FTTransferEventData {
            sender,
            recipient,
            asset_identifier,
            amount,
        };
        let event = StacksTransactionEvent::FTEvent(FTEventType::FTTransferEvent(event_data));

        self.push_to_event_batch(event);
        Ok(())
    }

    pub fn register_ft_mint_event(
        &mut self,
        recipient: PrincipalData,
        amount: u128,
        asset_identifier: AssetIdentifier,
    ) -> Result<(), VmExecutionError> {
        let event_data = FTMintEventData {
            recipient,
            asset_identifier,
            amount,
        };
        let event = StacksTransactionEvent::FTEvent(FTEventType::FTMintEvent(event_data));

        self.push_to_event_batch(event);
        Ok(())
    }

    pub fn register_ft_burn_event(
        &mut self,
        sender: PrincipalData,
        amount: u128,
        asset_identifier: AssetIdentifier,
    ) -> Result<(), VmExecutionError> {
        let event_data = FTBurnEventData {
            sender,
            asset_identifier,
            amount,
        };
        let event = StacksTransactionEvent::FTEvent(FTEventType::FTBurnEvent(event_data));

        self.push_to_event_batch(event);
        Ok(())
    }
}

/// Successful return of a contract initialization
///
/// Contains the result of the execution of the top-level expressions, and the cost of executing
/// them.
#[derive(Debug, PartialEq)]
pub struct ContractInitReturn {
    pub ret: Option<Value>,
    pub cost: CostMeter,
}

/// Initialize a contract, executing all of the top-level expressions and
/// registering all of the definitions in the context. Returns the value
/// returned from the last top-level expression.
pub fn initialize_contract(
    global_context: &mut GlobalContext,
    contract_context: &mut ContractContext,
    sponsor: Option<PrincipalData>,
    contract_analysis: &ContractAnalysis,
) -> Result<ContractInitReturn, VmExecutionError> {
    let publisher: PrincipalData = contract_context.contract_identifier.issuer.clone().into();

    let mut call_stack = CallStack::new();
    let epoch = global_context.epoch_id;
    let clarity_version = *contract_context.get_clarity_version();
    let engine = global_context.engine.clone();
    let init_context = ClarityWasmContext::new_init(
        global_context,
        contract_context,
        &mut call_stack,
        Some(publisher.clone()),
        Some(publisher),
        sponsor.clone(),
        Some(contract_analysis),
    );
    let module = init_context
        .contract_context()
        .with_wasm_module(|wasm_module| {
            Module::from_binary(&engine, wasm_module)
                .map_err(|e| VmExecutionError::Wasm(WasmError::UnableToLoadModule(e)))
        })?;
    let mut store = Store::new(&engine, init_context);
    let mut linker = Linker::new(&engine);
    // Link in the host interface functions.
    link_host_functions(&mut linker)?;
    linker
        .define_cost_globals(&mut store)
        .map_err(|e| VmExecutionError::Wasm(WasmError::UnableToLoadModule(e)))?;

    let instance = linker
        .instantiate(&mut store, &module)
        .map_err(|e| VmExecutionError::Wasm(WasmError::UnableToLoadModule(e)))?;

    // Call the `.top-level` function, which contains all top-level expressions
    // from the contract.
    let top_level = instance
        .get_func(&mut store, ".top-level")
        .ok_or(VmExecutionError::Wasm(WasmError::DefinesNotFound))?;

    // Get the return type of the top-level expressions function
    let ty = top_level.ty(&mut store);
    let results_iter = ty.results();
    let mut results = vec![];
    for result_ty in results_iter {
        results.push(placeholder_for_type(result_ty));
    }

    top_level
        .call(&mut store, &[], results.as_mut_slice())
        .map_err(|e| {
            error_mapping::resolve_error(e, instance, &mut store, &epoch, &clarity_version)
        })?;

    // Save the compiled Wasm module into the contract context
    store.data_mut().contract_context_mut()?.set_wasm_module(
        module
            .serialize()
            .map_err(|e| VmExecutionError::Wasm(WasmError::WasmCompileFailed(e)))?,
    );

    // Get the type of the last top-level expression with a return value
    // or default to `None`.
    let return_type = contract_analysis.expressions.iter().rev().find_map(|expr| {
        contract_analysis
            .type_map
            .as_ref()
            .and_then(|type_map| type_map.get_type_expected(expr))
    });

    let ret = if let Some(return_type) = return_type {
        let memory = instance
            .get_memory(&mut store, "memory")
            .ok_or(VmExecutionError::Wasm(WasmError::MemoryNotFound))?;
        wasm_to_clarity_value(return_type, 0, &results, memory, &mut &mut store, epoch)
            .map(|(val, _offset)| val)?
    } else {
        None
    };

    let cost = linker
        .get_used_cost(&mut store)
        .map_err(|_| VmExecutionError::Wasm(WasmError::GlobalNotFound("cost-*".to_string())))?;

    Ok(ContractInitReturn { ret, cost })
}
