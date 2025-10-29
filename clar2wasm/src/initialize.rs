use clarity::vm::analysis::ContractAnalysis;
use clarity::vm::contexts::GlobalContext;
use clarity::vm::errors::{Error, RuntimeErrorType, WasmError};
use clarity::vm::events::*;
use clarity::vm::types::{AssetIdentifier, BuffData, PrincipalData, QualifiedContractIdentifier};
use clarity::vm::{CallStack, ContractContext, Value};
use stacks_common::types::chainstate::StacksBlockId;
use wasmtime::{Linker, Module, Store};

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
            contract_analysis,
        }
    }

    pub fn push_sender(&mut self, sender: PrincipalData) {
        if let Some(current) = self.sender.take() {
            self.sender_stack.push(current);
        }
        self.sender = Some(sender);
    }

    pub fn pop_sender(&mut self) -> Result<PrincipalData, Error> {
        self.sender
            .take()
            .ok_or(RuntimeErrorType::NoSenderInContext.into())
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

    pub fn pop_caller(&mut self) -> Result<PrincipalData, Error> {
        self.caller
            .take()
            .ok_or(RuntimeErrorType::NoCallerInContext.into())
            .inspect(|_| {
                self.caller = self.caller_stack.pop();
            })
    }

    pub fn push_at_block(&mut self, bhh: StacksBlockId) {
        self.bhh_stack.push(bhh);
    }

    pub fn pop_at_block(&mut self) -> Result<StacksBlockId, Error> {
        self.bhh_stack
            .pop()
            .ok_or(Error::Wasm(WasmError::WasmGeneratorError(
                "Could not pop at_block".to_string(),
            )))
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
    pub fn contract_context_mut(&mut self) -> Result<&mut ContractContext, Error> {
        match &mut self.contract_context_mut {
            Some(contract_context) => Ok(contract_context),
            None => Err(Error::Wasm(WasmError::DefineFunctionCalledInRunMode)),
        }
    }

    pub fn push_to_event_batch(&mut self, event: StacksTransactionEvent) {
        if let Some(batch) = self.global_context.event_batches.last_mut() {
            batch.events.push(event);
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

    pub fn register_print_event(&mut self, value: Value) -> Result<(), Error> {
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
    ) -> Result<(), Error> {
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
    ) -> Result<(), Error> {
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
    ) -> Result<(), Error> {
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
    ) -> Result<(), Error> {
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
    ) -> Result<(), Error> {
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
    ) -> Result<(), Error> {
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
    ) -> Result<(), Error> {
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
    ) -> Result<(), Error> {
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
pub struct ContractInit {
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
) -> Result<ContractInit, Error> {
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
                .map_err(|e| Error::Wasm(WasmError::UnableToLoadModule(e)))
        })?;
    let mut store = Store::new(&engine, init_context);
    let mut linker = Linker::new(&engine);
    // Link in the host interface functions.
    link_host_functions(&mut linker)?;
    linker
        .define_cost_globals(&mut store)
        .map_err(|e| Error::Wasm(WasmError::UnableToLoadModule(e)))?;

    let instance = linker
        .instantiate(&mut store, &module)
        .map_err(|e| Error::Wasm(WasmError::UnableToLoadModule(e)))?;

    // Call the `.top-level` function, which contains all top-level expressions
    // from the contract.
    let top_level = instance
        .get_func(&mut store, ".top-level")
        .ok_or(Error::Wasm(WasmError::DefinesNotFound))?;

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
            .map_err(|e| Error::Wasm(WasmError::WasmCompileFailed(e)))?,
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
            .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;
        wasm_to_clarity_value(return_type, 0, &results, memory, &mut &mut store, epoch)
            .map(|(val, _offset)| val)?
    } else {
        None
    };

    let cost = linker
        .get_used_cost(&mut store)
        .map_err(|_| Error::Wasm(WasmError::GlobalNotFound("cost-*".to_string())))?;

    Ok(ContractInit { ret, cost })
}
