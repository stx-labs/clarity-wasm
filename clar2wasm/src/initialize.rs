use clarity::vm::analysis::ContractAnalysis;
use clarity::vm::clarity_wasm::{AccessCostMeter, CostGlobals, CostMeter};
use clarity::vm::contexts::GlobalContext;
#[cfg(feature = "developer-mode")]
use clarity::vm::errors::RuntimeCheckErrorKind;
use clarity::vm::errors::{RuntimeError, VmExecutionError, WasmError};
use clarity::vm::events::*;
#[cfg(feature = "developer-mode")]
use clarity::vm::types::TypeSignature;
use clarity::vm::types::{AssetIdentifier, BuffData, PrincipalData, QualifiedContractIdentifier};
use clarity::vm::{CallStack, ContractContext, Value};
use stacks_common::types::chainstate::StacksBlockId;
#[cfg(feature = "developer-mode")]
use wasmtime::Val;
use wasmtime::{AsContextMut, Linker, Module, Store};

use crate::error_mapping;
use crate::linker::{link_cost_globals, link_host_functions};
use crate::wasm_utils::*;

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
    pub cost_globals: Option<CostGlobals>,
}

impl<'a, 'b> ClarityWasmContext<'a, 'b> {
    #[allow(clippy::too_many_arguments)]
    pub fn new_init(
        global_context: &'a mut GlobalContext<'b>,
        contract_context: &'a mut ContractContext,
        call_stack: &'a mut CallStack,
        sender: Option<PrincipalData>,
        caller: Option<PrincipalData>,
        sponsor: Option<PrincipalData>,
        contract_analysis: Option<&'a ContractAnalysis>,
        cost_globals: Option<CostGlobals>,
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
            cost_globals,
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
            cost_globals: None,
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
        None,
    );
    let module = init_context
        .contract_context()
        .with_wasm_module(|wasm_module| {
            Module::from_binary(&engine, wasm_module)
                .map_err(|e| VmExecutionError::Wasm(WasmError::UnableToLoadModule(e)))
        })?;
    let mut store = Store::new(&engine, init_context);
    let mut linker = Linker::new(&engine);
    // Link in the host interface functions and globals.
    link_host_functions(&mut linker)?;
    store.data_mut().cost_globals = Some(
        link_cost_globals(&mut linker, &mut store.as_context_mut())
            .map_err(|e| VmExecutionError::Wasm(WasmError::UnableToLoadModule(e.into())))?,
    );

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

/// Call a function in the contract, as an outside call (like a transaction)
/// would, linking the contract's Wasm module against this crate's host
/// functions. This mirrors `call_function` in stacks-core's
/// `clarity_wasm.rs`, except that it does not charge the contract-call cost
/// overhead, since it is only used by the test tooling, where cost tracking
/// is free.
#[cfg(feature = "developer-mode")]
#[allow(clippy::too_many_arguments)]
pub fn call_function(
    function_name: &str,
    args: &[Value],
    global_context: &mut GlobalContext,
    contract_context: &ContractContext,
    call_stack: &mut CallStack,
    sender: Option<PrincipalData>,
    caller: Option<PrincipalData>,
    sponsor: Option<PrincipalData>,
) -> Result<Value, VmExecutionError> {
    let epoch = global_context.epoch_id;
    let clarity_version = *contract_context.get_clarity_version();
    let engine = global_context.engine.clone();
    let context = ClarityWasmContext::new_run(
        global_context,
        contract_context,
        call_stack,
        sender,
        caller,
        sponsor,
        None,
    );

    let func_types = context
        .contract_context()
        .lookup_function(function_name)
        .ok_or(RuntimeCheckErrorKind::UndefinedFunction(
            function_name.to_string(),
        ))?;
    let module = context
        .contract_context()
        .with_wasm_module(|wasm_module| unsafe {
            Module::deserialize(&engine, wasm_module)
                .map_err(|e| VmExecutionError::Wasm(WasmError::UnableToLoadModule(e)))
        })?;
    let mut store = Store::new(&engine, context);
    let mut linker = Linker::new(&engine);

    // Link in the host interface functions.
    link_host_functions(&mut linker)?;

    let expected_args = func_types.get_arg_types();
    let mut cost_globals = link_cost_globals(&mut linker, &mut store.as_context_mut())
        .map_err(|e| VmExecutionError::Wasm(WasmError::UnableToLoadModule(e.into())))?;

    // The cost meter holds the cost from the caller before doing the contract
    // call. This is the value we instantiate the current cost globals with.
    let cost_meter = store.data().global_context.cost_meter;
    cost_globals
        .from_cost_meter(&mut store, &cost_meter)
        .map_err(|_| {
            VmExecutionError::Wasm(WasmError::GlobalNotFound("cost globals not found".into()))
        })?;

    store.data_mut().cost_globals = Some(cost_globals);
    let instance = linker
        .instantiate(&mut store, &module)
        .map_err(|e| VmExecutionError::Wasm(WasmError::UnableToLoadModule(e)))?;

    // Access the global stack pointer from the instance
    let stack_pointer =
        instance
            .get_global(&mut store, "stack-pointer")
            .ok_or(VmExecutionError::Wasm(WasmError::GlobalNotFound(
                "stack-pointer".to_string(),
            )))?;
    let mut offset = stack_pointer
        .get(&mut store)
        .i32()
        .ok_or(VmExecutionError::Wasm(WasmError::ValueTypeMismatch))?;

    let workspace_size = instance
        .get_global(&mut store, "workspace-size")
        .ok_or_else(|| {
            VmExecutionError::Wasm(WasmError::GlobalNotFound("workspace-size".to_owned()))
        })?;

    let memory = instance
        .get_memory(&mut store, "memory")
        .ok_or(VmExecutionError::Wasm(WasmError::MemoryNotFound))?;

    // Validate argument count
    if args.len() != expected_args.len() {
        return Err(VmExecutionError::RuntimeCheck(
            RuntimeCheckErrorKind::IncorrectArgumentCount(expected_args.len(), args.len()),
        ));
    }

    // Validate argument types
    for (arg, expected_type) in args.iter().zip(expected_args.iter()) {
        if !expected_type.admits(&epoch, arg)? {
            return Err(VmExecutionError::RuntimeCheck(
                RuntimeCheckErrorKind::TypeError(
                    Box::new(expected_type.clone()),
                    Box::new(TypeSignature::type_of(arg)?),
                ),
            ));
        }
    }

    // Ensure that the memory has enough space for the arguments
    let mut total_required_bytes = workspace_size
        .get(&mut store)
        .i32()
        .ok_or(VmExecutionError::Wasm(WasmError::ValueTypeMismatch))?
        as usize;
    for (arg, ty) in args.iter().zip(expected_args) {
        total_required_bytes += get_required_bytes(ty, arg)?;
    }

    ensure_memory(&memory, &mut store, total_required_bytes + offset as usize)?;

    // We call the specified function
    let func = instance.get_func(&mut store, function_name).ok_or(
        RuntimeCheckErrorKind::UndefinedFunction(function_name.to_string()),
    )?;

    // Convert the args into wasmtime values
    let mut wasm_args = vec![];
    for (arg, ty) in args.iter().zip(expected_args) {
        let (arg_vec, new_offset) = pass_argument_to_wasm(memory, &mut store, ty, arg, offset)?;
        wasm_args.extend(arg_vec);
        offset = new_offset;
    }

    // Update the stack pointer after space is reserved for the arguments and
    // return values.
    stack_pointer
        .set(&mut store, Val::I32(offset))
        .map_err(|e| VmExecutionError::Wasm(WasmError::Runtime(e)))?;

    let return_type = func_types
        .get_return_type()
        .as_ref()
        .ok_or(VmExecutionError::Wasm(WasmError::ExpectedReturnValue))?
        .clone();

    // Call the function
    let mut results: Vec<_> = clar2wasm_ty(&return_type)
        .into_iter()
        .map(placeholder_for_type)
        .collect();
    func.call(&mut store, &wasm_args, &mut results)
        .map_err(|e| {
            error_mapping::resolve_error(e, instance, &mut store, &epoch, &clarity_version)
        })?;

    let updated_cost = cost_globals
        .to_cost_meter(&mut store.as_context_mut())
        .map_err(|e| VmExecutionError::Wasm(WasmError::Runtime(e)))?;
    store.as_context_mut().data_mut().global_context.cost_meter = updated_cost;
    // If the function returns a value, translate it into a Clarity `Value`
    wasm_to_clarity_value(&return_type, 0, &results, memory, &mut &mut store, epoch)
        .map(|(val, _offset)| val)
        .and_then(|option_value| {
            option_value.ok_or_else(|| VmExecutionError::Wasm(WasmError::ExpectedReturnValue))
        })
}
