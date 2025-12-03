#![cfg(test)]
pub mod unit_tests;

use clar2wasm::compile;
use clar2wasm::datastore::Datastore;
use clar2wasm::tools::{crosscheck, crosscheck_with_env, TestConfig, TestEnvironment};
use clar2wasm::wasm_utils::get_type_in_memory_size;
use clarity::types::StacksEpochId;
use clarity::vm::costs::LimitedCostTracker;
use clarity::vm::errors::{CheckErrorKind, VmExecutionError as Error};
use clarity::vm::types::{
    ListTypeData, QualifiedContractIdentifier, StandardPrincipalData, TypeSignature,
};
use clarity::vm::{ClarityVersion, Value};

/// Name of the buffer that will fill the empty space.
const IGNORE_BUFFER_NAME: &str = "ignore";
/// Size in memory for the buffer that will fill the empty space's (offset, len).
const IGNORE_BUFFER_SIZE: usize = 8;
/// Minimum size needed in memory to create a filling buffer
const IGNORE_BUFFER_MIN_SIZE_NEEDED: usize = IGNORE_BUFFER_SIZE + IGNORE_BUFFER_NAME.len();

/// Size of a page in Wasm
const WASM_PAGE_SIZE: usize = 65536;

#[allow(clippy::expect_used)]
fn as_oom_check_snippet(
    snippet: &str,
    args_types: &[TypeSignature],
    epoch: StacksEpochId,
    version: ClarityVersion,
) -> String {
    let compiled_module = Datastore::new()
        .as_analysis_db()
        .execute(|analysis_db| {
            compile(
                snippet,
                &QualifiedContractIdentifier::new(
                    StandardPrincipalData::transient(),
                    ("foo").into(),
                ),
                LimitedCostTracker::new_free(),
                version,
                epoch,
                analysis_db,
                false,
            )
            .map_err(|e| CheckErrorKind::Expects(format!("Compilation failure {e:?}")))
        })
        .expect("Could not compile snippet")
        .module;

    // we look for the total number of pages that were allocated for the module.
    let memory_pages = compiled_module
        .memories
        .iter()
        .next()
        .expect("Couldn't find a memory")
        .initial as usize;
    // we look for the first byte in memory which doesn't contain useful data.
    let stack_pointer_value = match compiled_module
        .globals
        .iter()
        .find(|g| g.name.as_ref().is_some_and(|name| name == "stack-pointer"))
        .expect("Couldn't find stack-pointer global")
        .kind
    {
        walrus::GlobalKind::Local(walrus::InitExpr::Value(walrus::ir::Value::I32(val))) => {
            val as usize
        }
        _ => unreachable!("stack-pointer should be a locally declared global with a i32 value"),
    };

    // WORKAROUND: this is to ignore arguments that are computed at runtime and should be removed after fixing
    //             [issue #587](https://github.com/stacks-network/clarity-wasm/issues/587)
    let args_space_needed = args_types
        .iter()
        .map(|ty| get_type_in_memory_size(ty, false))
        .sum::<i32>() as usize;

    // the free space on the last page that we want to fill is the substraction of the total number of bytes
    // for all the available pages and the last byte which will contain useful data.
    let mut free_space_on_memory_page = memory_pages * WASM_PAGE_SIZE - stack_pointer_value;

    let total_space_needed = IGNORE_BUFFER_MIN_SIZE_NEEDED + args_space_needed;
    if free_space_on_memory_page < total_space_needed {
        free_space_on_memory_page += WASM_PAGE_SIZE;
    }

    format!(
        "(define-constant {IGNORE_BUFFER_NAME} 0x{})\n{snippet}",
        "00".repeat(free_space_on_memory_page - total_space_needed)
    )
}

// TODO: deprecate after fixing [issue #587](https://github.com/stacks-network/clarity-wasm/issues/587)
pub fn crosscheck_oom_with_non_literal_args(
    snippet: &str,
    args_types: &[TypeSignature],
    expected: Result<Option<Value>, Error>,
) {
    crosscheck(
        &as_oom_check_snippet(
            snippet,
            args_types,
            TestConfig::latest_epoch(),
            TestConfig::clarity_version(),
        ),
        expected,
    );
}

pub fn crosscheck_oom(snippet: &str, expected: Result<Option<Value>, Error>) {
    crosscheck_oom_with_non_literal_args(snippet, &[], expected)
}

pub fn crosscheck_oom_with_env(
    snippet: &str,
    expected: Result<Option<Value>, Error>,
    env: TestEnvironment,
) {
    crosscheck_with_env(
        &as_oom_check_snippet(snippet, &[], env.epoch, env.version),
        expected,
        env,
    );
}

pub(crate) fn list_of(elem: TypeSignature, max_len: u32) -> TypeSignature {
    TypeSignature::SequenceType(clarity::vm::types::SequenceSubtype::ListType(
        ListTypeData::new_list(elem, max_len).unwrap(),
    ))
}
