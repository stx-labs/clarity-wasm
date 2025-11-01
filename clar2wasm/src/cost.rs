//! Functionality to track the costs of running Clarity.
//!
//! The cost computations in this module are meant to be a full match with the interpreter
//! implementation of the Clarity runtime.

mod clar1;
mod clar2;
mod clar3;

use std::fmt;

use clarity::vm::{ClarityName, ClarityVersion};
use walrus::ir::{BinaryOp, Instr, UnaryOp, Unop};
use walrus::{FunctionId, GlobalId, InstrSeqBuilder, LocalId, Module};
use wasmtime::{AsContextMut, Extern, Global, Mutability, Val, ValType};

use crate::error_mapping::ErrorMap;
use crate::wasm_generator::{GeneratorError, WasmGenerator};
use crate::words::Word;

type Result<T, E = GeneratorError> = std::result::Result<T, E>;

/// Values of the cost globals
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CostMeter {
    pub runtime: u64,
    pub read_count: u64,
    pub read_length: u64,
    pub write_count: u64,
    pub write_length: u64,
}

/// Globals used for cost tracking
#[derive(Debug, Clone, Copy)]
pub struct CostGlobals {
    pub runtime: Global,
    pub read_count: Global,
    pub read_length: Global,
    pub write_count: Global,
    pub write_length: Global,
}

/// Trait for a `Linker` that can be used to retrieve the cost globals.
pub trait CostLinker<T> {
    /// Get the cost globals.
    fn get_cost_globals(&self, store: impl AsContextMut<Data = T>)
        -> wasmtime::Result<CostGlobals>;
    /// Define the cost globals.
    fn define_cost_globals(&mut self, store: impl AsContextMut<Data = T>) -> wasmtime::Result<()>;
}

/// Convenience to use the same error string in multiple places
#[derive(Debug)]
enum GetCostGlobalsError {
    Runtime,
    ReadCount,
    ReadLength,
    WriteCount,
    WriteLength,
}

impl fmt::Display for GetCostGlobalsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use GetCostGlobalsError::*;

        match self {
            Runtime => write!(f, "missing `cost-runtime` global"),
            ReadCount => write!(f, "missing `cost-read-count` global"),
            ReadLength => write!(f, "missing `cost-read-length` global"),
            WriteCount => write!(f, "missing `cost-write-count` global"),
            WriteLength => write!(f, "missing `cost-write-length` global"),
        }
    }
}

impl std::error::Error for GetCostGlobalsError {}

impl<T> CostLinker<T> for wasmtime::Linker<T> {
    fn get_cost_globals(
        &self,
        mut store: impl AsContextMut<Data = T>,
    ) -> wasmtime::Result<CostGlobals> {
        let mut store = store.as_context_mut();

        let runtime = self.get(&mut store, "clarity", "cost-runtime");
        let read_count = self.get(&mut store, "clarity", "cost-read-count");
        let read_length = self.get(&mut store, "clarity", "cost-read-length");
        let write_count = self.get(&mut store, "clarity", "cost-write-count");
        let write_length = self.get(&mut store, "clarity", "cost-write-length");

        use GetCostGlobalsError::*;

        fn unwrap_global_or(
            ext: Option<Extern>,
            err: GetCostGlobalsError,
        ) -> Result<Global, GetCostGlobalsError> {
            match ext {
                Some(Extern::Global(global)) => Ok(global),
                _ => Err(err),
            }
        }

        Ok(CostGlobals {
            runtime: unwrap_global_or(runtime, Runtime)?,
            read_count: unwrap_global_or(read_count, ReadCount)?,
            read_length: unwrap_global_or(read_length, ReadLength)?,
            write_count: unwrap_global_or(write_count, WriteCount)?,
            write_length: unwrap_global_or(write_length, WriteLength)?,
        })
    }

    fn define_cost_globals(
        &mut self,
        mut store: impl AsContextMut<Data = T>,
    ) -> wasmtime::Result<()> {
        let mut store = store.as_context_mut();

        define_cost_global_import(self, &mut store, "cost-runtime", 0)?;
        define_cost_global_import(self, &mut store, "cost-read-count", 0)?;
        define_cost_global_import(self, &mut store, "cost-read-length", 0)?;
        define_cost_global_import(self, &mut store, "cost-write-count", 0)?;
        define_cost_global_import(self, &mut store, "cost-write-length", 0)?;

        Ok(())
    }
}

fn define_cost_global_import<T>(
    linker: &mut wasmtime::Linker<T>,
    mut store: impl AsContextMut<Data = T>,
    name: &str,
    value: u64,
) -> wasmtime::Result<()> {
    use wasmtime::{Global, GlobalType};

    let mut store = store.as_context_mut();

    let global = Global::new(
        &mut store,
        GlobalType::new(ValType::I64, Mutability::Var),
        Val::I64(value as _),
    )?;

    linker.define(&mut store, "clarity", name, global)?;

    Ok(())
}

/// Trait to manipulate the values of a cost meter.
pub trait AccessCostMeter<T>: CostLinker<T> {
    /// Get the current value of the cost meter.
    fn get_cost_meter(
        &self,
        mut store: impl AsContextMut<Data = T>,
    ) -> wasmtime::Result<CostMeter> {
        let mut store = store.as_context_mut();

        let globals = self.get_cost_globals(&mut store)?;

        use GetCostGlobalsError::*;

        Ok(CostMeter {
            runtime: globals.runtime.get(&mut store).i64().ok_or(Runtime)? as _,
            read_count: globals.read_count.get(&mut store).i64().ok_or(ReadCount)? as _,
            read_length: globals
                .read_length
                .get(&mut store)
                .i64()
                .ok_or(ReadLength)? as _,
            write_count: globals
                .write_count
                .get(&mut store)
                .i64()
                .ok_or(WriteCount)? as _,
            write_length: globals
                .write_length
                .get(&mut store)
                .i64()
                .ok_or(WriteLength)? as _,
        })
    }

    /// Set the value of the cost meter.
    fn set_cost_meter(
        &self,
        mut store: impl AsContextMut<Data = T>,
        meter: CostMeter,
    ) -> wasmtime::Result<()> {
        let mut store = store.as_context_mut();

        let globals = self.get_cost_globals(&mut store)?;

        globals
            .runtime
            .set(&mut store, Val::I64(meter.runtime as _))?;
        globals
            .read_count
            .set(&mut store, Val::I64(meter.read_count as _))?;
        globals
            .read_length
            .set(&mut store, Val::I64(meter.read_length as _))?;
        globals
            .write_count
            .set(&mut store, Val::I64(meter.write_count as _))?;
        globals
            .write_length
            .set(&mut store, Val::I64(meter.write_length as _))?;

        Ok(())
    }
}

impl<D, T: CostLinker<D>> AccessCostMeter<D> for T {}

/// Extension trait allowing for words to generate cost tracking code
/// during traversal.
pub trait WordCharge {
    /// Generate cost tracking code for this word.
    ///
    /// See [`ChargeGenerator::charge`] for more details.
    fn charge<C: ChargeGenerator>(
        &self,
        generator: &C,
        instrs: &mut InstrSeqBuilder,
        n: impl Into<Scalar>,
    ) -> Result<()>;
}

impl<W: ?Sized + Word> WordCharge for W {
    fn charge<C: ChargeGenerator>(
        &self,
        generator: &C,
        instrs: &mut InstrSeqBuilder,
        n: impl Into<Scalar>,
    ) -> Result<()> {
        generator.charge(instrs, self.name(), n)
    }
}

/// Generators of cost tracking code.
pub trait ChargeGenerator {
    /// The cost tracking context. Only present if charging code should be emitted.
    fn cost_context(&self) -> Option<(&ChargeContext, &Module)>;

    /// Generate code that charges the appropriate cost for the given word.
    ///
    /// `n` is a scaling factor that depends on the word being charged, but can only be known
    /// during traversal. The value *must* be either a `u32` or a `LocalId` representing a local
    /// with type `I32`.
    /// If the word has a constant cost, the value will be ignored. This is useful in words where
    /// the cost is known to be constant during traversal.
    ///
    /// Code will be generated iff [`cost_context`] returns `Some`.
    fn charge(
        &self,
        instrs: &mut InstrSeqBuilder,
        word_name: ClarityName,
        n: impl Into<Scalar>,
    ) -> Result<()> {
        let n = n.into();

        if let Some((ctx, module)) = self.cost_context() {
            let maybe_word_cost = match ctx.clarity_version {
                ClarityVersion::Clarity1 => clar1::WORD_COSTS.get(&word_name),
                ClarityVersion::Clarity2 => clar2::WORD_COSTS.get(&word_name),
                ClarityVersion::Clarity3 => clar3::WORD_COSTS.get(&word_name),
                ClarityVersion::Clarity4 => todo!("Clarity4 implementation"),
            };

            match maybe_word_cost {
                Some(cost) => ctx.emit(instrs, module, cost, n)?,
                None => {
                    return Err(GeneratorError::InternalError(format!(
                        "'{}' do not exists in costs table for {}",
                        word_name, ctx.clarity_version
                    )))
                }
            }
        }

        Ok(())
    }
}

impl ChargeGenerator for WasmGenerator {
    fn cost_context(&self) -> Option<(&ChargeContext, &Module)> {
        self.cost_context.as_ref().map(|ctx| (ctx, &self.module))
    }
}

/// A 32-bit unsigned integer to be resolved at either compile-time or run-time.
#[derive(Clone, Copy)]
pub enum Scalar {
    Compile(u32),
    Run(LocalId),
}

impl From<u32> for Scalar {
    fn from(n: u32) -> Self {
        Self::Compile(n)
    }
}

impl From<LocalId> for Scalar {
    fn from(n: LocalId) -> Self {
        Self::Run(n)
    }
}

/// Trait for allowing us to not repeat ourselves in resolving a scalar.
trait ScalarGet {
    fn scalar_get(&mut self, module: &Module, scalar: Scalar) -> Result<&mut Self>;
}

impl ScalarGet for InstrSeqBuilder<'_> {
    fn scalar_get(&mut self, module: &Module, scalar: Scalar) -> Result<&mut Self> {
        Ok(match scalar {
            Scalar::Compile(c) => self.i64_const(c as _),
            Scalar::Run(l) => {
                let local = module.locals.get(l);

                match local.ty() {
                    walrus::ValType::I32 => {}
                    ty => {
                        return Err(GeneratorError::InternalError(format!(
                            "cost local should be of type i32 but is of type {ty}"
                        )))
                    }
                }

                self.local_get(l)
                    // this is so we don't have to repeat this code in the `caf` functions
                    .instr(Instr::Unop(Unop {
                        op: UnaryOp::I64ExtendUI32,
                    }))
            }
        })
    }
}

/// Context required from a generator to emit cost tracking code.
pub struct ChargeContext {
    pub clarity_version: ClarityVersion,
    pub runtime: GlobalId,
    pub read_count: GlobalId,
    pub read_length: GlobalId,
    pub write_count: GlobalId,
    pub write_length: GlobalId,
    pub runtime_error: FunctionId,
}

#[derive(Debug, Clone, Copy)]
struct WordCost {
    runtime: Caf,
    read_count: Caf,
    read_length: Caf,
    write_count: Caf,
    write_length: Caf,
}

/// Cost assessment function
#[derive(Debug, Clone, Copy)]
enum Caf {
    /// Constant cost
    Constant(u32),
    /// Linear cost, scaling with `n`
    ///
    /// a * n + b
    Linear { a: u64, b: u64 },
    /// Logarithmic cost, scaling with `n`
    ///
    /// a * log2(n) + b
    LogN { a: u64, b: u64 },
    /// Linear logarithmic cost, scaling with `n`
    ///
    /// a * n * log2(n) + b
    NLogN { a: u64, b: u64 },
    /// Zero cost - equivalent to `Constant(0)`
    None,
}

impl ChargeContext {
    fn emit(
        &self,
        instrs: &mut InstrSeqBuilder,
        module: &Module,
        cost: &WordCost,
        n: Scalar,
    ) -> Result<()> {
        self.emit_with_caf(
            instrs,
            module,
            cost.runtime,
            self.runtime,
            ErrorMap::CostOverrunRuntime as _,
            n,
        )?;
        self.emit_with_caf(
            instrs,
            module,
            cost.read_count,
            self.read_count,
            ErrorMap::CostOverrunReadCount as _,
            n,
        )?;
        self.emit_with_caf(
            instrs,
            module,
            cost.read_length,
            self.read_length,
            ErrorMap::CostOverrunReadLength as _,
            n,
        )?;
        self.emit_with_caf(
            instrs,
            module,
            cost.write_count,
            self.write_count,
            ErrorMap::CostOverrunWriteCount as _,
            n,
        )?;
        self.emit_with_caf(
            instrs,
            module,
            cost.write_length,
            self.write_length,
            ErrorMap::CostOverrunWriteLength as _,
            n,
        )?;

        Ok(())
    }

    fn emit_with_caf(
        &self,
        instrs: &mut InstrSeqBuilder,
        module: &Module,
        params: Caf,
        global: GlobalId,
        err_code: i32,
        n: impl Into<Scalar>,
    ) -> Result<()> {
        match params {
            Caf::Constant(cost) => {
                caf_const(instrs, module, global, self.runtime_error, err_code, cost)
            }
            Caf::Linear { a, b } => caf_linear(
                instrs,
                module,
                global,
                self.runtime_error,
                err_code,
                n,
                a,
                b,
            ),
            Caf::LogN { a, b } => caf_logn(
                instrs,
                module,
                global,
                self.runtime_error,
                err_code,
                n,
                a,
                b,
            ),
            Caf::NLogN { a, b } => caf_nlogn(
                instrs,
                module,
                global,
                self.runtime_error,
                err_code,
                n,
                a,
                b,
            ),
            Caf::None => Ok(()),
        }
    }
}

fn caf_const(
    instrs: &mut InstrSeqBuilder,
    module: &Module,
    global: GlobalId,
    error: FunctionId,
    err_code: i32,
    cost: impl Into<Scalar>,
) -> Result<()> {
    let cost = cost.into();

    // global pushed onto the stack to subtract from later
    instrs.global_get(global);

    // cost
    instrs.scalar_get(module, cost)?;

    // global -= cost
    instrs
        .binop(BinaryOp::I64Sub)
        .global_set(global)
        .global_get(global)
        .i64_const(0)
        .binop(BinaryOp::I64LtS)
        .if_else(
            None,
            |builder| {
                builder.i32_const(err_code);
                builder.call(error);
            },
            |_| {},
        );

    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn caf_linear(
    instrs: &mut InstrSeqBuilder,
    module: &Module,
    global: GlobalId,
    error: FunctionId,
    err_code: i32,
    n: impl Into<Scalar>,
    a: u64,
    b: u64,
) -> Result<()> {
    let n = n.into();

    // global pushed onto the stack to subtract from later
    instrs.global_get(global);

    // cost = a * n + b
    instrs
        // n
        .scalar_get(module, n)?
        // a *
        .i64_const(a as _)
        .binop(BinaryOp::I64Mul)
        // b +
        .i64_const(b as _)
        .binop(BinaryOp::I64Add);

    // global -= cost
    instrs
        .binop(BinaryOp::I64Sub)
        .global_set(global)
        .global_get(global)
        .i64_const(0)
        .binop(BinaryOp::I64LtS)
        .if_else(
            None,
            |builder| {
                builder.i32_const(err_code);
                builder.call(error);
            },
            |_| {},
        );

    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn caf_logn(
    instrs: &mut InstrSeqBuilder,
    module: &Module,
    global: GlobalId,
    error: FunctionId,
    err_code: i32,
    n: impl Into<Scalar>,
    a: u64,
    b: u64,
) -> Result<()> {
    let n = n.into();

    // global pushed onto the stack to subtract from later
    instrs.global_get(global);

    // cost = a * log2(n) + b
    instrs
        // log2(n)
        // 63 minus leading zeros in `n`
        // n *must* be larger than 0
        .i64_const(63)
        .scalar_get(module, n)?
        .unop(UnaryOp::I64Clz)
        .binop(BinaryOp::I64Sub)
        // a *
        .i64_const(a as _)
        .binop(BinaryOp::I64Mul)
        // b +
        .i64_const(b as _)
        .binop(BinaryOp::I64Add);

    // global -= cost
    instrs
        .binop(BinaryOp::I64Sub)
        .global_set(global)
        .global_get(global)
        .i64_const(0)
        .binop(BinaryOp::I64LtS)
        .if_else(
            None,
            |builder| {
                builder.i32_const(err_code);
                builder.call(error);
            },
            |_| {},
        );

    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn caf_nlogn(
    instrs: &mut InstrSeqBuilder,
    module: &Module,
    global: GlobalId,
    error: FunctionId,
    err_code: i32,
    n: impl Into<Scalar>,
    a: u64,
    b: u64,
) -> Result<()> {
    let n = n.into();

    // global pushed onto the stack to subtract from later
    instrs.global_get(global);

    // cost = a * n * log2(n) + b
    instrs
        // log2(n)
        // 63 minus leading zeros in `n`
        // n *must* be larger than 0
        .i64_const(63)
        .scalar_get(module, n)?
        .unop(UnaryOp::I64Clz)
        .binop(BinaryOp::I64Sub)
        // n *
        .scalar_get(module, n)?
        .binop(BinaryOp::I64Mul)
        // a *
        .i64_const(a as _)
        .binop(BinaryOp::I64Mul)
        // b +
        .i64_const(b as _)
        .binop(BinaryOp::I64Add);

    // global -= cost
    instrs
        .binop(BinaryOp::I64Sub)
        .global_set(global)
        .global_get(global)
        .i64_const(0)
        .binop(BinaryOp::I64LtS)
        .if_else(
            None,
            |builder| {
                builder.i32_const(err_code);
                builder.call(error);
            },
            |_| {},
        );

    Ok(())
}

#[cfg(test)]
mod test_caf {
    //! The code in this module tests that the code generation in the `caf_*` functions is correct,
    //! *not* that the code generation of each word is correct.

    use super::*;

    #[test]
    fn constant() {
        let initial_cost_val = 1000000;

        for cost in 1..100 {
            let final_cost_val =
                execute_with_caf(0, initial_cost_val, |local| (Caf::Constant(cost), local))
                    .expect("execution with enough fuel should succeed");

            assert_eq!(
                final_cost_val,
                initial_cost_val - cost as u64,
                "should decrement accurately"
            );
        }
    }

    #[test]
    fn linear() {
        let initial_val = 1000000;

        let a = 2;
        let b = 3;

        for n in 0..100 {
            let cost = a * n + b;

            let final_val = execute_with_caf(n, initial_val, |local| {
                (
                    Caf::Linear {
                        a: a as _,
                        b: b as _,
                    },
                    local,
                )
            })
            .expect("execution with enough fuel should succeed");

            assert_eq!(
                final_val,
                initial_val - cost as u64,
                "should decrement accurately"
            );
        }
    }

    #[test]
    fn logn() {
        let initial_val = 1000000;

        let a = 2;
        let b = 3;

        // cost = (+ (* a (log2 n)) b))

        for n in 1..100u32 {
            let cost = a * n.ilog2() + b;

            let final_val = execute_with_caf(n as _, initial_val, |local| {
                (
                    Caf::LogN {
                        a: a as _,
                        b: b as _,
                    },
                    local,
                )
            })
            .expect("execution with enough fuel should succeed");

            assert_eq!(
                final_val,
                initial_val - cost as u64,
                "should decrement accurately"
            );
        }
    }

    #[test]
    fn nlogn() {
        let initial_val = 1000000;

        let a = 2;
        let b = 3;

        // cost = (+ (* a (* n (log2 n))) b))

        for n in 1..100u32 {
            let cost = a * n * n.ilog2() + b;

            let final_val = execute_with_caf(n as _, initial_val, |local| {
                (
                    Caf::NLogN {
                        a: a as _,
                        b: b as _,
                    },
                    local,
                )
            })
            .expect("execution with enough fuel should succeed");

            assert_eq!(
                final_val,
                initial_val - cost as u64,
                "should decrement accurately"
            );
        }
    }

    #[test]
    fn none() {
        let initial_val = 2;
        let fn_arg = 0;

        let final_val = execute_with_caf(fn_arg, initial_val, |local| (Caf::None, local))
            .expect("execution with enough fuel should succeed");

        assert_eq!(final_val, initial_val, "none caf should not cost");
    }

    const ERR_CODE: i32 = -42;

    fn execute_with_caf<S: Into<Scalar>>(
        arg: i32,
        initial: u64,
        caf: impl FnOnce(LocalId) -> (Caf, S),
    ) -> Result<u64, i64> {
        use wasmtime::{Engine, Linker, Module, Store};

        let engine = Engine::default();
        let binary = module_with_caf(caf);
        let module = Module::from_binary(&engine, &binary).unwrap();

        let mut linker = Linker::<()>::new(&engine);
        let mut store = Store::new(&engine, ());

        linker.define_cost_globals(&mut store).unwrap();
        linker
            .set_cost_meter(
                &mut store,
                CostMeter {
                    runtime: initial,
                    read_count: 0,
                    read_length: 0,
                    write_count: 0,
                    write_length: 0,
                },
            )
            .unwrap();

        let instance = linker.instantiate(&mut store, &module).unwrap();

        let func = instance
            .get_typed_func::<i32, i32>(&mut store, "identity")
            .unwrap();
        let err_code = instance.get_global(&mut store, "err-code").unwrap();

        match func.call(&mut store, arg) {
            Ok(_) => Ok(linker.get_cost_meter(&mut store).unwrap().runtime),
            Err(_) => Err(err_code.get(&mut store).unwrap_i64()),
        }
    }

    // The functions generated here is extremely simple (a: i32) -> a, but still allows for
    // understanding the runtime characteristics of any `Caf`.
    fn module_with_caf<S: Into<Scalar>>(caf: impl FnOnce(LocalId) -> (Caf, S)) -> Vec<u8> {
        use walrus::ir::Value;
        use walrus::{FunctionBuilder, InitExpr, Module, ValType};

        let mut module = Module::default();

        // we put in all the globals, but we only use `cost-runtime`
        let (cost_global, _) =
            module.add_import_global("clarity", "cost-runtime", ValType::I64, true);
        module.add_import_global("clarity", "cost-read-count", ValType::I64, true);
        module.add_import_global("clarity", "cost-read-length", ValType::I64, true);
        module.add_import_global("clarity", "cost-write-count", ValType::I64, true);
        module.add_import_global("clarity", "cost-write-length", ValType::I64, true);

        let error_global =
            module
                .globals
                .add_local(ValType::I32, true, InitExpr::Value(Value::I32(0)));

        let arg = module.locals.add(ValType::I32);

        // runtime error that takes an I32 and traps, similar to the stdlib
        let mut error = FunctionBuilder::new(&mut module.types, &[ValType::I32], &[]);
        let mut body = error.func_body();
        body.local_get(arg);
        body.global_set(error_global);
        body.unreachable();
        let error = error.finish(vec![arg], &mut module.funcs);

        let mut identity =
            FunctionBuilder::new(&mut module.types, &[ValType::I32], &[ValType::I32]);

        let mut body = identity.func_body();

        let (caf, scalar) = caf(arg);
        match caf {
            Caf::Constant(n) => {
                caf_const(&mut body, &module, cost_global, error, ERR_CODE, n).unwrap()
            }
            Caf::Linear { a, b } => caf_linear(
                &mut body,
                &module,
                cost_global,
                error,
                ERR_CODE,
                scalar,
                a,
                b,
            )
            .unwrap(),
            Caf::LogN { a, b } => caf_logn(
                &mut body,
                &module,
                cost_global,
                error,
                ERR_CODE,
                scalar,
                a,
                b,
            )
            .unwrap(),
            Caf::NLogN { a, b } => caf_nlogn(
                &mut body,
                &module,
                cost_global,
                error,
                ERR_CODE,
                scalar,
                a,
                b,
            )
            .unwrap(),
            Caf::None => {}
        }
        body.local_get(arg);
        let identity = identity.finish(vec![arg], &mut module.funcs);

        module.exports.add("identity", identity);
        module.exports.add("err-code", error_global);

        module.emit_wasm()
    }
}
