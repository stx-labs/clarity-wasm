#![allow(clippy::expect_used, clippy::unwrap_used)]

//! Benchmarks comparing the Clarity interpreter with the WebAssembly runtime on single operations.
//!
//! Each operation is the body of a `step` function, folded over a list argument of `n` elements.
//! The contract is the same for every `n`, so that only the work grows with `n`, and not the size
//! of the code (which would also grow the cost of loading the Wasm module). The cost of one
//! operation is the slope of the time over `n`, minus the slope of the `noop` baseline, which
//! accounts for the fold, the call to `step` and passing the list.
//!
//! Operations are measured as calls within a single transaction, the fixed cost of a whole
//! transaction is measured by the `comparison` benchmark. See [`common`] for how benchmarks are
//! run.

mod common;

use std::time::Duration;

use clarity::vm::contexts::{ExecutionState, InvocationContext};
use clarity::vm::Value;
use common::{bench_calls, check, criterion_config, Contract, Scenario};
use criterion::{criterion_group, criterion_main, Criterion};

/// The lengths of the folded list. The contract accepts lists of up to the last one.
const SIZES: [usize; 3] = [1, 500, 1000];

/// The type of the elements of the folded list.
#[derive(Clone, Copy)]
enum Elem {
    Int,
    UInt,
}

impl Elem {
    fn name(self) -> &'static str {
        match self {
            Elem::Int => "int",
            Elem::UInt => "uint",
        }
    }

    /// The list `1..=n`.
    fn list(self, n: usize) -> Value {
        let values = (1..=n as u128)
            .map(|i| match self {
                Elem::Int => Value::Int(i as i128),
                Elem::UInt => Value::UInt(i),
            })
            .collect();
        Value::cons_list_unsanitized(values).unwrap()
    }
}

/// An operation, as the body of `(define-private (step (x elem) (acc acc)) body)`.
struct Op {
    name: &'static str,
    elem: Elem,
    /// The type of the accumulator, which is also the type of `body`.
    acc: &'static str,
    /// The initial value of the accumulator.
    init: &'static str,
    body: &'static str,
    /// Definitions needed by `body`.
    defs: &'static str,
    /// Contracts deployed before the benchmarked one, as `(name, source)`.
    dependencies: &'static [(&'static str, &'static str)],
}

const fn op(
    name: &'static str,
    elem: Elem,
    acc: &'static str,
    init: &'static str,
    body: &'static str,
) -> Op {
    Op {
        name,
        elem,
        acc,
        init,
        body,
        defs: "",
        dependencies: &[],
    }
}

const fn op_with(
    name: &'static str,
    elem: Elem,
    acc: &'static str,
    init: &'static str,
    body: &'static str,
    defs: &'static str,
) -> Op {
    Op {
        name,
        elem,
        acc,
        init,
        body,
        defs,
        dependencies: &[],
    }
}

const BUFF_32: &str = "0x0000000000000000000000000000000000000000000000000000000000000000";
const BUFF_20: &str = "0x0000000000000000000000000000000000000000";

const CALLEE: &[(&str, &str)] = &[("callee", "(define-public (id (v int)) (ok v))")];

#[rustfmt::skip]
const OPS: &[Op] = &[
    // Baseline: the fold, the call to `step` and passing the list.
    op("noop", Elem::Int, "int", "0", "acc"),

    // Arithmetic and comparisons
    op("add", Elem::Int, "int", "0", "(+ x acc)"),
    op("add-uint", Elem::UInt, "uint", "u0", "(+ x acc)"),
    op("sub", Elem::Int, "int", "0", "(- acc x)"),
    op("mul", Elem::Int, "int", "0", "(* x x)"),
    op("div", Elem::Int, "int", "0", "(/ 1000000 x)"),
    op("mod", Elem::Int, "int", "0", "(mod 1000000 x)"),
    op("pow", Elem::Int, "int", "0", "(pow x 2)"),
    op("sqrti", Elem::Int, "int", "0", "(sqrti x)"),
    op("log2", Elem::Int, "int", "0", "(log2 x)"),
    op("bit-xor", Elem::Int, "int", "0", "(bit-xor x acc)"),
    op("lt", Elem::Int, "bool", "false", "(< x 500)"),
    op("is-eq", Elem::Int, "bool", "false", "(is-eq x 500)"),
    op("to-uint", Elem::Int, "uint", "u0", "(to-uint x)"),

    // Control flow and bindings
    op("if", Elem::Int, "int", "0", "(if (< x 500) x acc)"),
    op("let", Elem::Int, "int", "0", "(let ((a x)) a)"),
    op_with("private-call", Elem::Int, "int", "0", "(id x)", "(define-private (id (v int)) v)"),

    // Optionals
    op("some-unwrap", Elem::Int, "int", "0", "(unwrap-panic (some x))"),
    op("default-to", Elem::Int, "int", "0", "(default-to acc (some x))"),
    op("match-some", Elem::Int, "int", "0", "(match (some x) v v acc)"),

    // Tuples
    op("tuple-get", Elem::Int, "int", "0", "(get a {a: x, b: acc})"),
    op("tuple-merge", Elem::Int, "int", "0", "(get b (merge {a: x} {b: acc}))"),

    // Sequences
    op("list-len", Elem::Int, "uint", "u0", "(len (list x x x x))"),
    op("element-at", Elem::Int, "int", "0", "(default-to 0 (element-at? (list x acc x acc) u2))"),
    op("append", Elem::Int, "uint", "u0", "(len (append (list x x) x))"),
    op("buff-concat", Elem::Int, "uint", "u0", "(len (concat 0x0102030405060708 0x0102030405060708))"),
    op("string-concat", Elem::Int, "uint", "u0", r#"(len (concat "hello" "world"))"#),
    op("int-to-ascii", Elem::Int, "uint", "u0", "(len (int-to-ascii x))"),

    // Hashing
    op("sha256", Elem::Int, "(buff 32)", BUFF_32, "(sha256 x)"),
    op("keccak256", Elem::Int, "(buff 32)", BUFF_32, "(keccak256 x)"),
    op("hash160", Elem::Int, "(buff 20)", BUFF_20, "(hash160 x)"),

    // Serialization
    op("to-consensus-buff", Elem::Int, "uint", "u0", "(len (unwrap-panic (to-consensus-buff? x)))"),
    op("consensus-roundtrip", Elem::Int, "int", "0", "(unwrap-panic (from-consensus-buff? int (unwrap-panic (to-consensus-buff? x))))"),

    // Chain state
    op_with("var-get", Elem::Int, "int", "0", "(var-get v)", "(define-data-var v int 0)"),
    op_with("var-set", Elem::Int, "bool", "true", "(var-set v x)", "(define-data-var v int 0)"),
    op_with("map-set", Elem::Int, "bool", "true", "(map-set m x x)", "(define-map m int int)"),
    op_with("map-get-miss", Elem::Int, "int", "0", "(default-to acc (map-get? m x))", "(define-map m int int)"),
    op_with("ft-mint", Elem::UInt, "bool", "true", "(unwrap-panic (ft-mint? tok x tx-sender))", "(define-fungible-token tok)"),
    op_with("ft-get-balance", Elem::UInt, "uint", "u0", "(ft-get-balance tok tx-sender)", "(define-fungible-token tok)"),
    op("stx-get-balance", Elem::UInt, "uint", "u0", "(stx-get-balance tx-sender)"),
    op("stacks-block-height", Elem::UInt, "uint", "u0", "stacks-block-height"),
    op("print", Elem::Int, "int", "0", "(print x)"),

    // Contract calls
    Op {
        dependencies: CALLEE,
        ..op("contract-call", Elem::Int, "int", "0", "(unwrap-panic (contract-call? .callee id x))")
    },
];

impl Op {
    fn scenario(&self) -> Scenario {
        let max = SIZES[SIZES.len() - 1];
        let Op {
            elem,
            acc,
            init,
            body,
            defs,
            ..
        } = self;
        let elem = elem.name();
        let source = format!(
            r#"
            {defs}
            (define-private (step (x {elem}) (acc {acc}))
                {body})
            (define-public (run (l (list {max} {elem})))
                (ok (fold step l {init})))
            "#
        );

        let target = format!("op-{}", self.name);
        let contracts = self
            .dependencies
            .iter()
            .map(|(name, source)| Contract::new(*name, *source))
            .chain([Contract::new(target.clone(), source)])
            .collect();
        Scenario::new(contracts, target, "run")
    }
}

/// Produces the arguments of `run`: the list of `n` elements.
fn list_arg(
    elem: Elem,
    n: usize,
) -> impl Fn(&mut ExecutionState, &mut InvocationContext) -> Vec<Value> {
    move |_, _| vec![elem.list(n)]
}

fn operations(c: &mut Criterion) {
    for op in OPS {
        let scenario = op.scenario();
        let group_name = format!("ops-{}", op.name);
        let mut group = c.benchmark_group(&group_name);

        for n in SIZES {
            let param = n.to_string();
            let init = list_arg(op.elem, n);
            check(&group_name, Some(&param), &scenario, &init);
            bench_calls(&mut group, Some(&param), &scenario, init);
        }

        group.finish();
    }
}

criterion_group! {
    name = ops;
    config = criterion_config()
        .warm_up_time(Duration::from_secs(1))
        .measurement_time(Duration::from_secs(2))
        .sample_size(20);
    targets = operations
}
criterion_main!(ops);
