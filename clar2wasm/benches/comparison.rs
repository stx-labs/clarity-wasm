#![allow(clippy::expect_used, clippy::unwrap_used)]

use std::hint::black_box;

use clar2wasm::compile;
use clar2wasm::datastore::{BurnDatastore, Datastore, StacksConstants};
use clar2wasm::initialize::initialize_contract;
use clarity::consts::CHAIN_ID_TESTNET;
use clarity::types::{PrivateKey, StacksEpochId};
use clarity::util::hash::Keccak256Hash;
use clarity::util::secp256k1::{Secp256k1PrivateKey, Secp256k1PublicKey};
use clarity::vm::analysis::{run_analysis, AnalysisDatabase};
use clarity::vm::ast::build_ast_with_diagnostics;
use clarity::vm::contexts::{
    ExecutionState, FunctionExecutionOptions, GlobalContext, InvocationContext,
};
use clarity::vm::costs::LimitedCostTracker;
use clarity::vm::database::{ClarityDatabase, MemoryBackingStore};
use clarity::vm::resource_limiter::ResourceLimiter;
use clarity::vm::types::{QualifiedContractIdentifier, StandardPrincipalData, TupleData};
use clarity::vm::{
    eval_all, CallStack, ClarityName, ClarityVersion, ContractContext, ContractName, Value,
};
use criterion::measurement::Measurement;
use criterion::{criterion_group, criterion_main, Bencher, BenchmarkId, Criterion};
use paste::paste;
use pprof::criterion::{Output, PProfProfiler};

fn interpreter<M, F>(b: &mut Bencher<M>, fn_name: &str, clarity: &str, init: F)
where
    M: 'static + Measurement,
    F: FnOnce(&mut ExecutionState, &mut InvocationContext) -> Vec<Value>,
{
    let contract_id = QualifiedContractIdentifier::new(
        StandardPrincipalData::transient(),
        ContractName::try_from(format!("clarity-{fn_name}").as_str())
            .unwrap_or_else(|_| panic!("Failed to create contract name from clarity-{}", fn_name)),
    );
    let mut datastore = Datastore::new();
    let constants = StacksConstants::default();
    let burn_datastore = BurnDatastore::new(constants);
    let mut clarity_store = MemoryBackingStore::new();
    let mut conn = ClarityDatabase::new(&mut datastore, &burn_datastore, &burn_datastore);
    conn.begin();
    conn.set_clarity_epoch_version(StacksEpochId::latest())
        .unwrap();
    conn.commit().unwrap();
    let mut cost_tracker: LimitedCostTracker = LimitedCostTracker::new_free();
    let mut contract_context: ContractContext =
        ContractContext::new(contract_id.clone(), ClarityVersion::latest());

    let contract_str = clarity.to_string();

    // Create a new analysis database
    let mut analysis_db = AnalysisDatabase::new(&mut clarity_store);

    // Parse the contract
    let (ast, _, success) = build_ast_with_diagnostics(
        &contract_id,
        &contract_str,
        &mut cost_tracker,
        ClarityVersion::latest(),
        StacksEpochId::latest(),
    );

    if !success {
        panic!("Failed to parse contract");
    }

    // Run the analysis passes
    let mut contract_analysis = run_analysis(
        &contract_id,
        &ast.expressions,
        &mut analysis_db,
        false,
        cost_tracker,
        StacksEpochId::latest(),
        ClarityVersion::latest(),
        true,
        ResourceLimiter::unlimited(),
    )
    .expect("Failed to run analysis");

    let mut global_context = GlobalContext::new(
        false,
        CHAIN_ID_TESTNET,
        conn,
        contract_analysis.cost_track.take().unwrap(),
        StacksEpochId::latest(),
    );

    global_context.begin();

    // Initialize the contract
    eval_all(
        &ast.expressions,
        &mut contract_context,
        &mut global_context,
        None,
    )
    .expect("Failed to initialize the contract");

    let func = contract_context
        .lookup_function(fn_name)
        .expect("failed to lookup function");

    let mut call_stack = CallStack::new();
    let mut exec_state = ExecutionState {
        global_context: &mut global_context,
        call_stack: &mut call_stack,
    };

    let mut invoke_ctx = InvocationContext {
        contract_context: &contract_context,
        sender: Some(StandardPrincipalData::transient().into()),
        caller: Some(StandardPrincipalData::transient().into()),
        sponsor: None,
    };

    let args = init(&mut exec_state, &mut invoke_ctx);

    b.iter(|| {
        exec_state
            .execute_function_as_transaction(
                &invoke_ctx,
                &func,
                &args,
                FunctionExecutionOptions::default(),
            )
            .expect("Function call failed");
    });

    global_context.commit().unwrap();
}

fn webassembly<M, F>(b: &mut Bencher<M>, fn_name: &str, clarity: &str, init: F)
where
    M: 'static + Measurement,
    F: FnOnce(&mut ExecutionState, &mut InvocationContext) -> Vec<Value>,
{
    let contract_id = QualifiedContractIdentifier::new(
        StandardPrincipalData::transient(),
        ContractName::try_from(format!("clarity-{fn_name}").as_str())
            .unwrap_or_else(|_| panic!("Failed to create contract name from clarity-{}", fn_name)),
    );
    let mut datastore = Datastore::new();
    let constants = StacksConstants::default();
    let burn_datastore = BurnDatastore::new(constants);
    let mut clarity_store = MemoryBackingStore::new();
    let mut conn = ClarityDatabase::new(&mut datastore, &burn_datastore, &burn_datastore);
    conn.begin();
    conn.set_clarity_epoch_version(StacksEpochId::latest())
        .unwrap();
    conn.commit().unwrap();
    let cost_tracker: LimitedCostTracker = LimitedCostTracker::new_free();
    let mut contract_context: ContractContext =
        ContractContext::new(contract_id.clone(), ClarityVersion::latest());

    // Create a new analysis database
    let mut analysis_db = AnalysisDatabase::new(&mut clarity_store);

    let mut compilation = compile(
        clarity,
        &contract_id,
        cost_tracker,
        ClarityVersion::latest(),
        StacksEpochId::latest(),
        &mut analysis_db,
        false,
    )
    .expect("Failed compiling clarity to WASM");

    let mut global_context = GlobalContext::new(
        false,
        CHAIN_ID_TESTNET,
        conn,
        compilation.contract_analysis.cost_track.take().unwrap(),
        StacksEpochId::latest(),
    );

    contract_context.set_wasm_module(compilation.module.emit_wasm());

    global_context.begin();

    // Initialize the contract
    initialize_contract(
        &mut global_context,
        &mut contract_context,
        None,
        &compilation.contract_analysis,
    )
    .expect("Failed to initialize the contract");

    let func = contract_context
        .lookup_function(fn_name)
        .expect("failed to lookup function");

    let mut call_stack = CallStack::new();

    let mut exec_state = ExecutionState {
        global_context: &mut global_context,
        call_stack: &mut call_stack,
    };

    let mut invoke_ctx = InvocationContext {
        contract_context: &contract_context,
        sender: Some(StandardPrincipalData::transient().into()),
        caller: Some(StandardPrincipalData::transient().into()),
        sponsor: None,
    };

    let args = init(&mut exec_state, &mut invoke_ctx);

    b.iter(|| {
        exec_state
            .execute_function_as_transaction(
                &invoke_ctx,
                &func,
                &args,
                FunctionExecutionOptions::default(),
            )
            .expect("Function call failed");
    });

    global_context.commit().unwrap();
}

fn criterion_config() -> Criterion {
    if cfg!(feature = "flamegraph") {
        Criterion::default().with_profiler(PProfProfiler::new(100, Output::Flamegraph(None)))
    } else if cfg!(feature = "pb") {
        Criterion::default().with_profiler(PProfProfiler::new(100, Output::Protobuf))
    } else {
        Criterion::default()
    }
}

/// Used to declare benchmarks of clarity contracts to be run on both the interpreter and the
/// WebAssembly runtime.
/// Each arm should only be matched once and declares a criterion group that can then be picked up
/// by [`criterion_main!`].
macro_rules! decl_benches {
    // single
    ($(($fn_name:literal, $clarity:literal, [$($arg:expr),*])),* $(,)?) => {
        paste! {
            $(
                #[allow(non_snake_case)]
                fn [<single _ $fn_name>](c: &mut Criterion) {
                    let mut group = c.benchmark_group($fn_name);
                    group.bench_function("interpreter", |b| {
                        interpreter(
                            b,
                            black_box($fn_name),
                            black_box($clarity),
                            |_, _| vec![$(black_box($arg)),*]
                        );
                    });
                    group.bench_function("webassembly", |b| {
                        webassembly(
                            b,
                            black_box($fn_name),
                            black_box($clarity),
                            |_, _| vec![$(black_box($arg)),*]
                        );
                    });
                }
            )*

            criterion_group! {
                name = single;
                config = criterion_config();
                targets = $([<single _ $fn_name>]),*
            }
        }
    };
    // range
    ($(($fn_name:literal, $range:expr, $produce_clarity:expr, $init:expr)),* $(,)?) => {
        paste! {
            $(
                #[allow(non_snake_case)]
                fn [<range _ $fn_name>](c: &mut Criterion) {
                    let mut group = c.benchmark_group($fn_name);

                    let produce_clarity = $produce_clarity;

                    for i in $range {
                        let clarity = produce_clarity(i);
                        group.bench_with_input(BenchmarkId::new("interpreter", i), &i, |b, _| {
                            interpreter(
                                b,
                                black_box($fn_name),
                                black_box(&clarity),
                                |exec_state, invoke_ctx| { $init(i, exec_state, invoke_ctx) }
                            )
                        });
                        group.bench_with_input(BenchmarkId::new("webassembly", i), &i, |b, _| {
                            webassembly(
                                b,
                                black_box($fn_name),
                                black_box(&clarity),
                                |exec_state, invoke_ctx| { $init(i, exec_state, invoke_ctx) }
                            )
                        });
                    }
                }
            )*

            criterion_group! {
                name = range;
                config = criterion_config();
                targets = $([<range _ $fn_name>]),*
            }
        }
    }
}

decl_benches! {
    (
        "add",
        r#"
         (define-read-only (add (x int) (y int))
             (+ x y)
         )
        "#,
        [Value::Int(42), Value::Int(12345)]
    ),
}

decl_benches! {
    (
        "fold_add_square",
        (1..=1001).step_by(50),
        |i| format!(r#"
        (define-private (add_square (x int) (y int))
            (+ (* x x) y)
        )

        (define-public (fold_add_square (l (list {i} int)) (init int))
            (ok (fold add_square l init))
        )
        "#),
        |i, _, _| vec![Value::cons_list_unsanitized((1..=i).map(Value::Int).collect()).unwrap(), Value::Int(0)]
    ),
    (
        "map_set_entries",
        (1..=1001).step_by(50),
        |i| format!(r#"
        (define-map mymap int int)

        (define-public (map_set_entries (l (list {i} int)))
            (begin
                (map set_entry l)
                (ok true)
            )
        )

        (define-private (set_entry (entry int))
            (map-set mymap entry entry)
        )
        "#),
        |i, _: &mut ExecutionState, _: &mut InvocationContext| vec![Value::cons_list_unsanitized((1..=i).map(Value::Int).collect()).unwrap()]
    ),
    (
        "add_prices",
        (1..51).step_by(2),
        |_i| r"
        (define-map oracle_data
            { source: uint, symbol: uint }
            { amount: uint }
        )

        (define-map oracle_sources
            { source: uint }
            { key: (buff 33) }
        )

        (define-read-only (slice-16 (b (buff 48)) (start uint))
            (unwrap-panic (as-max-len? (unwrap-panic (slice? b start (+ start u16))) u16))
        )

        (define-read-only (extract-source (msg (buff 48)))
            (buff-to-uint-le (slice-16 msg u0))
        )

        (define-read-only (extract-symbol (msg (buff 48)))
            (buff-to-uint-le (slice-16 msg u16))
        )

        (define-read-only (extract-amount (msg (buff 48)))
            (buff-to-uint-le (slice-16 msg u32))
        )

        (define-read-only (verify-signature (msg (buff 48)) (sig (buff 65)) (key (buff 33)))
            (is-eq (unwrap-panic (secp256k1-recover? (keccak256 msg) sig)) key)
        )

        (define-private (add-price (msg (buff 48)) (sig (buff 65)))
            (let ((source (extract-source msg)))
                (if (verify-signature msg sig (get key (unwrap-panic (map-get? oracle_sources {source: source}))))
                    (let ((symbol (extract-symbol msg)) (amount (extract-amount msg)) (data-opt (map-get? oracle_data {source: source, symbol: symbol})))
                        (if (is-some data-opt)
                            (let ((data (unwrap-panic data-opt)))
                                (begin
                                    (map-set oracle_data {source: source, symbol: symbol} {amount: amount})
                                    (ok true)
                                )
                            )
                            (begin
                                (map-set oracle_data {source: source, symbol: symbol} {amount: amount})
                                (ok true)
                            )
                        )
                    )
                    (err u62)
                )
            )
        )

        (define-private (call-add-price (price {msg: (buff 48), sig: (buff 65)}))
            (unwrap-panic (add-price (get msg price) (get sig price)))
        )

        (define-public (add_source (source uint) (key (buff 33)))
            (begin
                (map-set oracle_sources { source: source } { key: key })
                (ok true)
            )
        )

        (define-public (add_prices (prices (list 1001 {msg: (buff 48), sig: (buff 65)})))
            (begin
                (map call-add-price prices)
                (ok true)
            )
        )
        ".to_string(),
        |i, execution_state: &mut ExecutionState, invoke_ctx: &mut InvocationContext| vec![add_prices_init(i, execution_state, invoke_ctx)]
    ),
    (
        "poc2",
        (1..123).step_by(3),
        |i| format!(r#"
            (define-public (poc2 (v int))
                (begin
                    (let ((a {{a: {{a: {{b: 1,c: 1,d: 1,e: 1,f: 1,g: 1,h: 1,i: 1,j: 1,k: 1,l: 1,m: 1,n: 1,o: 1,p: 1,q: 1,r: 1,s: 1,t: 1,u-: 1,v: 1,w: 1,x: 1,y: 1,z: 1,A: 1,B: 1,C: 1,D: 1,E: 1,F: 1,G: 1,H: 1,I: 1,J: 1,K: 1,L: 1,M: 1,N: 1,O: 1,P: 1,Q: 1,R: 1,S: 1,T: 1,U: 1,V: 1,W: 1,X: 1,Y: 1,Z: 1,ba: 1,bb: 1,bc: 1,bd: 1,be: 1,bf: 1,bg: 1,bh: 1,bi: 1,bj: 1,bk: 1,bl: 1,bm: 1,bn: 1,bo: 1,bp: 1,bq: 1,br: 1,bs: 1,bt: 1,bu: 1,bv: 1,bw: 1,bx: 1,by: 1,bz: 1,bA: 1,bB: 1,bC: 1,bD: 1,bE: 1,bF: 1,bG: 1,bH: 1,bI: 1,bJ: 1,bK: 1,bL: 1,bM: 1,bN: 1,bO: 1,bP: 1,bQ: 1,bR: 1,bS: 1,bT: 1,bU: 1,bV: 1,bW: 1,bX: 1,bY: 1,bZ: 1,ca: 1,cb: 1,cc: 1,cd: 1,ce: 1,cf: 1,cg: 1,ch: 1,ci: 1,cj: 1,ck: 1,cl: 1,cm: 1,cn: 1,co: 1,cp: 1,cq: 1,cr: 1,cs: 1,ct: 1,cu: 1,cv: 1,cw: 1,cx: 1,cy: 1,cz: 1,cA: 1,cB: 1,cC: 1,cD: 1,cE: 1,cF: 1,cG: 1,cH: 1,cI: 1,cJ: 1,cK: 1,cL: 1,cM: 1,cN: 1,cO: 1,cP: 1,cQ: 1,cR: 1,cS: 1,cT: 1,cU: 1,cV: 1,cW: 1,cX: 1,cY: 1,cZ: 1,da: 1,db: 1,dc: 1,dd: 1,de: 1,df: 1,dg: 1,dh: 1,di: 1,dj: 1,dk: 1,dl: 1,dm: 1,dn: 1,do: 1,dp: 1,dq: 1,dr: 1,ds: 1,dt: 1,du: 1,dv: 1,dw: 1,dx: 1,dy: 1,dz: 1,dA: 1,dB: 1,dC: 1,dD: 1,dE: 1,dF: 1,dG: 1,dH: 1,dI: 1,dJ: 1,dK: 1,dL: 1,dM: 1,dN: 1,dO: 1,dP: 1,dQ: 1,dR: 1,dS: 1,dT: 1,dU: 1,dV: 1,dW: 1,dX: 1,dY: 1,dZ: 1,ea: 1,eb: 1,ec: 1,ed: 1,ee: 1,ef: 1,eg: 1,eh: 1,ei: 1,ej: 1,ek: 1,el: 1,em: 1,en: 1,eo: 1,ep: 1,eq: 1,er: 1,es: 1,et: 1,eu: 1,ev: 1,ew: 1,ex: 1,ey: 1,ez: 1,eA: 1,eB: 1,eC: 1,eD: 1,eE: 1,eF: 1,eG: 1,eH: 1,eI: 1,eJ: 1,eK: 1,eL: 1,eM: 1,eN: 1,eO: 1}}}}}}) (b (list{} ))) b)
                    (ok (+ 1 1))
                )
            )"#,
            " a".repeat(i)
        ),
        |_, _, _| vec![Value::Int(42)]
    ),
}

fn add_prices_init(
    n: usize,
    execution_state: &mut ExecutionState,
    invocation_context: &mut InvocationContext,
) -> Value {
    let mut prices = Vec::with_capacity(n);

    let sk = Secp256k1PrivateKey::from_hex(
        "9bf49a6a0755f953811fce125f2683d50429c3bb49e074147e0089a52eae155f01",
    )
    .unwrap();
    let pk = Secp256k1PublicKey::from_private(&sk);

    let source = 1u128;
    let symbol = 2u128;
    let amount = 3u128;

    let mut msg = [0; 48];
    msg[0..16].copy_from_slice(&source.to_le_bytes());
    msg[16..32].copy_from_slice(&symbol.to_le_bytes());
    msg[32..48].copy_from_slice(&amount.to_le_bytes());
    let msg_hash = Keccak256Hash::from_data(&msg);

    // NOTE: the way we have to construct the signature here would be better handled closer to
    //       the upstream types themselves.
    let sig = sk.sign(msg_hash.as_bytes()).unwrap();
    let sig = sig.to_secp256k1_recoverable().unwrap();
    let (recovery_id, compact) = sig.serialize_compact();

    let mut sig_bytes = [0u8; 65];
    sig_bytes[..64].copy_from_slice(&compact);
    sig_bytes[64] = recovery_id.to_i32() as u8;

    for _ in 0..n {
        prices.push(Value::Tuple(
            TupleData::from_data(vec![
                (
                    ClarityName::from_literal("msg"),
                    Value::buff_from(msg.to_vec()).unwrap(),
                ),
                (
                    ClarityName::from_literal("sig"),
                    Value::buff_from(sig_bytes.to_vec()).unwrap(),
                ),
            ])
            .unwrap(),
        ));
    }

    let func = invocation_context
        .contract_context
        .lookup_function("add_source")
        .expect("failed to lookup function");

    execution_state
        .execute_function_as_transaction(
            invocation_context,
            &func,
            &[
                Value::UInt(source),
                Value::buff_from(pk.to_bytes_compressed()).unwrap(),
            ],
            FunctionExecutionOptions::default(),
        )
        .expect("Adding source should succeed");

    Value::cons_list_unsanitized(prices).unwrap()
}

criterion_main!(single, range);
