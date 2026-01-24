       / / /     ▶ clarity-wasm
      | | |        Compile Clarity to Wasm.
       \ \ \       Generate WebAssembly from your Clarity code for fast and portable execution.

<div align="center">

[![Introduction](https://img.shields.io/badge/%23-%20Introduction%20-orange?labelColor=gray)](#introduction) [![Features](https://img.shields.io/badge/%23-Features-orange?labelColor=gray)](#features) [![Quick Start](https://img.shields.io/badge/%23-Quick%20Start-orange?labelColor=gray)](#quick-start) [![Documentation](https://img.shields.io/badge/%23-Documentation-orange?labelColor=gray)](#documentation) [![Contribute](https://img.shields.io/badge/%23-Contribute-orange?labelColor=gray)](#contribute) [![codecov](https://codecov.io/gh/stacks-network/clarity-wasm/graph/badge.svg?token=WtR78mrRYT)](https://codecov.io/gh/stacks-network/clarity-wasm)

</div>

---

## Introduction

`clar2wasm` is a compiler for generating [WebAssembly](https://webassembly.org/) from [Clarity](https://github.com/clarity-lang/reference).

**Version**: 2026 | **Status**: Production-Ready

## Features

## Quick-start

### Clone the repository

This repository includes the stacks-blockchain as a submodule, to keep in sync with the proper version of the clarity crate defined there. To clone this repo and its submodule, use:

```sh
git clone --recurse-submodules https://github.com/stacks-network/clarity-wasm.git
```

If you have cloned this repository without the `--recurse-submodules` flag, you can use:

```sh
git submodule update --init --recursive
```

### Command line tool

Install the command line tool, `clar2wasm` with:

```sh
cargo install --path clar2wasm
```

Once installed, try compiling one of our examples:

```sh
clar2wasm tests/contracts/define-read-only-0.clar
```

This will generate a wasm file, `tests/contracts/define-read-only-0.wasm`, from the Clarity source code.

You can view the text format of the generated Wasm by using a tool like [`wasm2wat`](https://github.com/WebAssembly/wabt):

```sh
wasm2wat tests/contracts/define-read-only-0.wasm
```

The output should contain the definition of the `simple` function:

```wasm
  (func $simple (type 2) (result i64 i64)
    (local i32)
    global.get 0
    local.set 0
    block (result i64 i64)  ;; label = @1
      i64.const 42
      i64.const 0
    end
    local.get 0
    global.set 0)
```

### Crate

`clar2wasm` is also available as a Rust library crate, to embed into other Rust projects.

## Documentation

### Top-Level Expressions

Any top-level expressions from a Clarity contract are added into a `.top-level` function that is exported from the generated Wasm module. This function should be called only once, during contract deployment. This top-level code also includes calls to the host-interface functions to register definitions in the contract.

### ABI

WebAssembly only supports basic number types, `i32`, `i64`, `f32`, and `f64`. We need to decide how to map Clarity types into these Wasm types.

- `int`: pair of `i64`s (upper, lower)
- `uint`: pair of `i64`s (upper, lower)
- `bool`: `i32` (`0` for false, `1` for true)
- `principal`: `i32` offset in call stack, `i32` length; call stack contains 21 bytes for standard principal (1 byte version, 20 byte Hash160) followed by 1 byte indicating the length of the contract name, which, if non-zero, is followed by the contract name string.
- `buff`: `i32` offset in call stack, `i32` length
- `string-ascii`: `i32` offset in call stack, `i32` length
- `string-utf8`: `i32` offset in call stack, `i32` length; the string is represented as array of 4 byte (big-endian) Unicode scalars
- `list`: `i32` offset in call stack, `i32` length
- `tuple`: each value in the tuple concatenated
- `optional`: `i32` indicator (`0` for `none`, `1` for `some`), followed by value for `some`
- `response`: `i32` indicator (`0` for `err`, `1` for `ok`) followed by ok value, then err value
- When a type is not known, for example, in a `response` where either the `ok` or the `err` are never used, the `NoType` is represented with an `i32` with a value of `0`.

When the return value of a function requires memory space, this space should be allocated by the caller and the offset for that space should be passed to the callee, following the arguments. For example, we can look at the following function:

```clarity
(define-read-only (get-boolean-string (b bool))
  (if b "true" "false")
)
```

This function takes a `bool` and returns a `(string-ascii 5)`. The generated Wasm function would take as arguments:

- `I32` representing the boolean
- `I32` representing the offset of the return value's memory space
- `I32` representing the length of the return value's memory space

For consistency with other types, the Wasm function would still return these two `I32`s for offset and length of the return value, even though that is not necessary for the caller.

### Memory Management

Web Assembly provides a simple linear memory, accessible with load/store operations. This memory is also exported for access from the host. For the Clarity VM, at the base of this memory, starting at offset 0, we are storing literals that do not fit into the scalar types supported by Wasm, for example, string literals. When used in the code, the literals are loaded from a constant offset. During compilation, the top of the literal memory is tracked by the field `literal_memory_end` in the `WasmGenerator` structure.

Constants defined in the contract (with `define-constant`) are also stored in this literal memory space. The values for the constants are written into the preallocated memory inside of the `.top-level` function.

After the literals, space may be allocated for passing arguments into the contract being called. Simple arguments are passed directly to the function, but those that require stack space (see [ABI](#abi)) will be written to this location. If the return value from the contract call requires stack space, then this will follow the arguments' space.

After this argument space, we build a call stack, where function local values that do not fit into scalars are stored. A global variable is defined in the Wasm module to maintain a stack pointer. At the beginning of every function, we insert the function prologue, which saves the current stack pointer to a local variable, which we can call the frame pointer. The frame pointer is the base of the current function's frame, its space in the call stack, and the function's local values can be accessed via offsets from this frame pointer. The stack pointer is then incremented for any space that gets reserved for the current function. Every function also has a function epilogue, which must be called upon exit from the function. The epilogue pops the function's frame from the call stack, since its locals are no longer needed, by setting the stack pointer equal to its frame pointer.

It may be helpful to clarify this with an example. Consider the following Clarity code:

```clarity
(define-private (do-concat (a (string-ascii 16)) (b (string-ascii 16)))
  (len (concat a b))
)

(define-read-only (hello (to (string-ascii 16)))
  (do-concat "hello " to)
)
```

The `concat` expression in the `do-concat` function creates a new string by concatenating the two input strings. This new string needs to be stored in the call stack, in that function's frame. The type of this expression is `(string-ascii 32)`, so in this case, we need to allocate 32 bytes on the call stack for the result. Before exiting the `do-concat` function, our linear memory will look like this:

```
stack pointer ->     +-------------------+
                     |         .         |
                     |  32 byte string   | <- Frame for do-concat
                     |         .         |
frame pointer ->     +-------------------+ <- Frame for example (no space allocated)
                     |         to        | <- Argument memory
                     +-------------------+
                     |      "hello "     | <- Literal memory
0 ->                 +-------------------+
```

In this diagram, the "frame pointer" is actually the frame pointer for both the `example` function and the `do-concat` function, because `example` does not require any space in its frame.

### Standard Library

Certain Clarity operations are implemented as functions in [_standard.wat_](clar2wasm/src/standard/standard.wat). This text format is then used during the build process to generate _standard.wasm_ which gets loaded into `clar2wasm`. Any operations that are cleaner to implement as a function call instead of directly generating Wasm instructions go into this library. For example, you can find the Clarity-style implementation of arithmetic operations in this library. These need to be written out manually because WebAssembly only supports 64-bit integers. The library implements 128-bit arithmetic, with the overflow checks that Clarity requires.

### Host Interface

When executing the compiled Clarity code, it needs to interact with the host - for example reading/writing to the MARF, emitting events, etc. We define a host interface that the generated Wasm code can call to perform these operations. Since these functions are type-agnostic, values are passed back and forth on the stack. The host function is responsible for marshalling/unmarshalling values to/from the Wasm format as needed (see ABI section above). These functions are imported by the standard library module, and it is the responsibility of the host to provide implementations of them.

| Clarity Operation | Host Function | Inputs | Outputs |
| --- | --- | --- | --- |
| `var-get` | `get_variable` | - ` var_name`: string (offset: i32, length: i32) | - |
|  |  | - `result`: stack pointer (offset: i32, length: i32) |  |
| `var-set` | `set_variable` | - `var_name`: string (offset: i32, length: i32) | - |
|  |  | - `value`: stack pointer (offset: i32, length: i32) |  |

## Benchmarking

Benchmarks are run and their results published on a continuous basis using [github-action-benchmark].
The results are published to GitHub pages and are available [here].

[github-action-benchmark]: https://github.com/benchmark-action/github-action-benchmark
[here]: https://stacks-network.github.io/clarity-wasm/dev/bench/

#### Generate a flamegraph

Run the bench command with `--features flamegraph` and `--profile-time <seconds>` flags. 

For example:
```shell
cargo bench --bench comparison --features flamegraph -- --profile-time 10 "wasm_add"
```
Output `target/criterion/wasm_add/profile/flamegraph.svg` preview:

![bench-flamegraph](docs/images/bench-flamegraph-example.png?raw=true)

#### Generate a protobuf and svg graph

Run the bench command with `--features pb` and `--profile-time <seconds>` flags. Then use [`pprof`](https://github.com/google/pprof) to generate a graph.

For example:
```shell
cargo bench --bench comparison --features pb -- --profile-time 10 "wasm_add"
$GOPATH/bin/pprof -svg "target/criterion/wasm_add/profile/profile.pb"
```
Output `profile001.svg` preview:

![bench-protobuf-graph](docs/images/bench-protobuf-graph-example.png?raw=true)

## Contribute

### Using local paths for dependencies

When modifying both the `clar2wasm` crate and the `stacks-core` crates, you can use the `[patch]` section in .cargo/config to specify local paths for these dependencies. This will allow you to test your changes to both crates together, without the need to first untested changes push to GitHub.

Add the following to *clarity-wasm/.cargo/config*

```toml
[patch.'https://github.com/stacks-network/stacks-core.git']
clarity = { path = "./stacks-core/clarity" }
``````

Similarly, in the stacks-core directory, you can add the following to *stacks-core/.cargo/config*

```toml
[patch.'https://github.com/stacks-network/stacks-core.git']
clarity = { path = "clarity" }
stacks-common = { path = "stacks-common" }
pox-locking = { path = "pox-locking" }
libstackerdb = { path = "libstackerdb" }
stx-genesis = { path = "stx-genesis"}
stacks = { package = "stackslib", path = "stackslib" }
libsigner = { path = "libsigner" }
stacks-signer = { path = "stacks-signer" }

[patch.'https://github.com/stacks-network/clarity-wasm.git']
clar2wasm = { package = "clar2wasm", path = "../clar2wasm/." }
```

Note that these patch configurations should not be checked into the repositories, because we want the default behavior to be to use the git repo paths.

### Formatting

To standardize the formatting of the code, we use rustfmt. To format your changes using the standard options, run:

```sh
cargo +nightly fmt-stacks
```
