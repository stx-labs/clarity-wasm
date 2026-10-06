# Mainnet contracts

Copies of Stacks mainnet contracts used by the `mainnet` benchmark. The sources are unmodified:
they are byte for byte the source returned by `/v2/contracts/source/{address}/{name}` of the Hiro
API, so that the benchmarks run the code that runs on mainnet.

The benchmark deploys them under the transient test address, which keeps the relative contract
references (`.sbtc-registry`) working. Contracts they depend on but which are not relevant to the
benchmarked functions are replaced by stubs defined in `mainnet.rs`.

| File | Mainnet contract | Clarity | Fetched |
|---|---|---|---|
| `sbtc-token.clar` | `SM3VDXK3WZZSA84XXFKAFAF15NNZX32CTSG82JFQ4.sbtc-token` | 3 | 2026-10-06 |
| `sbtc-registry.clar` | `SM3VDXK3WZZSA84XXFKAFAF15NNZX32CTSG82JFQ4.sbtc-registry` | 3 | 2026-10-06 |
| `BNS-V2.clar` | `SP2QEZ06AGJ3RKJPBV14SY1V5BBFNAW33D96YPGZF.BNS-V2` | 2 | 2026-10-06 |
| `commission-trait.clar` | `SP2QEZ06AGJ3RKJPBV14SY1V5BBFNAW33D96YPGZF.commission-trait` | 2 | 2026-10-06 |
| `nft-trait.clar` | `SP2PABAF9FTAJYNFZH93XENAJ8FVY99RRM50D2JG9.nft-trait` (deployed at its mainnet address, as BNS-V2 refers to it by its fully qualified name) | 1 | 2026-10-06 |
