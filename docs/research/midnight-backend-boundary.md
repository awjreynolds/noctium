# Midnight backend boundary for a Lean frontend

Context pointer: [GitHub issue #3, Map the deployable Midnight backend boundary](https://github.com/awjreynolds/noctium/issues/3)

Research checked on 2026-11-16 against official Midnight documentation and repositories.

## Findings

- The documented contract build path accepts Compact source and an output directory. The generated bundle contains ZKIR circuits, prover and verifier keys, JavaScript and TypeScript contract bindings, and a compiler JSON description. Midnight.js deployment then pairs the generated contract module with those compile artifacts. [Build a private smart contract](https://docs.midnight.network/guides/build-a-private-smart-contract) [Deploying and operating a contract](https://docs.midnight.network/guides/deploy-and-operate)
- `midnight-zkir` publicly defines the ZKIR format, VM, and CLI. Its `zkir compile-many` command turns `.zkir` files into prover and verifier keys. The repository describes ZKIR as the circuit format targeted by Compact's compiler. The reviewed official docs do not document a complete direct-ZKIR route that also produces the generated contract bindings and other artifacts used by Midnight.js deployment. [midnight-zkir repository](https://github.com/midnightntwrk/midnight-zkir)
- The compatibility matrix checked on 2026-11-16 listed ledger 9, Compact toolchain 0.36.0, language version 0.28.0, Compact runtime 0.21.0, on-chain runtime 4.0.0, and proof server 9.0.0. The [updated baseline](compact-equivalence-baseline.md) records the 2026-11-17 client patch. Compact 0.36 generates ZKIR version 3. [Current compatibility matrix](https://docs.midnight.network/relnotes/support-matrix) [Ledger 9 upgrade](https://docs.midnight.network/relnotes/ledger-9) [Compact 0.36 release notes](https://docs.midnight.network/relnotes/compact/toolchain-0.36.0)
- ZKIR and the on-chain runtime are separate components. The 2026-11-16 ledger 9 notes list the on-chain runtime as version 4.0.0, while Compact 0.36's release notes describe ZKIR version 3 as its backend. The [updated baseline](compact-equivalence-baseline.md) records the 2026-11-17 client patch. [Current compatibility matrix](https://docs.midnight.network/relnotes/support-matrix) [Ledger 9 upgrade](https://docs.midnight.network/relnotes/ledger-9) [Compact 0.36 release notes](https://docs.midnight.network/relnotes/compact/toolchain-0.36.0)
- Contract artifacts are version-sensitive. Compact 0.36 changes verifier keys when recompiling contracts that used ZKIR v2. A deployed contract needs matching keys, supplied through its maintenance authority, or it needs redeployment. Compact 0.36 also requires Compact runtime 0.21.x. [Compact 0.36 release notes](https://docs.midnight.network/relnotes/compact/toolchain-0.36.0)

## What this evidence establishes

The official documented pipeline proves one complete route from Compact source to generated circuits, keys, bindings, and deployment inputs. The `midnight-zkir` repository documents compilation of `.zkir` files into prover and verifier keys. Reviewed official sources do not document a complete direct-ZKIR contract bundle. This evidence describes available routes. It does not require Noctium to adopt Compact as its source semantics or backend.

Any direct-ZKIR route needs a tested contract interface and deployment bundle. Moriarty's current direct ZKIR compiler is a relevant additional reference; see [Moriarty overlap research](moriarty-overlap.md).
