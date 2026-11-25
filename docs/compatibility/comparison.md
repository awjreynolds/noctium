# Noctium and Compact capabilities

This comparison uses Compact 0.36.1, language 0.28, and the selected Noctium target for Midnight Ledger 9 and ZKIR 3.2.1. Scope varies by operation, type and execution path. [Pinned releases and evidence](compact-feature-matrix.json) · [Parity workstreams and acceptance](compact-parity.md)

## Contract features

| Area | Noctium | Compact 0.36.1 |
| --- | --- | --- |
| Types and control | Scoped Lean syntax for fields, bounded integers, Booleans, bytes, records, tuples, vectors and enums. Typed helpers, modules, bounded generics and finite loops. | Field, Uint, Boolean, Bytes, structs, tuples, vectors and enums. Circuits, modules, generics and bounded iteration. |
| Private witnesses | Typed host providers and wallet-owned cells. Compiler checks private flows to public sinks. Staged writes travel through the host journal. | Witness signatures, host-supplied implementations, application-managed private state and explicit disclosure. |
| Ledger | Native Impact lowering for checked state effects, typed calls and Ledger 9 events. Funded localnet evidence covers selected composed calls and the token port. | Ledger declarations, state operations, contract references and events through the supported compiler and runtime interfaces. |
| Cryptography | Typed Jubjub and foreign-field operations, byte and field hashing, and ECDSA, Schnorr and Ed25519 helpers with scoped evidence. | Hashing, typed curve operations and signature helpers through the standard and ZKIR v3 libraries. |
| Contract specifications | Lean theorems and tactics. The one-time claim has scoped correctness and privacy evidence. General compiler preservation is open. | The pinned compiler's source and generated interfaces provide the comparison baseline for executable contracts. |

[Compact language and compiler](https://github.com/LFDT-Minokawa/compact/tree/7fa3a117c5e7efe9d2c51da04263e5f0b3509144) · [Feature-level evidence and gaps](compact-feature-matrix.json) · [Noctium assurance scope](../designs/architecture.md#assurance-boundaries)

### Ledger collection gaps

The feature register links implemented Map, Set, List and Counter paths to their source and checks. Expression-valued Counter updates and scalar Lists have matched native and Compact fixtures. A funded development Ledger 9 run stored one finalized self-minted shielded coin in a Map, Cell, Set and List in the same call. A native query-context test also covers two-coin List ordering. Broader collection and SDK iterator cases remain open. [Funded receipt](../development/shielded-coin-collections-localnet-receipt.json) · [Counter checks](../development/native-counter.md) · [List checks](../development/native-lists.md)

Compact's List head returns `Maybe<T>`. Noctium's `headOrDefault` binds presence and typed defaults, while strict `head` requires a nonempty List. The scoped native examples cover Noctium's result shapes. Matched reference checks are still required for equivalence. [Pinned ledger ADT reference](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/doc/ledger-adt.mdx) · [Noctium List examples](../development/native-lists.md)

## Witness execution targets

✓ marks a documented execution path. The Compact column covers generated interfaces. An n/a entry refers to a compiler output target. The Noctium column names the qualification for each host.

| Host | Noctium execution path | Compact 0.36.1 compiler output |
| --- | --- | --- |
| Rust | ✓ Native witness runtime and localnet proof/client path. Optional per-contract Rust wrappers. [Rust witness guide](../development/typed-witnesses.md) | n/a |
| C / C++ | ✓ C ABI. C++ witness execution and finalized development calls. [Qualification](../development/typed-witness-qualification.md) | n/a |
| Kotlin / Android | ✓ Native library. Witnesses, proof and finality on an arm64 emulator. [Android guide](../development/android-witness-sdk.md) | n/a |
| Swift / Apple | ✓ Native library. Witnesses, proof and finality on macOS and the iOS simulator. [Swift guide](../development/swift-witness-sdk.md) | n/a |
| TypeScript / web | ✓ WASM witness execution and local proof verified in Chrome. [Web guide](../development/web-witness-sdk.md) | ✓ Generated JavaScript execution and TypeScript witness declarations. [Witness guide](https://docs.midnight.network/guides/private-state-witnesses) |

Noctium's host-neutral witness plan serves these runtimes. The OpenZeppelin timing command emits that plan and generates zero SDK bindings. [Benchmark](../development/oz-compile-performance.md)

## Full pinned ZKIR v3 instruction inventory

The pinned ZKIR 3.2.1 inventory contains 40 active instruction names. Noctium registers these names through scoped source routes. Each instruction has separate type, semantics and execution requirements. [Pinned ZKIR inventory and scope](zkir-feature-matrix.json)

| Instruction group | Active ZKIR instruction names |
| --- | --- |
| Scalar arithmetic and comparison | `add`, `mul`, `neg`, `inv`, `test_eq`, `less_than` |
| Logic and selection | `not`, `and`, `or`, `xor`, `cond_select` |
| Constraints | `assert`, `constrain_bits`, `constrain_eq`, `constrain_to_boolean` |
| Inputs, outputs and ledger binding | `public_input`, `private_input`, `impact`, `output`, `copy`, `load_constant` |
| Bytes and encoding | `encode`, `to_bytes`, `from_bytes`, `bytes_from_natives`, `bytes_into_natives`, `nth`, `reverse`, `slice`, `concat` |
| Hashes | `transient_hash`, `persistent_hash`, `sha512`, `keccak256`, `hash_to_curve` |
| Curve operations | `jubjub_scalar_from_native`, `ec_mul_generator`, `ec_mul`, `from_coordinates`, `into_coordinates` |

The upstream inventory also records seven deprecated instructions. Noctium targets the active instruction set for new contracts.

`into_bytes32`, `from_bytes32`, `reverse_bytes`, `bytes32_into_low_high`, `bytes32_from_low_high`, `div_mod_power_of_two`, `reconstitute_field`

### Compact backend source audit

The pinned Compact 0.36.1 lowering pass contains constructors for 31 of the 40 active names and writes ZKIR 3.1. This count describes the selected backend source. Equivalent operations often lower to different instruction sequences. For example, a Compact ledger toggle compiles Boolean negation into `cond_select`. [Compact lowering pass](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/compiler/zkir-v3-passes/reduce-to-zkir.ss) · [Compact JSON printer](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/compiler/zkir-v3-passes/print-zkir-v3.ss)

The printer recognizes `not` and `slice` without a constructor in the lowering pass. The printer omits `and`, `or`, `xor`, `concat`, `nth`, `reverse` and `load_constant`. These findings describe direct opcode emission. Source-level equivalence needs contracts that exercise the same behavior on both compilers.

The OpenZeppelin ports are one workload. The benchmark pairs entrypoints by name and reports timings and circuit size. The ports use different interfaces and state paths. [OpenZeppelin benchmark and limitations](../development/oz-compile-performance.md)

## Full pinned ZKIR v3 type inventory

Noctium uses all 15 native type families in scoped source or lowering paths. Bool, Byte and Bytes also appear as derived encodings or internal intermediates. [Type and overload evidence](zkir-feature-matrix.json)

| Family | Native types |
| --- | --- |
| Scalars and bytes | `Native`, `Bool`, `Byte`, `Bytes` |
| Jubjub | `JubjubScalar`, `JubjubPoint` |
| Secp256k1 | `Secp256k1Base`, `Secp256k1Scalar`, `Secp256k1Point` |
| Secp256r1 | `Secp256r1Base`, `Secp256r1Scalar`, `Secp256r1Point` |
| Curve25519 | `Curve25519Base`, `Curve25519Scalar`, `Curve25519Point` |
