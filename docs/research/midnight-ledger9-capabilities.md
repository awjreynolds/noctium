# Midnight ledger 9 capability inventory

Context pointer: [ticket 13, Inventory ledger 9 circuit and contract capabilities](https://github.com/awjreynolds/noctium/issues/13)

Research checked on 2026-11-16 against the official Midnight documentation and repositories cited below. This is a bounded inventory of public interfaces reviewed so far, not a complete opcode or contract-feature catalogue.

## Compatibility profile recorded on 2026-11-16

The compatibility matrix checked on 2026-11-16 listed ledger 9.1.0.1, node 2.1.101, proof server 9.0.0, Midnight.js 5.0.0, Compact toolchain 0.36.0, language 0.28.0, Compact runtime 0.21.0, and on-chain runtime 4.0.0. The [updated baseline](compact-equivalence-baseline.md) records the 2026-11-17 client patch. [Current compatibility matrix](https://docs.midnight.network/relnotes/support-matrix) [Ledger 9 compatibility notes](https://docs.midnight.network/relnotes/ledger-9) [Ledger 9.1.0.1 release](https://github.com/midnightntwrk/midnight-ledger/releases/tag/ledger-9.1.0.1)

At the circuit boundary, ledger 9 documents ZKIR 3.2.0. Compact 0.36 emits ZKIR 3.1 and bundles a `zkir-v3` binary from `midnight-zkir` 3.2.0-rc.2. Treat these as separate producer and target identifiers until an exact emitted artifact passes the ledger's checks. [Ledger 9.1.0.1 release](https://github.com/midnightntwrk/midnight-ledger/releases/tag/ledger-9.1.0.1) [Compact 0.36 release notes](https://docs.midnight.network/relnotes/compact/toolchain-0.36.0)

## Observed capabilities by layer

| Layer | Publicly documented evidence | Boundary or gap |
| --- | --- | --- |
| Circuit representation and execution | `midnight-zkir` publishes the ZKIR format, a VM, and a CLI. `zkir compile` and `compile-many` accept ZKIR circuit files and produce proving and verifying keys. Its WASM bindings expose checker and prover functions. [midnight-zkir](https://github.com/midnightntwrk/midnight-zkir) | The reviewed sources do not provide a complete, versioned catalogue of ZKIR v3 operations or establish which operations are accepted by each ledger 9 verifier profile. |
| Circuit and proving libraries | Ledger 9.1.0.1 release materials pin `midnight-circuits` 7.3.0 and `midnight-zk-stdlib` 2.4.0. Ledger 9 release notes also identify new cryptographic primitives. [Ledger 9.1.0.1 release](https://github.com/midnightntwrk/midnight-ledger/releases/tag/ledger-9.1.0.1) [Ledger 9 upgrade notes](https://docs.midnight.network/relnotes/ledger-9) | The reviewed documentation does not classify the complete primitive set by proving interface, ledger availability, or Compact exposure. The package pins alone do not prove a primitive is deployable from a non-Compact frontend. |
| Witness and local proof construction | The published witness flow uses off-chain witness functions to provide private values for local execution. Witness results are untrusted and must be constrained by the circuit. The client uses ZK config and proof providers to load circuits and keys and construct a proof. [Private state and witnesses](https://docs.midnight.network/guides/private-state-witnesses) [Deploy and operate](https://docs.midnight.network/guides/deploy-and-operate) | The documented witness API is expressed through Compact declarations and TypeScript implementations. The proof server sees witness material in clear text, so the official guide recommends running it locally. No reviewed language-independent witness schema API was found. |
| Contract execution and state | Ledger 9 uses Impact VM with on-chain runtime 4.0.0. Ledger 9 notes list contract-to-contract calls, event emission, and new cryptographic primitives among capabilities usable by Compact contracts. [Midnight.js architecture](https://github.com/midnightntwrk/midnight-js#architecture) [Ledger 9 upgrade notes](https://docs.midnight.network/relnotes/ledger-9) | These release notes establish features in the documented Compact path. They do not establish that Compact defines the full lower-level capability set or that a direct Noctium artifact path exists for each feature. |
| Transaction verification and state acceptance | The ledger 9.1.0.1 release notes describe versioned proofs and verifier keys, call transcripts, public-input accounting, state-write accounting, and strict transcript validation. The deployed verifier key participates in transaction acceptance. [Ledger 9.1.0.1 release](https://github.com/midnightntwrk/midnight-ledger/releases/tag/ledger-9.1.0.1) | A Noctium proof's public outputs and state effects must be bound to the accepted call transcript. The exact language-independent binding and atomic state/nullifier behavior need a ledger-backed vertical-slice check. |
| Build, package, and deployment | The documented Compact compiler route emits ZKIR, proving and verifying keys, generated JavaScript and TypeScript contract bindings, and compiler metadata. Midnight.js deployment consumes the generated module and compile artifacts. [Build a private smart contract](https://docs.midnight.network/guides/build-a-private-smart-contract) [Deploy and operate](https://docs.midnight.network/guides/deploy-and-operate) | The ZKIR repository documents compiling circuits into keys, but reviewed sources do not document a complete direct-ZKIR contract package with bindings and deployment metadata. |

## Capabilities outside Compact

The reviewed evidence shows lower-level ZKIR, VM, key-generation, checker, and prover components as public projects and interfaces. It does not provide a reliable list of capabilities that are ledger-supported yet absent from Compact's source surface. That distinction needs source-level inventory and compatibility checks before Noctium promises any specific feature beyond Compact.

Do not infer that Compact defines the whole ledger feature set from the completeness of its documented build and deployment route. Also do not infer that a low-level library operation is a supported contract capability from its presence in source. Record both facts separately for each proposed Noctium feature: the ledger/proving interface that supports it, and the tested path that packages, proves, and executes it.

## Recommendation for Noctium

Implement a Lean-owned target profile that pins ledger, ZKIR, proving-library, proof-server, and on-chain runtime versions independently. Model circuit relations, witness/public input boundaries, circuit outputs, contract state effects, and transaction bindings as separate typed components. Compose them at a contract entrypoint. Keep target capabilities extensible and profile-specific so later ledger-backed operations do not require changing a claim-only IR or adopting Compact's syntax and semantics.

Treat a capability as supported only after a pinned profile demonstrates its complete required path through compilation, proof generation and verification, contract artifact assembly, and transaction acceptance. The private one-time claim qualifies the v1 path; it does not define the complete future capability inventory.

## Unresolved questions

- What is the complete ZKIR v3 operation set accepted by the current ledger 9 verifier, and which interface promises compatibility?
- Which ledger 9 circuit and proving primitives are available outside Compact, and through which stable public APIs?
- How do a non-Compact compiler's witness schema, public outputs, proof, call transcript, and state writes bind atomically at ledger acceptance?
- Which direct-ZKIR artifacts and metadata does Midnight.js require beyond the proving and verifying keys?
- Which capabilities have a complete Preview-tested route today, rather than only a library implementation or release-note description?

These questions should guide capability additions after the first vertical slice. Compact remains one integration route and evidence source, not Noctium's semantic or feature boundary.
