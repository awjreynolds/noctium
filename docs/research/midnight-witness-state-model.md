# Midnight ledger 9 witness, proof, and state boundaries

Context pointer: [ticket 12, Map ledger 9 witness, proof, and state boundaries](https://github.com/awjreynolds/noctium/issues/12)

Research checked on 2026-11-16 against official Midnight documentation and repositories.

## Compatibility profile recorded on 2026-11-16

The compatibility matrix checked on 2026-11-16 listed ledger 9.1.0.1, node 2.1.101, proof server 9.0.0, Midnight.js 5.0.0, and Compact toolchain 0.36.0 for Mainnet and Preview. The ledger 9.1.0.0 release notes identify `midnight-circuits` 7.3.0 and `midnight-zk-stdlib` 2.4.0. Proof Server 9.0.0 supports ZKIR v3 through `midnight-zkir` 3.2.0. The [updated baseline](compact-equivalence-baseline.md) records the 2026-11-17 client patch. [Current compatibility matrix](https://docs.midnight.network/relnotes/support-matrix) [Ledger 9 upgrade](https://docs.midnight.network/relnotes/ledger-9) [Ledger 9.1.0.1 release](https://github.com/midnightntwrk/midnight-ledger/releases/tag/ledger-9.1.0.1) [Proof Server 9.0.0 release notes](https://github.com/midnightntwrk/midnight-ledger/releases)

## Observed boundaries

- A witness is an off-chain function that supplies private values for local circuit execution. The proof lets the network verify the circuit relation without receiving those witness values. Midnight's published witness API is currently documented through Compact declarations and TypeScript implementations. The witness receives a local context and may update local private state. Its returned values are untrusted, so the circuit must constrain every property it relies on. [Manage private state with witnesses](https://docs.midnight.network/guides/private-state-witnesses)
- The proof server handles witness material in clear text, so the official deployment guide recommends keeping the server local. The client obtains ZKIR and keys through a ZK config provider, sends proving work to the proof provider, then submits the call through the wallet and node providers. [Deploy and operate a contract](https://docs.midnight.network/guides/deploy-and-operate)
- ZKIR defines a circuit representation and VM. Its CLI compiles circuit files into proving and verifying keys, and its WASM bindings expose checker and prover functions. The repository does not document a complete language-independent contract packaging or deployment API. [midnight-zkir repository](https://github.com/midnightntwrk/midnight-zkir/tree/zkir-v3)
- The documented call flow runs contract logic locally, generates a proof, balances the transaction, then submits it. The ledger validates submitted transactions and applies accepted state changes. Ledger 9 release notes describe versioned proofs and verifier keys, contract-call transcripts, public-input accounting, state write accounting, and strict transcript validation. The deployed verifier key is part of the acceptance boundary. A call using an unavailable key is rejected. [Deploy and operate a contract](https://docs.midnight.network/guides/deploy-and-operate) [Ledger 9.1.0.1 release](https://github.com/midnightntwrk/midnight-ledger/releases/tag/ledger-9.1.0.1)
- The public ledger stores contract state. Private application state stays with the client and changes only after the transaction succeeds. This separation is explicit in the official witness guide and browser DApp guide. [Manage private state with witnesses](https://docs.midnight.network/guides/private-state-witnesses) [Deploying and calling a contract from a browser DApp](https://docs.midnight.network/guides/browser-dapp)

## Recommended Noctium boundary

Keep the circuit relation and contract state transition as separate typed parts of the Lean model. A circuit relation declares typed private witness inputs, public inputs, constrained computations, and public outputs. A contract entrypoint declares the ledger state it reads, the conditions it requires, and the state effects it commits when the proof and transaction pass. A witness provider supplies untrusted off-chain values and any local private-state update. It does not define ledger state or circuit truth.

The compiler-owned IR should represent these concepts independently and compose them at a contract entrypoint. This supports circuits and state operations beyond the first claim workload without taking Compact declarations as normative. The private one-time claim then becomes one program in the model: a secret and Merkle path arrive as witnesses, the root and nullifier participate in the proved statement, and the nullifier state check and insertion happen as one accepted ledger transition.

## Unknowns to resolve in the vertical slice

- Official public documentation does not specify a language-agnostic API for a non-Compact compiler to bind its witness schema, public statement, proof, state transcript, generated bindings, and deployment artifacts.
- The official ZKIR repository documents IR, execution, and key generation. Reviewed sources do not establish that direct ZKIR output alone supplies all contract-call metadata, generated bindings, and deployable artifacts required by Midnight.js.
- The exact relationship between Noctium's public outputs and the ledger call transcript must be tested against the pinned ledger 9.1.0.1 stack. The same test must confirm that proof verification, state reads, nullifier uniqueness, and state writes share one transaction acceptance boundary.
- The proof server is a trusted local service boundary for confidentiality and availability. The contract must still constrain witness values and prove the public statement; successful local witness execution alone does not establish acceptance.

These unknowns belong in the first Lean-to-ZKIR vertical slice and artifact-route decision. They do not justify restricting Noctium's source language to Compact's feature set.
