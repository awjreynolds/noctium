# Native Rust runtime probe

Checked on 2026-11-16 for [Run the private claim in a native Rust runtime without Node](https://github.com/awjreynolds/noctium/issues/30).

The bounded runtime in `runtime/` executes the actual Lean compiler's schema-version-1 plan without invoking Node or loading a JavaScript/WASM package. The compiler remains Lean. This runtime consumes emitted program data through public native Midnight APIs.

## Verified scope

The Rust library evaluates Native and Boolean expressions, canonical field constants, arithmetic, equality, eager selection, and the pinned native Poseidon operation. It validates an exact named input schema, constructs the supported state-cell/empty-map layout, materializes typed Impact operations, runs state checks, applies the official transcript partitioner using actual ledger parameters, constructs a diagnostic checker preimage, and calls the official native ZKIR checker.

Its `prepare` function accepts a plan, input map, initial charged state, ledger parameters, and public contract address. Its returned `Execution` holds typed native operations, guaranteed/fallible transcripts, successor state, and a `ProofPreimage`. `check` executes the upstream relation and checks the per-operation activity count.

The probe CLI additionally loads the earlier accepted fixture's initial and predicted contract state, compares exact serialized bytes, runs its five configured negative cases, and attempts replay against the successor state. The library does not require those golden files. They are conformance inputs for this CLI experiment.

This is not a general witness-provider SDK, C ABI, mobile library, WASM runtime, cryptographic proving implementation, wallet, or transaction sender. It does not generate a proof or submit a transaction. The accepted-ledger evidence used for comparison remains the earlier [source-driven native POC](native-localnet.md).

## Pins and dependency resolution

- Rust toolchain: `1.100.0`, also recorded in `runtime/rust-toolchain.toml`.
- Native ledger/runtime/crypto/serialization/storage source: `a2b30128ca4b660b73a068e29b56b48ede8c9a74`.
- Independent ZKIR 3.2.0 source: `446c7fecc6bd41dab99ebe89ab404e9d077d11a9`.
- `runtime/Cargo.lock` pins the resolved consumer dependency graph.
- Root Cargo patches unify ZKIR's base-crypto, transient-crypto, serialization, and storage-core dependencies to the ledger revision. The native checker therefore receives the same Rust `ProofPreimage` type as the runtime.

The Rust ledger crate labels itself `1.0.1`, while the prior JavaScript distribution is `@midnight-ntwrk/ledger-v9` `1.0.2`. Those labels are not treated as equivalent. Exact fixture bytes and official checking establish the result below. The lockfile intentionally retains older upstream compatibility crates pulled by the ledger. A feature-tree inspection found no `mock-verify` or `test-utilities` feature enabled.

The consumer graph resolved some compatible transitive versions newer than the standalone CLI's original lockfile, including `midnight-proofs` 0.8.3. They are fixed in this crate's lockfile. This probe does not upgrade the compiler target from ZKIR 3.2.0 or qualify a new network profile.

## Results

The accepted fixture came from the actual `examples/PrivateClaim.lean` source and used public development values only. The test run passed:

- Exact initial serialized state equality with the qualified artifact.
- Official native ZKIR checking for the valid claim.
- 21 native VM operations and 21 ZKIR activity groups.
- 5 private inputs, 75 public transcript input fields, and 6 public read outputs.
- 21 guaranteed operations and no fallible operations for this parameter snapshot.
- Exact serialized predicted contract-state equality. SHA-256: `d03deaed2a47e077412acd4db0fb3069e47cd41d05472eebb3c8182f0c938dc3`, matching the earlier finalized ledger state.
- Rejection of wrong secret, sibling path, direction, root, and nullifier by native checking.
- Replay rejection against the successor state and unchanged state on failure.

The Rust binary also passed with an empty inherited environment and only `/usr/bin:/bin` on PATH. Its executable contains no subprocess invocation; the only `std::process` use is its exit status.

A separate one-off reference check invoked the existing JavaScript helper outside the Rust process and serialized the same diagnostic preimage. `cmp` found its 962-byte output byte-for-byte identical to Rust's tagged `ProofPreimage`. This covers the complete selected fixture's canonical witness ordering, op-field encoding, read results, key location, and diagnostic commitment/binding context. It is a golden-reference experiment, not a Node dependency of the runtime.

Eight focused Rust tests cover canonical field boundaries, field arithmetic, eager selection and type failures, exact input-schema validation, unknown expression rejection, the official Poseidon vector, and explicit rejection of unqualified state features. They passed with the locked graph.

## Run

Build using the pinned toolchain and locked consumer graph:

```sh
cargo +1.100.0 test --manifest-path runtime/Cargo.toml --locked
cargo +1.100.0 run --manifest-path runtime/Cargo.toml --locked -- /path/to/qualified/native/artifacts
```

The artifact directory used by the probe contains `source-plan.json`, `runtime-config.json`, `ledger.params`, `native-contract.json`, `initial-state.bin`, `predicted-state.bin`, and `zkir/<entrypoint>.zkir`. The existing [native workflow](native-contract.md) explains their provenance. It currently uses JavaScript for its orchestration; this experiment replaces the runtime execution and checker portion, not all build and deployment tooling.

The verified isolated toolchain command was:

```sh
RUSTUP_HOME=/private/tmp/noctium-rustup \
CARGO_HOME=/private/tmp/noctium-cargo \
CARGO_TARGET_DIR=/private/tmp/noctium-rust-runtime-target \
/private/tmp/noctium-cargo/bin/cargo +1.100.0 run \
  --manifest-path runtime/Cargo.toml --locked -- \
  /private/tmp/noctium-native-actual-source/final-artifacts
```

An optional `--write-checker-preimage PRIVATE_FILE` writes the diagnostic preimage to a new file with mode 0600 on Unix. The file contains witness values and stays outside the public artifact bundle. The CLI refuses overwriting an existing file and does not print witnesses or their raw serialization.

## Remaining boundaries

The probe implements the current initial Native/Bool and cell/map slice. It explicitly rejects state reads after a write, nonempty initial maps, unsupported operation shapes, and unsupported schema versions. Ordered state effects beyond the claim need expanded evaluation and conformance coverage rather than a support claim.

Compiler bundle hashes and ABI compatibility are not yet verified by the runtime. The CLI uses trusted source-generated artifacts for this experiment. A production loader must bind the plan, circuit, keys, profile, and canonical schema in a verified manifest.

Communication randomness and binding input are zero in this diagnostic checker context, matching the existing checker helper. Real transactions require fresh communication randomness and their actual binding input. No diagnostic proof or preimage is suitable for attachment to a transaction.

The library takes all private inputs up front. Host callbacks, resumable execution, cancellation, bounded resources, allocator/secret-buffer contracts, stable C bindings, Kotlin/Swift packaging, optional WASM builds, in-process proving, and new Rust-constructed ledger transactions remain separate qualification work. Native values and host input strings also create copies beyond the upstream preimage's zeroization-on-drop protection.

## Block time with authenticated current state

`ContractOperationTarget::prepare_call_in_block` takes the existing
authenticated current-state token and an explicit prospective Ledger
`BlockContext`. The proof binds the checked predicate and the ledger
rechecks the predicate on execution. An active call without a block context
rejects during preparation and leaves the current-state token available.

The `checkTime` fixture finalized at block 49886 with its exact state
unchanged after deployment at 49883. [Finalized receipt](native-block-time-current-state-receipt.json)
