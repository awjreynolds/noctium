# Guarded typed witnesses

Typed witnesses inside structured branches use native binding schema 2. Each static call row carries a closed Boolean `guard`, its source call path and site, and its exact result slots. The control-plan format stays at version 2. Straight-line witness bindings retain schema 1.

The Rust Session evaluates call guards in static order. An active row must match the next source-executed provider call. An inactive row receives canonical slot defaults and makes no provider request. A missing active call, an unexpected call or an unavailable guard reference rejects execution. Completion processes trailing inactive rows before exporting the native input map.

This matters when a helper continues after a branch. Native lowering duplicates the continuation under the two branch guards. Both copies have distinct static ordinals and result slots. Only the selected copy invokes the provider. A witness used to decide a branch runs under the enclosing guard, before its result controls the branch calls.

## Slot values and disclosure

Inactive Native and unsigned slots use zero. Bool uses false. Bytes use zero-filled buffers of the declared length. JubjubScalar uses zero, and JubjubPoint uses the identity `(0,1)`. Foreign fields use zero and foreign points use their canonical identity. Checked aggregate results bind Native leaves, with zero defaults. Unit and empty aggregate calls still have call rows even though they have no result slots.

Native constraints enforce inactive defaults independently of the branch's ordinary constraints. Runtime zero filling alone would leave a malicious prover free to change unused private inputs. Provider results on active paths remain untrusted values subject to the contract's constraints.

Private values used to control public observations still require explicit disclosure. A private-state stage executes in its selected host branch. The circuit retains the corresponding computation, but does not prove persistence of the host's journal or private store. Provider callbacks and host timing remain visible to the host.

## Authoring and scope

The [Source fixture](../../tests/GuardedWitness.lean) uses `noctium_witness_circuit` and an ordinary contract entrypoint. Its flag provider selects an amount provider and a unit or empty-result provider. A shared tail call follows the branch. Each selected branch stages a private value, and the contract stores the checked public result.

Each readable conditional arm has its own scope. A branch-local `let` or
destructuring pattern may reuse an outer name. Its right-hand side resolves
before the new binding enters scope. The continuation sees the original
binding, and a duplicate name in one block fails elaboration.
[Branch shadowing fixture](../../tests/ReadableLazyConditional.lean)

Use `Witness.compile` for declared typed providers. Ordinary `Helpers.compile` retains its conservative guarded-witness gate. Untyped private witness placeholders do not acquire provider bindings through this format. Host-only `noctium_control` plans keep their separate qualification boundary.

The separate [structured state entry](structured-cells.md) route supports native cell and map statements inside helper bodies. A [nested scalar fixture](structured-cells.md#nested-hosted-branches-on-ledger-9) combines provider scheduling and private staging with native proving and finalized state checks. Broader ledger effects and compiler preservation have separate evidence requirements. [Guarded witness binding](https://github.com/awjreynolds/noctium/issues/84) · [Compiler preservation](https://github.com/awjreynolds/noctium/issues/21)

## Evidence boundary

The [focused Rust case](../../runtime/tests/guarded_witness.rs) drives both provider outcomes through a real Session and Source-generated native artifacts. It checks callback order, skipped calls, private staging, completed slot values, public results and exact state. An altered inactive raw witness slot must reject at the pinned checker. Guard metadata receives targeted rejection cases.

Existing straight-line schema-1 artifacts supply byte-comparison checks. These checks do not establish general lowering correctness, provider honesty or private-store persistence. No new keys, proofs, deployments, K benchmark or mobile/WASM qualification accompany this prerequisite slice. The existing witness semantic model does not qualify the new guarded binding format.

The 73-job compiler/Claim build and Source export pass. The end-to-end and malformed-guard cases pass in 0.01 seconds. The legacy unit/empty-call runtime case also passes, and 20 existing artifacts remain byte-identical. The new relation contains 48 instructions, seven static calls and five private witness fields. The binding occupies 9,060 bytes. These are structural counts, not proving-time measurements.
