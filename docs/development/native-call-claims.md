# Native call-claim references

The direct contract entrypoint path supports Midnight's call-claim operation:

```lean
claimContractCall(target, entryHash, disclose(commitment))
```

`target` and `entryHash` have type Bytes32. `commitment` is a Native field.
The operation records a reference to another call. It does not execute a remote
witness provider or construct a complete transaction. The ledger generates the
claim's sequence number from its current claim set.

Lean emits one checked Impact operation with nine activity groups. Rust expands
the pinned ledger's `kernel_claim_contract_call!` macro. The same guard applies to
all nine VM operations. The operation targets the kernel effects map, not a
contract state field. Address, entrypoint hash, commitment and private control
dependencies require explicit authorized disclosure before reaching this sink.

## Binding input and output

Midnight's communication commitment hashes the opening followed by the flattened
call input and output fields. The scalar example uses the existing Native hash:

```lean
disclose(transientHashNativeVector([
  opening, argument, expectedBalance,
  cast(Native, expectedCount), cast(Native, expectedEnabled)]))
```

These fields match `NativeReturns.advance`: one committed Native argument and
Native balance, UInt64 count and Bool return values. The entrypoint hash comes
from the official `EntryPointBuf.ep_hash()` domain. The commitment does not bind
alignment metadata or a type schema, so callers must also select and validate the
callee's interface. Passing a field reference alone does not establish this
payload binding.

### Check the call payload against a declared interface

Use `callCommitment` to let Lean read an earlier contract declaration's
committed argument and return types. The [typed caller](../../tests/TypedCallArguments.lean)
binds a Bool, Bytes33, UInt, Jubjub values, a Secp256k1 field and Bytes0:

```lean
claimContractCall(target, entryHash,
  disclose(callCommitment(TypedCallArguments, "store", opening,
    [flag, payload, score, point, scalar, field, empty],
    [expectedTail, expectedScore, expectedApproval])))
```

Lean checks both lists in interface order and emits the same native field
encoding as the callee. Each expression evaluates once, including Bytes0
expressions that can fail without contributing a field. The opening and
payload retain their privacy until the caller explicitly authorizes release.
The SDK matches the claimed address and entrypoint hash to the actual callee.
The compile-time contract name selects a schema.

The native test assembles both source-generated calls and rejects an altered
expected result. Source checks reject a mismatched type or argument count.
The checked expression supports scalar and fixed-byte arguments and results.
For a named aggregate result, supply its label and the fields in the checked
layout order. Scalar results stay positional among the scalar returns.

```lean
claimContractCall(target,
  disclose(callCommitment(Codec, "inspectPayment", opening, [],
    [payment := fields(amount, approved, false, true, 1,
      byteAt(expectedMemo, 0), byteAt(expectedMemo, 1)),
     approved, expectedMemo, flags := fields(false, true)])))
```

The compiler matches each label once against the declared callee. It checks
the field count and the Native, Bool, UInt, byte and enum-tag leaf types.
Enum payload slots use their canonical Native representation. The compiled
call evaluates and commits the values in the callee's physical return order,
including when aggregate groups appear elsewhere in the source list.
An empty aggregate still needs its label and contributes zero fields.

The native test assembles a caller and callee with two aggregate results, a Bool
and fixed bytes. Changing the amount from 300 to 299 produces a checked caller
whose claim fails to match the callee. Bundle selection still needs a trusted
manifest and the deployed verifier. The ledger commitment authenticates the
result fields, with schema selection supplied by the source interface and trusted
callee bundle. Helper-body call authoring remains open.
[Payment example](../../examples/AggregateSerialization.lean) · [Native test](../../runtime/tests/aggregate_serialization.rs)

The funded payment example attached two K9 proofs and finalized in one
localnet transaction at block 31967. The Rust client checked one call event
per address and matched both finalized states to their exact deployment
bytes. Two compiles reproduced all 27 selected files. [Aggregate composition receipt](native-aggregate-composition-receipt.json)

### Share a named call interface

A named interface lists the argument and return layouts for provable contract
entrypoints. Declare each implementation before using the interface at a call.

```lean
noctium_interface BalanceUpdate where
  entry store accepts [amount : UInt 8] yields [stored : UInt 8]
end

noctium_implements BalanceContract implements BalanceUpdate
```

Pass the implementing contract and interface to the qualified commitment form.

```lean
claimContractCall(target,
  disclose(callCommitment(BalanceContract, BalanceUpdate, "store", opening,
    [proposedAmount], [expectedStored])))
```

The compiler checks entry names, field order, scalar types and aggregate
grouping. Source labels belong to each declaration. A caller uses the
interface's labels for grouped arguments and results. The contract
implementation uses its own labels. The qualified form uses the existing
native commitment and the declared operation's selector. It still requires the
call commitment to cross the normal disclosure check.

The [payment example](../../examples/AggregateSerialization.lean) uses a named
interface for two grouped returns and two scalar returns. The native test
assembles the compiled caller and callee and rejects a changed result. The
[Compact oracle](../../tests/compact/NamedInterface.compact) checks
matching declarations and incompatible signatures against the pinned compiler.
Run `python3 tests/compact/contract-interfaces.py /path/to/compactc` with
Compact 0.36.1.
[Compact contract types](https://docs.midnight.network/compact/reference/compact-reference#contract-types)

The qualified payment caller and callee emitted byte-identical ZKIR and
Impact plans to the direct-call version. Both proofs finalized in one
Ledger 9 localnet transaction at height 10. The native client matched
both finalized state byte strings to their expected values.
[Named-interface composition receipt](named-interface-composition-receipt.json)

The [stateful pair fixture](../../tests/ContractInterfaceComposition.lean)
passed a grouped `UInt 8` and `Bool` through a named interface. The caller read
the callee address from a ledger cell. One localnet transaction finalized both
proofs and advanced both counters from zero to one. The native assembly step
rejected a caller that expected amount `8` from a callee returning `7`.
The receipt uses the ZKIR 3.2.1 target with `--emit ledger --emit witness`
and `--dedup-range-checks`.
[Stateful composition receipt](named-interface-stateful-composition-receipt.json)

With Compact 0.36.1 and runtime 0.21.0, the grouped `readPair` comparator
returned `[7n, true]` and stored `saved = 7n` in memory. This checks the grouped
argument and return behavior. The Noctium receipt covers atomic state updates
across two deployed contracts.

### Route a call through a typed contract reference

Use `ContractRef BalanceUpdate` for a circuit input, scalar Cell, root scalar
List element, or field of a named record stored in a root Cell or List. The
compiler retains the declared interface when reading a Cell or taking a List
head. Each address uses the existing Bytes32 encoding.

```lean
read route as target
claimContractCall(target,
  disclose(callCommitment("store", opening, [proposedAmount], [expectedStored])))
```

The target's interface supplies the method selector and ordered argument and
result types. A private target still needs an explicit `disclose(target)`.
Native call assembly checks the selected address, operation, and committed
argument and return values against the supplied callee relation.

For a record field named `target`, `read route as stored` binds
`stored_target` with its declared interface. A record write or List push
checks every typed field against the destination's interface.

The [typed reference fixture](../../tests/TypedContractReference.lean) and
[Compact comparison](../../tests/compact/typed-contract-reference.mjs) exercise
scalar and record Cell and List routing. The same fixtures cover an
`echo` method that accepts and returns a `ContractRef`. Noctium checks the
declared interface on both sides of the call while the native ABI carries
the usual 32-byte address. An implementation with a raw or wrong-interface
argument or result fails the interface check. The typed caller also checks
its supplied arguments and expected results before lowering. Native call
assembly matches the returned address and rejects a substituted argument
or expected result.

Nested record storage and deployed dynamic interface lookup remain open
under [typed contract references](https://github.com/awjreynolds/noctium/issues/828).

### Bind the entrypoint and read the address from a registry

The two-argument form derives the entrypoint selector from the same declared
operation used to check the commitment. The [typed caller source](../../tests/TypedCallArguments.lean)
reads a public `Bytes32` registry cell before claiming the call.

```lean
read route as target
claimContractCall(target,
  disclose(callCommitment(TypedCallArguments, "store", opening,
    [flag, payload, score, point, scalar, field, empty],
    [expectedTail, expectedScore, expectedApproval])))
```

Lean hashes the public operation name during compilation using Midnight's
domain and emits a literal selector. The runtime checks the address from the
current registry cell, the selector and the call commitment together. The
native case checks the selector against `EntryPointBuf::ep_hash`, runs a
secret-authorized registry rotation, assembles a call to the second deployment
address and rejects the stale address and a wrong operation. [Midnight selector implementation](https://github.com/midnightntwrk/midnight-ledger/blob/a2b30128ca4b660b73a068e29b56b48ede8c9a74/onchain-state/src/state.rs#L912-L918) · [SHA-256 standard](https://csrc.nist.gov/pubs/fips/180-4/upd1/final)

On localnet, the first routed call finalized at block 28361, the registry
update at 28364, and the second routed call at 28367. The caller used one
deployment throughout. Each composed transaction updated its selected callee's
`stored` cell to 200. The native proof SDK checked each selected bundle against
the verifier installed at its address and operation. A wrong selector, a
wrong callee bundle and the stale address all rejected before proving.
[Registry qualification receipt](native-registry-receipt.json)

### Require the immediate contract caller

Read an address from public state and require the ledger to authenticate it as
the immediate parent of this call. The [protected callee](../../tests/ContractCaller.lean)
uses this guard before changing its balance.

```lean
read permitted as parent
requireContractCaller(parent)
```

Lean binds the tagged contract address to the Impact transcript. The ledger
derives the caller from the matching parent call. A user address with the
same bytes still fails the contract variant check. Conditional checks use
`when` and the existing disclosure analysis for both the address and the guard.
[Ledger caller semantics](https://docs.midnight.network/relnotes/compact/toolchain-0.35.0#the-caller-of-a-circuit-is-available-to-the-circuit)

Rust applications prepare direct entrypoints with `prepare_with_context` and
the prospective parent address. `assemble_checked_calls` compares it with the
actual parent in the assembled call forest before proving. A root call and a
different parent fail this check. This path authenticates the parent address.
The pinned ledger does not supply a parent operation name to the callee.

The funded case attached two K8 proofs and finalized at localnet block 28533.
The node replayed the guard against the actual parent before the callee balance
moved from 10 to 13. In-process checks reject a missing caller, a user address
with identical bytes, and a host-supplied parent that differs from the call
forest. The inactive guard skips all three Impact operation groups and the five
caller value fields. [Caller qualification receipt](native-caller-receipt.json)

## Assemble a native call forest

The Rust SDK takes prepared calls in ledger execution order through
`assembly::assemble_checked_calls`. Each call has a circuit, an initial
`QueryContext`, an entrypoint and a fresh private communication opening. The
helper replays each program from its supplied context and checks the resulting
state and effects. It uses Midnight's partitioner to split guaranteed and
fallible operations across the forest.

Every recorded claim must match a later call's address, entrypoint hash and
communication commitment. Commitments must be distinct, and each callee has
at most one incoming claim. The ledger's sequencing check enforces sibling
order and transcript causality. The intent carries both transcript sections
and the private proof preimages. The helper checks each reconstructed preimage
and activity schedule against its circuit. Key locations use
`<hex-address>:<entrypoint>` so equally named operations at different
addresses have separate resolver entries.

The focused case assembles `NativeCallClaims.claim`, its claimed
`NativeReturns.advance` callee and an independent call to another address
in one intent. It checks the ordered calls and the committed Native argument.
Missing, reversed and wrong targets, duplicate commitments and preloaded
effects reject. When the claim guard is false, the caller assembles by itself.
Source guards reject private addresses, hashes, commitments and control without
release.

The result is a private, unbalanced intent. Applications supply the initial
contexts. [Committed scalar and fixed byte arguments](committed-returns.md#native-call-arguments)
use the native input ABI, including private source parameters from readable
hosted witness circuits. Checked aggregate parameters from structured witness
sources also use the ABI. The caller names the argument group and supplies each
leaf in layout order. The callee binds the group to its typed provider input.
Automatic bundle discovery and claim statements inside helper bodies remain
open. The reference state interpreter rejects active call claims.

The hosted pair-argument fixture finalized at localnet block 32173 with two
K8 proofs. Its provider received the typed record and returned a private reply.
The node accepted both calls and the callee's `total` moved from 1 to 14. The
host's staged write stayed in the test invocation. Two builds reproduced all
15 selected compiler files. [Aggregate argument receipt](native-aggregate-argument-receipt.json)

## Prove a composed intent

`proof::PreparedComposition::from_intent` freezes the assembled intent.
Pass a host-authenticated ledger snapshot and a `CompositionMaterial` for
each call in intent order. Each selection contains its authenticated public
bundle and trusted proof parameters. The SDK compares the bundle's ledger
parameters with the snapshot, allowing the fee prices to change per block.
The bundle's verifier key must match the operation installed at the call's
address and entrypoint. These checks precede proof requests.

`prove_locally` uses host-provided entropy. `prove` accepts a host-authorized
proof service. Each proof binds its own call statement and the shared intent
commitment. The SDK verifies every response, attaches the native V3 proofs
and verifies the attached statements again before returning a proved intent.

The focused case generated keys from fresh Lean exports and attached k=9 and
k=8 proofs to one intent. A snapshot with the caller's key installed for the
callee rejected before proving. The sealed transaction passed the pinned
ledger's in-process verification with fee balancing disabled.

To reproduce, compile [the caller](../../tests/NativeCallClaims.lean) and
[the callee](../../tests/NativeReturns.lean) with the ZKIR 3.2.1 target.
Generate keys with the pinned [native ZKIR tool](native-toolchain.md).
Assemble the two [public bundles](portable-artifacts.md) as `caller-bundle`
and `callee-bundle`, selecting `claim` and `advance` respectively, with
identical ledger parameters. Set `NOCTIUM_COMPOSITION_BUNDLES` to their
absolute parent path. Supply the independently trusted manifest digests as
`NOCTIUM_COMPOSITION_CALLER_SHA256` and `NOCTIUM_COMPOSITION_CALLEE_SHA256`.
Set `NOCTIUM_COMPOSITION_SRS` to the public SRS directory and provide the
k9 and k8 digests as `NOCTIUM_COMPOSITION_CALLER_SRS_SHA256` and
`NOCTIUM_COMPOSITION_CALLEE_SRS_SHA256`.

```sh
cargo test --manifest-path runtime/Cargo.toml --locked \
  --no-default-features --features zkir-321 --test native_composition -- --include-ignored
```

## Prove calls with separate witness owners

Each owner prepares its own `CheckedNativeCall` and shares a
`composition_offer`. Offers contain the public VM program, its context,
the operation identity, the communication commitment and the unmerged activity
schedule. The checked inputs, private transcript and communication opening
stay with the owner. The caller in the example needs the callee's commitment
to claim the call. The example publishes the balance change, which reveals the
amount. Each credential preimage stays local. [Lean fixture](../../tests/IndependentComposition.lean)

Each owner sends `CompositionOffer::public_bytes()` through the application's
authenticated channel. The coordinator decodes the offers, then calls
`IndependentComposition::freeze` with their agreed order, a trusted snapshot,
expiry and fresh entropy. The SDK partitions and sequences the calls and
retains the Pedersen opening with the coordinator.

The coordinator sends `CompositionDraft::public_bytes()` to both owners. Each
decodes the draft against its trusted snapshot, rebuilds the partitioned calls,
and checks their digest before approving the call order, binding commitment and
expiry. `prove_call` matches the owner's local execution to its offer and checks
the installed verifier against the authenticated bundle. The coordinator takes
the detached proof bytes and `attach` verifies each proof for its frozen slot.

Ledger proofs bind their individual call statements to the shared Pedersen
commitment. Whole-draft agreement, including expiry and order, belongs to
the host and this SDK workflow. The coordinator and peers see the offered
public execution details. The versioned native encoding has a 4 MiB limit per
offer, a 16 MiB total draft limit and a maximum of 64 calls per draft. Imports
check the profile, canonical encoding, entrypoint and transcript bounds. The
draft also checks the network ID and that the rebuilt public calls match its
digest. Hosts supply authentication, expiry policy and the trusted ledger
snapshot.

The K9 caller and K7 callee finalized together at block 30432. The node
confirmed both call events in the same extrinsic and the exact resulting
states. The callee balance moved from 10 to 13. The SDK rejected a missing
callee, an owner proving the wrong slot, and both proofs replayed under
a different intent commitment. This first qualification used two owner values
in one process. [Separate-owner receipt](independent-composition-receipt.json)

The next run used two Rust processes. Each generated its credential preimage
and communication opening locally, fetched its own finalized contract state
and verified the installed key. The coordinator exchanged a 1,840-byte public
draft and accepted two 3,852-byte proofs. Both calls finalized in one extrinsic
at block 30556, with the callee balance at 13 and count at 1. The checks rejected
an altered draft digest, a wrong owner slot and replay under a different intent
commitment. [Cross-process receipt](composition-transport-receipt.json)

The archived block 30432 also has a focused offline proof replay. Supply the
pinned extrinsic as `extrinsic.scale`, the caller and callee tagged contract
states at that block as `caller.state` and `callee.state`, and the public K9
and K7 SRS as `bls_midnight_2p9` and `bls_midnight_2p7`. The replay checks their
receipt digests, reconstructs both public statements from the sealed
transaction, and verifies both V3 proofs with the installed keys. Changes to
the statement, proof order or verifier key reject. SRS substitutions reject at
the digest and degree check because the universal verifier powers are shared.

The key identity checks also require the requested operation to exist and bind
lookup to the exact retained state bytes. The test rejects a missing entrypoint
and a state with an added operation, even though the original `claim` verifier
key remains present.

```sh
NOCTIUM_ARCHIVED_COMPOSITION_DIR=/path/to/block-30432 \
  cargo test --manifest-path runtime/Cargo.toml --locked --offline --no-default-features \
  --features localnet,zkir-321 --test archived_composition_proofs -- \
  retained_composition_proofs_verify_against_their_installed_keys_and_historical_srs --ignored --exact
```

The archived verifier keys also regenerate from the receipt-pinned ZKIR and
SRS. Use the native 3.2.1 `zkir` binary with SHA-256
`7396c9a368e70fb66cb91f39d1508c9f983cacc8d3bc27f7a94e12d9fe327c40`.
Set `MIDNIGHT_PP` to the parameter directory for each operation during key
generation. The caller uses K9 and the callee uses K7.

```sh
mkdir -p "$KEYS/caller" "$KEYS/callee"
MIDNIGHT_PP="$CALLER_SRS_DIR" zkir compile "$CIRCUITS/IndependentCaller.claim.zkir" \
  "$KEYS/caller/IndependentCaller.claim.prover" "$KEYS/caller/IndependentCaller.claim.verifier"
MIDNIGHT_PP="$CALLEE_SRS_DIR" zkir compile "$CIRCUITS/IndependentCallee.advance.zkir" \
  "$KEYS/callee/IndependentCallee.advance.prover" "$KEYS/callee/IndependentCallee.advance.verifier"
```

Set `NOCTIUM_ARCHIVED_REGENERATED_KEYS_DIR` to `$KEYS` when running the replay
test above. Each regenerated verifier was 1,353 bytes and matched the exact
tagged key installed for its operation. Both crossed key comparisons failed.
[Receipt pins](independent-composition-receipt.json)

To run the funded case, compile and bundle `IndependentCaller.claim` at K9 and
`IndependentCallee.advance` at K7 from the fixture. Name the public bundles
`caller-bundle` and `callee-bundle`. Set the same manifest, SRS and node
variables described above and below. Run this one test on the isolated
development chain.

```sh
cargo +1.100.0 test --manifest-path runtime/Cargo.toml --locked \
  --no-default-features --features zkir-321,localnet --test native_composition \
  independent_processes_compose_on_localnet -- --ignored --nocapture
```

### Prove a callee through the C ABI

The [native header](../../runtime/include/noctium_native.h) exposes the owner
side of this protocol. Begin with the authenticated bundle and proof
parameters, the address and trusted ledger snapshot, the private input map
and fresh entropy. Read the public offer from a result token. Approve the
coordinator's draft and pass the exact draft bytes, owner slot and fresh
entropy to prove. The runtime rebuilds the draft, checks the owner slot and
installed verifier, and returns a detached proof. Free the owner and both
result tokens. Hosts authenticate their snapshot and approve the full draft.
The Rust coordinator continues to attach the proofs and submit the intent.

Build the C++ callee for the same funded test. Set `LIBDIR` to the directory
holding the Cargo output for this build.

```sh
cargo +1.100.0 build --manifest-path runtime/Cargo.toml --locked \
  --no-default-features --features zkir-321,localnet --lib
c++ -std=c++17 -Wall -Wextra -Werror runtime/tests/native_composition/cpp_owner.cpp \
  -L"$LIBDIR" -lnoctium_runtime -Wl,-rpath,"$LIBDIR" -o "$LIBDIR/cpp-composition-owner"
export NOCTIUM_COMPOSITION_CPP_OWNER="$LIBDIR/cpp-composition-owner"
```

Run `independent_processes_compose_on_localnet` with the same bundle and
network settings. The callee's test worker passes its inputs and finalized
snapshot to the linked C++ process over a private pipe. The coordinator
receives the public offer and detached proof. The caller continues to use
the Rust SDK. Durable composition recovery and foreign coordinator APIs
remain open.

The Rust caller and linked C++ callee finalized together on Ledger 9 at block
113. The callee rejected the wrong slot and an altered draft, then proved its
own slot and rejected a second proof. The caller's state matched its deployment
bytes. The callee's balance moved from 10 to 13 and its count from 0 to 1.
[Finalized receipt and build pins](composition-cpp-localnet-receipt.json)

## Fund and observe on localnet

Pass `ProvedIntent::native()` to `client::BoundTransaction::prepare`.
The native DUST adapter funds the call intent in its own fee segment. The
client verifies the sealed transaction and predicts each affected contract
state from the finalized snapshot. `Node::finalized_receipt` checks the exact
extrinsic, one `TxApplied`, the expected call-event count for each address,
and each predicted state at the inclusion block. The receipt exposes the
first call's state and a map of the other finalized contract states.

The [funded qualification receipt](native-composition-receipt.json) records
both deployments and the composed transaction finalized at block 27627.
The caller's state matched its deployment bytes and the callee's balance
moved from 10 to 13 with count 1. The same extrinsic contained both call
events and one successful ledger outcome. Rust funded, proved, sealed,
submitted and observed the transaction.

The native Rust host controls submission and retries for composed calls.
The single-contract private journal and C/C++ client flow still cover one
operation at a time.

For the funded check, use the two bundles above with ledger parameters
captured from the selected localnet. Use the public development genesis and
a local SRS cache with the pinned DUST artifacts. Set
`NOCTIUM_COMPOSITION_NODE` to the development node's loopback HTTP RPC
endpoint, then run:

```sh
cargo test --manifest-path runtime/Cargo.toml --locked \
  --no-default-features --features zkir-321,localnet --test native_composition \
  composed_intent_finalizes_both_contract_states_on_localnet -- --ignored --nocapture
```

For the registry case, compile `tests/TypedCallArguments.lean` with the same
profile. Build `caller-bundle` for `TypedCaller.claim`, `rotate-bundle` for
`TypedCaller.rotateRoute` and `callee-bundle` for `TypedCallArguments.store`.
Pin each manifest as above, using `NOCTIUM_COMPOSITION_ROTATE_SHA256` for the
rotation bundle. The route and callee use K11, and the rotation uses K8. Pin the
rotation parameters with `NOCTIUM_COMPOSITION_ROTATE_SRS_SHA256`.

```sh
cargo test --manifest-path runtime/Cargo.toml --locked \
  --no-default-features --features zkir-321,localnet --test native_composition \
  registry_rotation_routes_two_finalized_calls_without_redeploying -- --ignored --nocapture
```

For the authenticated-caller case, compile `tests/ContractCaller.lean` with
the same profile. Build `caller-bundle` for `ForwardingCaller.forward` and
`callee-bundle` for `ProtectedCallee.move`. Both use K8. Use the same bundle,
SRS and node environment variables as the two-operation funded check.

```sh
cargo test --manifest-path runtime/Cargo.toml --locked \
  --no-default-features --features zkir-321,localnet --test native_composition \
  composed_call_finalizes_with_a_ledger_authenticated_parent -- --ignored --nocapture
```
