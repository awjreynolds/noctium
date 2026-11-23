# Host capabilities and private-state lifecycle

Status: bounded native runtime protocol implemented for ticket 36. Rust and linked C++ exercise the same scalar-provider, journal and host-CAS cases without Node. General source witness functions, composite values, durable storage adapters and native ledger-receipt validation remain separate work.

## Ownership and trust boundary

The host owns durable storage, network requests, keys, entropy, user interaction and transaction construction/submission. The runtime performs no ambient I/O. Host callbacks do not execute inside a retained native call stack. Source execution still runs the selected native plan and official ZKIR checker.

Private application writes in this protocol are explicit host-policy updates staged through the runtime API. They are not source-generated witness-function effects, circuit constraints, or proved statements about application storage. This package establishes their transport and transaction lifecycle. It does not establish their business correctness.

The host grants operations and key scopes explicitly. The runtime validates operation/version, capability, argument/result schemas, canonical scalar values and request identity. The host remains responsible for enforcing its storage permissions and the truth of persistence, submission, acceptance and CAS reports. The native core does not validate ledger receipts. An `accepted` notification is host evidence.

## Optional ABI-v1 context

Existing sessions without `hostContext` retain their scalar `witness.input` requests and response encoding. An optional begin field enables protocol version 1:

```json
{
  "hostContext": {
    "protocolVersion": 1,
    "namespace": "wallet_A",
    "baseRevision": "r0",
    "attemptId": "64 lowercase hexadecimal characters",
    "capabilities": [{
      "id": "store",
      "namespace": "wallet_A",
      "keyPrefix": "claims/",
      "operations": ["private_state.read.v1", "private_state.stage.v1", "private_state.compare_exchange.v1"]
    }],
    "operations": [{
      "operation": "private_state.read.v1",
      "argumentSchema": {"key": "Key"},
      "resultSchema": "UIntRange<256>"
    }],
    "providers": [{
      "input": "left",
      "operation": "private_state.read.v1",
      "capability": "store",
      "arguments": {"key": "claims/secret"}
    }],
    "commitCapability": "store",
    "limits": {"requests": 3, "writes": 1, "privateBytes": 4096}
  }
}
```

This abbreviated attempt identifier is explanatory. Real identifiers contain exactly 64 lowercase hex characters, without `0x`. The host must generate a unique attempt identity. Transaction IDs use the same canonical encoding. The base revision is a bounded opaque ASCII identifier. Durable storage must not recycle revisions in a way which defeats compare-and-swap.

Capabilities require an exact operation name and matching namespace. Empty prefixes and wildcard characters reject. A prefix ending in one slash grants descendants beginning with that exact byte prefix. A prefix without a slash suffix grants one exact key. `claims/` therefore grants `claims/secret` and excludes `claims_evil/secret`. Keys reject empty, dot, parent and empty interior path components. These are logical storage keys, not filesystem paths. Matching is bounded and case-sensitive.

Operation descriptors support typed argument maps of Native, Bool, normalized UIntRange and Key. Provider results are scalar. Application-defined `.v1` operation names use the same transport and capability validation. The concrete builtin `private_state.read.v1` requires exactly a Key argument named `key`. Stage and CAS names are reserved for their lifecycle APIs. Unbound inputs still use manual scalar acquisition and receive no authority to perform a protected provider operation.

## Requests and private buffers

At most one input provider or CAS request is outstanding. Repeating advance returns the same request ID. Public `need_host` metadata contains the operation, capability, result schema, input name where applicable and `hasPrivateArguments: true`. It contains no private arguments, journal keys, values or digest.

The host retrieves pending private arguments with `noctium_session_private_data(session, NOCTIUM_PRIVATE_REQUEST, ...)`. Provider arguments contain the namespace and typed argument map. The concrete read returns a scalar response through the existing resume function:

```json
{"abiVersion":1,"requestId":1,"operation":"private_state.read.v1","capability":"store","schema":"UIntRange<256>","value":"255"}
```

Every metadata field must match. Canonical range/type rules apply to the value. Rejection leaves the pending request intact. Duplicate responses reject after successful consumption. The executor neither starts nested requests nor performs the host's read itself.

Private retrieval returns a token in a separate buffer registry. `noctium_private_length`, `noctium_private_copy` and `noctium_private_free` own that token. Normal result functions reject private tokens, and private functions reject normal result tokens. Copies have no terminator and no partial-copy behavior. Session release and private-buffer release are independent. The caller owns copied bytes and their confidentiality.

## Journal preparation and transaction binding

Before execution finishes, `noctium_session_stage_private` accepts a capability-scoped typed write:

```json
{"abiVersion":1,"operation":"private_state.stage.v1","capability":"store","key":"claims/used","type":"Native","value":"8675309"}
```

These values are synthetic test data. Both the stage grant and commit grant must cover the key. Updates remain runtime-owned and mutable only in the open execution phase. Replacing one staged key replaces its proposed value. Resource-limit failure restores the previous journal. No durable private state changes at this stage.

Successful native execution freezes the journal in Prepared. A failed circuit or cancelled pre-submission session discards retained updates. No journal is exported before successful execution. The public completion result keeps `privateStateJournal: null`, including for sessions with staged writes. Journal contents never appear in completion JSON.

After constructing the final intended transaction, the host sends a `bind` notification with the exact transaction ID and attempt ID. Binding is immutable. Changing fees, signatures or another identity-bearing transaction component requires a new transaction identity and therefore a new execution attempt. The core trusts the host's transaction identity association until it validates serialized transactions/receipts itself.

A bound successful session exports the private journal through `NOCTIUM_PRIVATE_JOURNAL`. The journal contains protocol version, attempt and transaction IDs, namespace, base revision, intended contract address and entrypoint, typed writes and `journalDigest`. Address and entrypoint come from the actual native begin context rather than a later notification.

The digest is SHA-256 over the domain bytes `noctium.private-state-journal.v1\0` followed by compact UTF-8 JSON of the journal without `journalDigest`. Object keys use lexical order, scalar values use their canonical encodings, and write maps use lexical keys. No digest leaves the private buffer channel. It binds the complete frozen update payload and execution target, rather than serving as a public fingerprint of low-entropy secrets.

## Executable transition contract

`runtime/src/lifecycle.rs` contains the pure model. Fields are private. `apply(Event)` returns an effect and `invariant()` checks the resulting relationships. Identifiers and revision syntax are validated before mutation. Errors use fixed messages without caller data.

| Event | Required phase/evidence | Result/effect |
| --- | --- | --- |
| ExecutionSucceeded | Open | Prepared, freeze updates |
| ExecutionFailed | Open | Failed, discard updates |
| Cancel | Open or Prepared | Cancelled, discard updates |
| Bind | Prepared and no prior different binding | Bind exact canonical transaction ID |
| Persisted | Matching bound transaction and attempt, Prepared | Record host persistence acknowledgement |
| Submitted | Prepared, bound and persisted | Submitted |
| Uncertain | Submitted | Uncertain, no CAS request or commit |
| Rejected | Submitted or Uncertain | Rejected, discard retained updates |
| Accepted | Submitted or Uncertain | AwaitingCas, request host CAS |
| CasCommitted | AwaitingCas and all evidence matches | Committed, discard retained updates |
| CasConflict | AwaitingCas and all evidence matches | Conflicted, discard retained updates |

Success/failure/cancel repeats in the same resulting phase are idempotent where defined. The same bound ID remains idempotent and a different one rejects. Repeated persistence/submission evidence never reverses a later phase. Repeated accepted evidence in AwaitingCas returns the same CAS request, and after Committed returns committed status. A stale uncertainty notification in AwaitingCas leaves accepted evidence and its existing CAS request unchanged. Rejected evidence cannot override accepted evidence. Contradictory terminal notifications reject. Duplicate CAS responses at the ABI reject after request consumption. The pure model also treats an identical already-recorded CAS result as idempotent.

The invariant requires Committed to imply successful native execution, a bound transaction, persisted and submitted evidence, accepted host evidence and a validated successful CAS revision different from the immutable base. Uncertain, Rejected, Cancelled, Failed and Conflicted have no successful CAS. Host validation additionally requires the pending request ID, capability/schema, echoed attempt and transaction IDs, base revision and frozen private journal digest before delivering a CAS event to this model.

## Persistence, CAS and recovery

The host must persist the complete pending journal, transaction identity and target before broadcasting. It then reports `persisted`, followed by `submitted`. The core requires this acknowledgement order but cannot verify disk durability. Cancellation after submission rejects because a transaction might already be accepted. Freeing a native session does not cancel a broadcast transaction or erase durable host recovery records.

Accepted host evidence requests `private_state.compare_exchange.v1`. Private request arguments contain the frozen journal. The host performs an atomic storage transaction: compare the namespace's current revision against `baseRevision`, apply the full updates, advance the revision and record a durable idempotency receipt bound to attempt, transaction, target, base and full journal digest. Only then return:

```json
{"abiVersion":1,"requestId":3,"operation":"private_state.compare_exchange.v1","capability":"store","schema":"PrivateStateCasResult/v1","value":{"outcome":"committed","attemptId":"same canonical attempt ID","transactionId":"same exact transaction ID","journalDigest":"same private digest","baseRevision":"r0","revision":"r1"}}
```

This is a response shape, not a runnable identifier example. A conflict response uses `outcome: conflict` and the current different revision. Both commit and conflict validate all identity fields before consuming the pending request. A reply copied from another session rejects, even when its local request ID and base revision happen to match.

Concurrent attempts based on the same revision receive at most one successful durable CAS under the host's storage contract. A retry of the identical attempt and journal returns its existing receipt without applying twice. Reusing an attempt/transaction identity with different updates must reject or conflict. The reference Rust/C++ host stores bind receipts to the private journal digest and test both cases.

An absent, lost or uncertain CAS response leaves the runtime awaiting its existing request. The host retries using the same idempotency identity and queries durable receipts. It must not guess whether an update applied. Ledger uncertainty also never authorizes CAS. Later matching accepted host evidence or definitive rejection resolves a submitted uncertainty. Re-execution after a process restart must retain the same immutable identities/payload for an already persisted attempt. This package tests replay against an honest host store but does not supply a crash-durable storage adapter or serialize native session recovery state.

The core cannot roll back arbitrary network, key or callback side effects. A host must stage reversible storage updates and avoid unsafe irreversible effects in a provider advertised as a read. Neither a host claim nor these invariants prove the truth of a ledger receipt or an external database transaction.

## Limits, wiping and qualification

The opt-in context limits descriptors, capabilities and bindings to 32 each, typed arguments to 8 per operation, proposed writes to 64 and private buffers to 64 KiB. Request budget includes every private input plus one reserved CAS request, with a maximum of 257. Begin rejects an insufficient budget. Key/identifier lengths are bounded. The registry permits 64 live private buffers independently of the existing public result limit. Quota errors do not consume pending responses or authorize state changes.

Retained private result bytes are wiped on explicit free. Retained journal values and key strings are wiped best effort on commit acknowledgement, conflict, rejection, failure, cancellation and session release. Temporary parser/serializer/arithmetic copies and caller-owned copies have no complete erasure guarantee. Hosts must protect pending journals and callback arguments as private execution material.

`runtime/tests/host_protocol.rs` drives the actual ABI from Rust. `runtime/tests/cpp_host_smoke.cpp` links the native library and uses the same descriptor fixture and operation/transition sequence. Tests cover wrong metadata, canonical/range errors, scope boundaries, quotas, duplicate responses and notices, no commit before acceptance/CAS, crossed CAS replies, concurrent stale revisions, identical retries, altered-journal retries, uncertainty, rejection, cancellation and failed source execution. Neither harness invokes Node.

`Noctium.Verification.HostCas` models `Runtime::finish_cas` after response decoding, for an already-reachable pending CAS request. Kernel theorems show mismatched replies preserve the full state, an accepted commit consumes the request, a consumed request rejects duplicates, and conflict consumes the request without commit acknowledgement. The Lean runner and Rust ABI acceptance test read the same synthetic cases from `runtime/tests/fixtures/host-cas/cases.json`. The digest marker stays redacted, and the Rust test binds replies to the live private journal digest. Implementation refinement, FFI decoding, lifecycle reachability, digest authenticity, durable storage, and host receipt truth require separate evidence.

This evidence covers the runtime protocol. Full source/composite/private-state semantics, verified-bundle FFI loading, native transaction/receipt authentication, production host persistence, mobile/WASM bindings and proof-backed correspondence between the Rust implementation and the Lean lifecycle model remain visible follow-up work.
