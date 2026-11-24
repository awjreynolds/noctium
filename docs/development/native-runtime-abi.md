# Native runtime ABI v1

The Rust runtime now exports an in-process C ABI. A linked C++ host supplies the accepted private claim's five private inputs, obtains the expected public nullifier, and runs the official native circuit checker. Neither execution nor the linked harness invokes Node. The compiler remains written in Lean.

The original scalar-input slice now includes an optional versioned host-capability and private-journal protocol. General source witness functions, composite providers, durable host adapters and native receipt validation remain outstanding. Kotlin, Swift, WASM and TypeScript bindings have not been built or qualified. This ABI produces a checked execution summary and records host lifecycle evidence. It does not generate a cryptographic proof or submit a transaction.

## Version and representation

The header is `runtime/include/noctium_runtime.h`. Cargo builds `rlib`, `cdylib` and `staticlib` artifacts. ABI version 1 uses explicit UTF-8 JSON buffers, without a trailing NUL. No Rust layout crosses the boundary. Binary encodings require a separate versioned contract.

Each native build selects one profile: default `midnight-ledger-9-zkir-3.2.0` or explicit `midnight-ledger-9-zkir-3.2.1`. The release/source identity and build flags are recorded in [selectable-profile integration](zkir-3.2.1-integrated.md). A consumer rejects a different profile, rather than switching implementations from an input label. The upstream 3.2.1 source still declares crate/banner version 3.2.0. The npm distribution and native ledger crate versions differ, so canonical state/transcript vectors and new acceptance evidence qualify their shared behavior.

Native field values are canonical decimal strings, with no sign, whitespace or redundant leading zero. Values must be smaller than the BLS12-381 scalar modulus. Bool values are JSON booleans. JavaScript numbers and string booleans reject. Only explicitly public output declarations enter completion results.

The unsigned scalar extension uses normalized `UIntRange<N>` types and canonical decimal strings in `[0,N)`, with exclusive bound at most `2^248`. Its checked arithmetic, conversion and provider rules are recorded in [native-unsigned-scalars.md](native-unsigned-scalars.md).

## Host protocol

`noctium_session_begin` consumes this envelope:

```json
{
  "abiVersion": 1,
  "profile": "midnight-ledger-9-zkir-3.2.0",
  "plan": { "schemaVersion": 1 },
  "publicInputs": {},
  "state": {},
  "ledgerParametersHex": "...",
  "address": "...",
  "circuit": {}
}
```

`plan`, `state`, serialized ledger parameters and circuit use the existing qualified artifact formats. The abbreviated objects above show envelope fields, not a runnable fixture. `publicInputs` must contain exactly every declared public input. Private inputs reject in this object. The address is exactly 32 bytes encoded in hex. Unknown envelope fields reject. The artifact producer and target profile remain trusted for circuit/plan correspondence. This raw ABI begin path does not verify a signed or content-addressed artifact manifest. The Rust assembler has a separate verified-bundle entry point; a complete high-level C binding remains follow-up SDK work.

Begin returns a session token and a `ready` result token. The host calls `noctium_session_advance`. Each missing private input yields a request in declaration order:

```json
{"abiVersion":1,"status":"need_host","request":{"id":1,"operation":"witness.input","name":"secret","type":"Native","visibility":"private"}}
```

The host performs storage access, networking, prompting or other asynchronous work outside the library, then calls `noctium_session_resume` with:

```json
{"abiVersion":1,"requestId":1,"value":"42"}
```

A matching, well-typed response produces `ready`. Wrong IDs, duplicate responses, unsolicited responses, unknown response fields and noncanonical values reject. A rejected response preserves the pending request. Repeated advance returns the same pending request. Only one request exists per session, with no nested host callback stack.

After all private inputs arrive, advance evaluates the plan, executes native Impact operations, partitions transcripts with the supplied ledger cost model, constructs the diagnostic preimage and runs the official ZKIR checker. Completion returns only declared public outputs and operation counts:

```json
{"abiVersion":1,"status":"completed","result":{"publicOutputs":{},"operations":21,"activityGroups":21,"officialCircuitChecked":true,"proofGenerated":false,"transactionSubmitted":false,"privateStateJournal":null}}
```

Circuit rejection produces `failed` with the fixed error code `execution_rejected`. Neither failure results nor numeric API errors echo private input values. Completion is repeatable until release. Cancellation yields `cancelled`, clears retained input strings and prevents resumption. Legacy terminal completed/failed sessions reject cancellation. Opt-in host contexts permit cancellation after successful execution while the private journal is still prepared and unsubmitted. Releasing an incomplete session also discards retained inputs.

## Optional capabilities and private journals

Add `hostContext` to the begin envelope to declare protocol-version-1 capabilities, operation argument/result schemas, per-input provider bindings, namespace, base revision and attempt identity. Existing scalar sessions omit this field. The complete schema, transition contract and host assumptions are in [private-state-lifecycle.md](../designs/private-state-lifecycle.md).

The concrete `private_state.read.v1` operation supplies a declared private scalar from host storage. Its normal request contains operation/capability/schema metadata and `hasPrivateArguments: true`. The host retrieves arguments with `noctium_session_private_data(..., NOCTIUM_PRIVATE_REQUEST, ...)`. Resume must echo the operation, capability, schema and request ID. Canonical scalar checks still apply. Only one provider or CAS request is outstanding.

`noctium_session_stage_private` stages scoped, typed host-policy application updates. Success freezes the updates without placing them in public completion results. After execution, `noctium_session_notify` binds the exact intended transaction ID. The prepared journal is then available through `NOCTIUM_PRIVATE_JOURNAL`. The host must durably persist this private journal before sending `persisted` and `submitted` notifications.

`accepted` records host evidence and requests `private_state.compare_exchange.v1`. Acceptance alone does not acknowledge commit. Private CAS arguments include the base revision, immutable attempt/transaction/target identity, complete updates and a private digest binding those fields. The host applies an atomic, durable compare-and-swap with an idempotency receipt and echoes attempt ID, transaction ID, digest, base revision and resulting revision. Incorrect or crossed replies reject without consuming the pending request. A conflict, rejection or unresolved uncertainty never applies private updates inside the core.

Private tokens use separate `noctium_private_length/copy/free` functions. Normal result functions reject these tokens. Keys, values and digests stay out of ordinary result JSON and diagnostic errors. Each private token requires explicit release, independently from its session. Copy and ownership rules match normal results. The host owns confidentiality and erasure of copied or persisted material.

The native model exposes explicit invariant hooks for audit/proof work. Commit acknowledgement requires successful execution, matching immutable identity, persistence/submission evidence, accepted-host-evidence and matching successful CAS. Host receipt truthfulness, durable CAS correctness and crash recovery remain external assumptions. These staged writes do not implement or prove general source witness-function effects.

## Ownership, limits and failures

Sessions and results use process-local integer tokens in separate registry maps. Zero, stale and unallocated tokens reject without dereferencing foreign session pointers. Tokens are monotonic and never reused. They are not security capabilities against another caller inside the same process.

Input memory belongs to the caller and is borrowed only for each call. Results belong to Rust and remain valid until `noctium_result_free`. Query the byte length, provide a caller-owned buffer, then copy. A short buffer returns `NOCTIUM_BUFFER_TOO_SMALL`, writes zero bytes and performs no partial copy. The result has no NUL terminator. Session release does not release result tokens. Every successful allocation needs its corresponding free.

Non-null pointers still require readable or writable memory of the declared size and correct alignment. Input buffers and output storage must not overlap. Output storage regions must not overlap one another. Rust cannot validate arbitrary native addresses. Invalid pointers, allocator exhaustion and aborts lie outside panic recovery. Every fallible exported function catches unwinding Rust panics and returns `NOCTIUM_INTERNAL`. The library does not replace the application's global panic hook. Applications should avoid panic hooks which log sensitive application context.

The current implementation limits each input or result JSON buffer to 1 MiB, live sessions to 64, live results to 256, plan/circuit instruction counts to 4096, declared inputs/outputs/reads to 256 and native state slots to 16. Native field parsing bounds decimal length before big-integer allocation. These are bounded interface limits, not a hostile-code memory or CPU sandbox. Qualified artifacts remain the intended input. The supported operation whitelist excludes arbitrary ZKIR execution such as general exponentiation.

Calls serialize through one registry mutex. The host must wait for an active call before releasing its session. Cancellation takes effect between calls and does not interrupt a checker already running. No callback, filesystem access, network access, wallet key access or ambient time access occurs in this library. The CLI and fixture preparation script read files separately. Retained JSON strings receive best-effort zeroization on completion, cancellation and release. Temporary parser, field arithmetic and upstream dependency copies have no complete zeroization guarantee.

## Reproduce the linked checks

Build with the pinned Rust toolchain. `QUALIFIED_ARTIFACTS` denotes the accepted native artifact directory, including `source-plan.json`, `runtime-config.json`, `ledger.params`, `native-contract.json` and `zkir/claim.zkir`.

```sh
cd runtime
cargo build --locked
cargo test --locked
cd ..
python3 runtime/tests/prepare_abi_fixture.py "$QUALIFIED_ARTIFACTS" /tmp/noctium-abi-public.json
```

The preparation script writes only the plan, public inputs, public ledger state, parameters, address and circuit. The test host supplies fixed, synthetic private values from its own test source. It does not put production witness material into the public artifact bundle.

For macOS, set `RUNTIME_LIB` to the Cargo debug artifact directory:

```sh
clang -std=c11 -Wall -Wextra -Werror -I runtime/include runtime/tests/c_smoke.c \
  -L "$RUNTIME_LIB" -lnoctium_runtime -Wl,-rpath,"$RUNTIME_LIB" -o /tmp/noctium-c-smoke
clang++ -std=c++17 -Wall -Wextra -Werror -I runtime/include runtime/tests/cpp_smoke.cpp \
  -L "$RUNTIME_LIB" -lnoctium_runtime -Wl,-rpath,"$RUNTIME_LIB" -o /tmp/noctium-cpp-smoke
env -i PATH=/usr/bin:/bin /tmp/noctium-c-smoke
env -i PATH=/usr/bin:/bin /tmp/noctium-cpp-smoke /tmp/noctium-abi-public.json
```

The C harness checks symbol linkage, version, null inputs and invalid tokens. The C++ harness checks real claim execution, the expected public nullifier, a rejected wrong secret, request ordering, repeat advance, wrong IDs, Native/Bool validation, duplicate or unsolicited resume, cancellation, short copy buffers, explicit release and stale-token rejection. The existing native CLI remains the state-byte, five-negative-case and replay qualification check.

The host-protocol C++ harness uses the unsigned source fixture and shares the descriptor fixture with Rust tests. Its host-CAS check also consumes the shared 15-case corpus. Eleven malformed or mismatched replies must leave the pending request and private journal unchanged. The remaining cases check a committed reply, a conflict reply, and duplicate replies after either terminal state.

```sh
cargo +1.100.0 build --locked --manifest-path runtime/Cargo.toml --no-default-features --features zkir-321
python3 runtime/tests/prepare_abi_fixture.py "$QUALIFIED_ARTIFACTS" /tmp/noctium-abi-unsigned.json --unsigned-fixture
clang++ -std=c++17 -Wall -Wextra -Werror -I runtime/include runtime/tests/cpp_host_smoke.cpp \
  -L "$RUNTIME_LIB" -lnoctium_runtime -Wl,-rpath,"$RUNTIME_LIB" -o /tmp/noctium-cpp-host-smoke
python3 runtime/tests/render_host_cas_cases.py runtime/tests/fixtures/host-cas/cases.json | \
  env -i PATH=/usr/bin:/bin /tmp/noctium-cpp-host-smoke /tmp/noctium-abi-unsigned.json runtime/tests/fixtures/private-state/context.json
```

This harness and `host_protocol.rs` test scoped storage reads, staged journals, persistence ordering, crossed replies, host-CAS concurrency, deduplicated and changed-payload retries, uncertainty, rejection, cancellation, execution failure, private buffers and quotas. The original linked claim harness remains the compatibility check for sessions without `hostContext`.
