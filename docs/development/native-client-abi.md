# Native client C ABI

The native C ABI lets a C or C++ host drive Noctium's Rust proof and transaction client. The ABI uses explicit request and reply calls. Rust owns asynchronous work and its typed request mailboxes, then delegates to the same `BoundTransaction` and `SubmissionAttempt` state machine used by the Rust SDK. No foreign callback, borrowed buffer, or foreign stack frame survives a call.

Phase A proves and verifies a retained statement, then keeps the typed `ProvedIntent` inside a proof session. Phase B takes that exact deployment or call intent through funding, signing approval, submission, finalized receipt validation, and durable private journal recovery. Phase A's numeric `requestId` stays unchanged. Phase B's `u64` request identities and `u128` budgets use canonical decimal JSON strings. The ABI rejects stale, crossed, duplicate, malformed, and wrong-token replies before state changes.

The generic client ABI chooses no endpoint, wallet, entropy source, filesystem, or signing policy. Hosts provide chain, funding, signing, and journal capabilities. Phase B accepts checked typed replies from its Rust host adapter. It does not accept caller-asserted receipt JSON. Recovery loads the current full record and storage revision through the journal capability, then reobserves finalized chain state before any private compare-and-swap. An unknown broadcast remains uncertain and keeps the exact sealed transaction for reconciliation. Cancellation after submission rejects. Detach waits for durable acknowledgement. Retrying a failed cancellation or deadline persistence only retries persistence.

The optional `localnet` feature supplies one explicit development adapter. It restricts calls to the qualified loopback endpoint and isolated development genesis. It uses existing Rust node, funding, sealing, and directory-journal code. This adapter does not select a production wallet or endpoint. No Node or Compact process runs in the C++ application's proof or transaction path. Node was used only by a separate development observer to inspect finalized receipts and full state.

## Build and use

Build the shared library with Rust 1.100.0 and the selected proof profile. Profile 3.2.0 is the default. For 3.2.1, select `zkir-321` explicitly.

```sh
cargo +1.100.0 build --manifest-path runtime/Cargo.toml --locked --lib --features localnet
cargo +1.100.0 build --manifest-path runtime/Cargo.toml --locked --lib --no-default-features --features zkir-321,localnet
```

Include [`noctium_native.h`](../../runtime/include/noctium_native.h), link `libnoctium_runtime`, and call the `noctium_client_*` functions for phase B. The header documents descriptor fields, request correlation, token ownership, limits, and localnet helper configuration. [`native_client_cpp_smoke.cpp`](../../runtime/tests/native_client_cpp_smoke.cpp) is the linked qualification host. Its `run` mode writes a private recovery reference for a second process; keep that file private. Its `recover` mode needs the public descriptor, localnet configuration, and that private reference. The complete two-process run also needs the retained public bundle, private proof configuration, trusted SRS, and funded isolated localnet. The evidence file records the qualified inputs by digest without publishing private configuration or journal contents.

Compile the checked-in host against the library built for the same profile:

```sh
clang++ -std=c++17 -Wall -Wextra -Werror runtime/tests/native_client_cpp_smoke.cpp \
  -L"$LIBDIR" -lnoctium_runtime -Wl,-rpath,"$LIBDIR" \
  -o /tmp/noctium-native-client-cpp

/tmp/noctium-native-client-cpp run PROOF_DESCRIPTOR PRIVATE_CONFIG TRUSTED_SRS \
  CLIENT_DESCRIPTOR LOCALNET_CONFIG RUN_RECORD PRIVATE_RECOVERY_REFERENCE
/tmp/noctium-native-client-cpp recover CLIENT_DESCRIPTOR LOCALNET_RECOVERY_CONFIG \
  PRIVATE_RECOVERY_REFERENCE RECOVERY_RECORD
```

The run and recovery records contain sealed transaction bytes and full state. Keep them with the private recovery reference. The published evidence contains receipt identifiers and digests only.

The localnet fixture stages a host-owned Boolean `claims/accepted` value to exercise the private journal protocol. It does not establish general execution or proof of source-declared private effects through this ABI. The source claim and Rust client cover separate paths.

## Qualification

The published implementation is commit `7346401d8521ed32e36727ed42c6659d55dd2923`, tree `5b6be85f2adff7286b83c018f71afa8bcea9e377`. Frozen qualification source hashes bind the eight changed runtime files. The independently qualified snapshot matches all 81 tracked runtime files and their Git modes in the published commit.

Both 3.2.0 and 3.2.1 passed the worker's ordinary Rust suite and six retained-material proof/ABI tests. The linked C++ client deployed the retained contract, made the claim, lost a submission acknowledgement, restarted in a separate process without witness, seed, funding, or signing inputs, and recovered by resubmitting identical sealed bytes. An independent C++ rebuild repeated both profile runs. A stale private writer was rejected before broadcast. The accepted claim committed private state once. A separate development observer matched all eight finalized receipts and full contract-state byte strings against the loopback node. The published source also passed [CI](https://github.com/awjreynolds/noctium/actions/runs/43998040599).

Counts, source hashes, native binary identities, public receipt IDs, full-state digests, and independent qualification records are in [native client ABI evidence](../../tests/native-client-abi-evidence.json). This is an isolated development-network qualification. It does not prove consensus finality, universal compiler correctness, source-effect execution, business-spec correctness, or public-network behavior. The node, proof parameters and keys, entropy, external service policy, signing approval, and durable journal store remain host trust assumptions. Cancellation does not hard-stop in-flight CPU or transport work. The ABI makes no blanket native-memory erasure claim. TypeScript/WASM, Kotlin, and Swift bindings remain future goals.

## Call multiple entrypoints on one deployment

Use `noctium_native_contract_target_begin` with authenticated operation bundles
from one contract and its initial state. The target keeps one verifier map and
deployment address. Start the deployment with
`noctium_client_contract_deployment_start` and drive it through the native
client. `noctium_native_contract_state_take` issues each next state token once,
after finalized receipt validation, durable acknowledgement and private commit.

Select an operation in `noctium_client_contract_call_start` with its pinned
SRS, canonical scalar inputs and fresh entropy. The ABI proves locally and
starts a bound client. A successful start consumes the current token. A
rejected call leaves the token available for a corrected input.
Use this path for entrypoints without a witness-control sidecar.

For development recovery, use the same explicitly authorized journal with
`noctium_native_contract_target_restore` and
`noctium_native_contract_call_recover`. Pass the deployment attempt ID to
restore the original target, and the selected call attempt ID with its matching
host context to recover the client. Reobserve the finalized receipt and
complete the private commit before requesting the next state token.

Use the linked C++ test with the four authenticated
[ModuleLedger bundles](modules.md) and the pinned K6 SRS. The target and
localnet descriptors share one private journal directory. Keep the handoff
file in that directory with private permissions.

```sh
"$CPP_HOST" modules-run "$CLIENT" "$LOCALNET" "$TARGET" "$INITIAL_STATE" \
  "$K6_SRS" "$K6_SHA256" "$HANDOFF"
"$CPP_HOST" modules-recover "$CLIENT" "$LOCALNET" "$TARGET" "$INITIAL_STATE" \
  "$K6_SRS" "$K6_SHA256" "$HANDOFF"
```

On Ledger 9, the first process deployed all four operations and lost the
acknowledgement for `firstUpdate`. A new process recovered the original signed
transaction, confirmed finality and committed private state once. It then
called `againRead`, `againUpdate` and `differentUpdate`. Every finalized state
digest matched the Rust module run. A mismatched recovery context and a stale
read both rejected.
[C++ receipts and artifact pins](module-ledger-cpp-localnet-receipts.json)

## Run typed witnesses against the current state

For an operation with witness sidecars, call
`noctium_native_contract_witness_begin` with its authenticated contract target,
current-state token, selected operation, source inputs, typed host context
and SRS. The runtime selects the control plan from the retained bundle and
binds ledger reads to the state token before requesting callbacks.

Advance the witness handle to get request metadata. Read callback arguments
through the private token API and resume with a typed response for the same
attempt. To abandon an unprepared invocation, cancel it to recover the
current state. On completion, `noctium_client_contract_witness_start` prepares
and proves the call locally, then transfers its source runtime into the
native client. Drive the client through finality and durable private commit
before taking the next state token.

For the linked C++ test, compile [TypedMultiEntryWitness](../../tests/TypedMultiEntryWitness.lean)
with `--emit ledger --emit witness` and assemble both authenticated operation
bundles. Initialize the public count at 6. The test uses 6 as the application
default for its private cell and reads the journal after the first commit.
Use the same localnet and client settings as the scalar test, with the
pinned K7 SRS. Keep the exported recovery context and handoff file private.

```sh
"$CPP_HOST" typed-modules-run "$CLIENT" "$LOCALNET" "$TARGET" "$INITIAL_STATE" \
  "$K7_SRS" "$K7_SHA256" "$HANDOFF"
"$CPP_HOST" typed-modules-recover "$CLIENT" "$LOCALNET" "$TARGET" "$INITIAL_STATE" \
  "$K7_SRS" "$K7_SHA256" "$HANDOFF"
```

Ledger 9 finalized the deployment and both typed calls at blocks 145, 148
and 151. The host lost the first call's submission acknowledgement and
recovered its original signed transaction in a new process. The next
callback read the committed wallet value of 7, then advanced the public
count and private fixture value to 9. The test rejected a crossed callback
reply and retried the same valid response after releasing a full result
queue. [Finalized typed witness receipts and artifact pins](typed-multi-entry-cpp-receipts.json)

## Read a Cell

Call `noctium_ledger_cell_get` with the emitted plan, tagged snapshot, and
their trusted SHA-256 digests. Pass the root Cell name and `keys: []`.
The getter checks the declared type and FAB alignment before returning
`kind: "cell"` and the canonical scalar or checked record `value` in a
native result handle. Numeric values use decimal strings. A wrong state
kind or invalid encoding returns an error.
[C header](../../runtime/include/noctium_native.h) ·
[ABI tests](../../runtime/tests/collection_reads.rs)

## Read Counter snapshots

`noctium_ledger_counter_get` reads a root or nested Counter from the tagged
contract-state snapshot. Supply the trusted plan and snapshot SHA-256 digests.
Use an empty `keys` array for a root Counter or pass the typed public Map keys
in traversal order. The getter returns the UInt64 as a decimal string through
the native result handle, preserving values above JavaScript’s safe integer
range. It uses the supplied snapshot for the entire read. [C header](../../runtime/include/noctium_native.h) · [Native tests](../../runtime/tests/counter_snapshot_ffi.rs)

## Look up one Map entry

Call `noctium_ledger_map_lookup` with the emitted plan, exact tagged
contract-state snapshot and their trusted SHA-256 digests. Use the state
name and `keys: []` for a root Map. For a nested Map, list the typed keys
of its enclosing Maps in traversal order. Pass the final key separately
as `key`. The getter uses the Map declaration to select the scalar or flat
record key layout.

The result handle contains `kind: "mapLookup"`, a Boolean `found` field
and `value` in the same encoding as a collection page. A missing final key
returns `found: false` with a null value. Missing enclosing Maps, invalid
keys and malformed selected values return an error. The getter reads the
selected key directly from the supplied immutable snapshot.
[C header](../../runtime/include/noctium_native.h) ·
[ABI tests](../../runtime/tests/collection_reads.rs)

## Check Set membership

Call `noctium_ledger_set_member` with the same request fields as
`noctium_ledger_map_lookup`. Pass the member as `key`, separate from
any enclosing Map keys. The Set declaration supplies the member type.
Scalar keys use native input JSON. Ordinary record and qualified coin
keys use an object containing the declared fields.

The result handle contains `kind: "setMember"` and a Boolean `member`.
A valid key absent from the Set returns `false`. Missing parents, invalid
keys and a malformed selected Set value return an error. The getter tests
membership in the supplied pinned snapshot.
[C header](../../runtime/include/noctium_native.h) ·
[ABI tests](../../runtime/tests/collection_reads.rs)

## Read a List head

Call `noctium_ledger_list_head` with the emitted plan, exact tagged snapshot
and their trusted SHA-256 digests. Pass the List name and `keys: []` for a
root List, or supply the typed keys for its enclosing Maps. The getter shares
List node and element checks with paging, including counts and the empty
sentinel.

The native result handle contains `kind: "listHead"`, `found` and `value`.
Use `found` to distinguish an empty List from one whose first element is
zero. An empty List has a null value. A nonempty List uses the same typed
scalar or record encoding as a collection page entry. Malformed snapshots
and missing parent paths return an error.
[C header](../../runtime/include/noctium_native.h) ·
[ABI tests](../../runtime/tests/collection_reads.rs)

## Read collection sizes

Call `noctium_ledger_collection_size` with the same pinned plan, snapshot,
state name, and enclosing Map keys as `noctium_ledger_list_head`. The
result has `kind: "collectionSize"`, the resolved `collection` type
(`map`, `set`, or `list`), and `size` as a UInt64 decimal string.

Map and Set sizes come from the native container. List sizes use the same
node, element, and empty-sentinel checks as the List head and paging
readers. A valid empty collection has size `"0"`. Missing parents or an
unsupported collection return an error.
[C header](../../runtime/include/noctium_native.h) ·
[ABI tests](../../runtime/tests/collection_reads.rs)

## Replay the scalar collection fixture

The fixture manifest lists one public Impact plan and three tagged Ledger
`ContractState` snapshots with SHA-256 hashes of the exact files. Each
case specifies a state name, offset, limit and expected
`noctium_ledger_collection_page` response. Use `keys: []` for these root
collections and take both pins from the reviewed manifest.
[Fixture manifest](../../tests/fixtures/native-collection-pages/manifest.json)

`empty.state` covers empty List, Map and Set pages. `populated.state` has
two pages each for `values` (List of Field), `flags` (Map from Field to
Bool) and `members` (Set of Bytes32). `removed.state` records the Set
after removing the member filled with byte 4. List pages preserve
head-to-tail order. The Compact oracle sorts Map keys numerically and Set
members lexicographically before slicing the pages.

Swift and Android tests share the manifest and plan. Use the empty and
populated snapshots for List and Map cases. Set cases also use the removed
snapshot. [Swift List](https://github.com/awjreynolds/noctium/issues/1375) ·
[Swift Map](https://github.com/awjreynolds/noctium/issues/1376) ·
[Swift Set](https://github.com/awjreynolds/noctium/issues/1377) ·
[Android List](https://github.com/awjreynolds/noctium/issues/1378) ·
[Android Map](https://github.com/awjreynolds/noctium/issues/1379) ·
[Android Set](https://github.com/awjreynolds/noctium/issues/1380)

The fixture uses the selected Ledger 9.1.0.1 and ZKIR 3.2.1 profile.
The oracle uses Compact 0.36.1 at `7fa3a117c` and Compact Runtime 0.21.0.
[Target profile](../../profiles/midnight-ledger-9-zkir-3.2.1-target.json) ·
[Pinned ledger source](../../runtime/Cargo.toml) ·
[Compact release](https://github.com/LFDT-Minokawa/compact/releases/tag/compactc-v0.36.1) ·
[Compact Runtime package](https://www.npmjs.com/package/@midnight-ntwrk/compact-runtime/v/0.21.0)

Replay the retained bytes on the C ABI with Rust 1.100.0:

```sh
cargo +1.100.0 test --manifest-path runtime/Cargo.toml --locked \
  --no-default-features --features zkir-321 --test collection_reads \
  retained_collection_snapshot_pages_match_c_abi -- --exact
```

Export to a scratch directory and compare with the retained fixture. Set
`COMPACTC_0361` and `COMPACT_RUNTIME_0210` to absolute paths to the pinned
compiler and Runtime package directory.

```sh
scratch=$(mktemp -d)
trap 'rm -rf -- "$scratch"' EXIT
NOCTIUM_COLLECTION_FIXTURE_EXPORT="$scratch/fixture" \
  cargo +1.100.0 test --manifest-path runtime/Cargo.toml --locked \
    --no-default-features --features zkir-321 --test collection_reads \
    retained_collection_snapshot_pages_match_c_abi -- --exact
diff -r tests/fixtures/native-collection-pages "$scratch/fixture"
"$COMPACTC_0361" --version | grep -E '^0\.36\.1 \(7fa3a117c'
"$COMPACTC_0361" --skip-zk tests/compact/NativeCollectionPages.compact "$scratch/compact"
NOCTIUM_COMPACT_RUNTIME_DIR="$COMPACT_RUNTIME_0210" \
  node tests/compact/native-collection-pages.mjs "$scratch/compact"
```

The test builds synthetic public state with the native Ledger types and
serializes each tagged snapshot. The C ABI replay checks all ten pages
and rejects a tampered plan or snapshot hash. The Compact oracle derives
the canonical page values independently by running the collection circuits.

## Read Map pages with Bytes33 keys

The paired replay uses the existing `Map<Bytes33, Native>` source state.
The native test seeds it through the emitted `putWide` entrypoint and
reads one tagged snapshot through `noctium_ledger_collection_page`.
The replay sorts the entries from Compact's generated Map iterator by
all 33 key bytes, then compares them with the two native pages in offset
order.

All keys share the first 32 bytes `01` through `20` in hex. The replay
inserts suffix `80` with value 80, `01` with 10, and `ff` with 255, then
overwrites `01` with 11. With limit 2, the first page returns `01` and
`80` with `nextOffset: 2`. The second returns `ff` with `nextOffset: null`.
Offset 3 returns an empty page with `nextOffset: null`. Each result
retains the exact key width and the overwritten value. A wrong snapshot
hash or malformed lookup key rejects.

The replay uses Compact 0.36.1 (`7fa3a117c`) and Runtime 0.21.0, and
Noctium Ledger 9.1.0.1 / ZKIR 3.2.1. It checks the existing native ABI
on fresh source-generated artifacts and in-process state.
[Lean fixture](../../tests/FixedByteCollectionKeys.lean) ·
[Compact reference](../../tests/compact/fixed-byte-collection-keys.mjs) ·
[Native check](../../runtime/tests/collection_reads.rs)

```sh
set -eu
mkdir -p build/experiments
scratch=$(mktemp -d "$PWD/build/experiments/bytes33-map-pages.XXXXXX")
trap 'rm -rf "$scratch"' EXIT
lake build Noctium.Cli Noctium.Compiler Noctium.Frontend
node tests/compact/fixed-byte-collection-keys.mjs \
  "$COMPACTC_0361" "$COMPACT_RUNTIME_0210" > "$scratch/compact.json"
lake env lean --run NoctiumMain.lean compile tests/FixedByteCollectionKeys.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --output "$scratch/native"
NOCTIUM_FIXED_BYTE_KEYS_DIR="$scratch/native" \
NOCTIUM_BYTES33_PAGE_COMPACT="$scratch/compact.json" \
  cargo +1.100.0 test --locked --manifest-path runtime/Cargo.toml \
  --no-default-features --features zkir-321 --test collection_reads \
  bytes33_map_pages_match_compact_after_overwrite -- --ignored --exact
```

## Read Map pages with fixed-byte record keys

The paired replay uses the root `memos` Map from
`RootFixedByteRecordMap`. The key fields are `tag: Bytes<1>` and
`id: Bytes<33>`, and the value is `UInt<16>`. Both keys have tag
`[7]` and the first 32 ID bytes are `03` in hex. The record ending in
`03` has value 101 and the record ending in `04` has value 303.

Compact inserts the later record first. The comparison sorts the
generated Map iterator by tag and all 33 ID bytes. The native ABI
returns the two exact records in that order at page size one after
either insertion order. The first page reports offset `1`, the
second reports `null`, and offset `2` returns an empty page. A
separately tagged snapshot with a 32-byte FAB field in place of
the 33-byte ID rejects with `NOCTIUM_NATIVE_INVALID_ARGUMENT`
even when supplied with its correct test digest.

The replay uses Compact 0.36.1 (`7fa3a117c`), Runtime 0.21.0 and
Noctium Ledger 9.1.0.1 / ZKIR 3.2.1.
[Lean fixture](../../tests/RootFixedByteRecordMap.lean) ·
[Compact reference](../../tests/compact/root-fixed-byte-record-map.mjs) ·
[Native replay](../../runtime/tests/collection_reads.rs)

```sh
set -eu
mkdir -p build/experiments
scratch=$(mktemp -d "$PWD/build/experiments/record-map-pages.XXXXXX")
trap 'rm -rf "$scratch"' EXIT
lake build Noctium.Cli Noctium.Compiler Noctium.Frontend
node tests/compact/root-fixed-byte-record-map.mjs \
  "$COMPACTC_0361" "$COMPACT_RUNTIME_0210" > "$scratch/compact.json"
lake env lean --run NoctiumMain.lean compile tests/RootFixedByteRecordMap.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --output "$scratch/native"
NOCTIUM_FIXED_RECORD_MAP_PAGE_DIR="$scratch/native" \
NOCTIUM_FIXED_RECORD_MAP_PAGE_COMPACT="$scratch/compact.json" \
  cargo +1.100.0 test --locked --manifest-path runtime/Cargo.toml \
  --no-default-features --features zkir-321 --test collection_reads \
  record_key_map_pages_with_fixed_bytes_match_compact -- --ignored --exact
```

## Read qualified coin Set pages

Pass the emitted plan and tagged contract snapshot to
`noctium_ledger_collection_page` with the two trusted SHA-256 digests.
Use the Set name, `keys: []`, and the requested `offset` and `limit`.
The page returns `kind: "set"` and `nextOffset`. Each entry contains
`nonce` and `color` as 32-byte values, and `value` and `mtIndex` as
decimal strings.

Pages sort the records by nonce bytes, color bytes, numeric value, then
numeric Merkle tree index. Use the same snapshot and plan for every page.
The reader checks each member's canonical FAB record and null Set marker
before returning any entries. [C header](../../runtime/include/noctium_native.h) · [Native checks](../../runtime/tests/collection_reads.rs)

## Read record Set pages

A root Set with ordinary flat record keys uses the same page request and
returns one object of named fields per member. Fields sort in declared
schema order. Native and UInt values sort numerically, Bool sorts false
before true, and Bytes32 sorts lexicographically. The reader checks every
member's canonical alignment and null marker before applying the page bounds.
The pinned Compact fixture compares member values after sorting by the same
fields. [ABI tests](../../runtime/tests/collection_reads.rs) · [Compact fixture](../../tests/compact/native-collection-pages.mjs)

## Read Merkle snapshots

`noctium_ledger_collection_page` reads ordinary and historic Merkle trees
from exact tagged `ContractState` bytes. Supply the plan and snapshot hashes
from trusted artifacts for the same contract. The reader checks the complete
byte strings, the target profile and the selected path. For a nested tree,
supply the typed public map keys in traversal order.

Page queries use `offset` and `limit`. Every Merkle page includes a decimal
`root` and `firstFree`. Historic pages return their stored roots in `entries`
and a `nextOffset` for subsequent pages. Keep the same snapshot and plan for
every page. An ordinary tree has no history entries.

Use `merklePath` in place of both pagination fields. Omit the index for a
stored-leaf search, or supply a canonical decimal UInt64 index for a
candidate path. Indexed queries return sibling fields and directions in
leaf-to-root order, plus the snapshot and candidate roots. A candidate path
reconstructs the snapshot root when those roots match. Use a search to
require a stored match. An unsuccessful search has null candidate root and
steps. Sparse branches and indices beyond capacity reject.

Field, structured, typed curve, prehashed and raw FAB leaves all use the
pinned ledger leaf hash. Foreign curve inputs require ZKIR 3.2.1. The FAB
form accepts checked nonopaque atoms and bounds the expanded representation
to 1 MiB. See the request and result fields in the
[C header](../../runtime/include/noctium_native.h).

The read path uses only the plan header and state declarations. The test
constructs tagged ledger snapshots with the pinned Rust ledger API, then
compares Rust and C++ reads to Compact. Emitting Merkle operations from Lean
and submitting a transaction are separate compiler and runtime work.

```sh
profile=zkir-321
cargo +1.100.0 build --manifest-path runtime/Cargo.toml --locked \
  --no-default-features --features "$profile" --lib
mkdir -p build/experiments
scratch=$(mktemp -d "$PWD/build/experiments/merkle-reads.XXXXXX")
trap 'rm -r -- "$scratch"' EXIT
libdir="$(cd runtime/target/debug && pwd)"
c++ -std=c++17 -Wall -Wextra -Werror -I runtime/include \
  runtime/tests/collection_cpp_smoke.cpp -L "$libdir" -lnoctium_runtime \
  -Wl,-rpath,"$libdir" -o "$scratch/merkle-cpp"
NOCTIUM_COLLECTION_CPP="$scratch/merkle-cpp" \
  cargo +1.100.0 test --manifest-path runtime/Cargo.toml --locked \
    --no-default-features --features "$profile" --test merkle_reads
```
