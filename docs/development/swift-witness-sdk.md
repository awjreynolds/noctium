# Swift witness SDK

Swift applications run Noctium witnesses and generate and verify native proofs through the same Rust runtime as C and C++. The package links that runtime as a static XCFramework. It needs no Node process or Compact installation.

## Build and import

On Apple Silicon with Xcode, Swift 6 and the pinned Rust toolchain, install the Rust target for each platform you want. Then generate a Swift package with the same explicit target list.

```sh
rustup target add --toolchain 1.100.0 aarch64-apple-ios aarch64-apple-ios-sim
bash sdk/swift/package.sh build/noctium-swift \
  aarch64-apple-darwin aarch64-apple-ios aarch64-apple-ios-sim
```

Add the generated directory as a local Swift package in Xcode and link its `Noctium` product. Build only the slices you need. The package uses native ZKIR 3.2.1 and the repository's locked Rust dependencies. iOS compilation currently requires the compatible `libc` and `mio` patches recorded in `runtime/Cargo.lock`. The pinned ledger pulls in `sysinfo` 0.39, which imports an Apple network constant that `libc` 0.2.190 and later expose only on macOS. [Upstream sysinfo changelog](https://github.com/GuillaumeGomez/sysinfo/blob/main/CHANGELOG.md#0400) · [libc Apple declarations](https://github.com/rust-lang/libc/blob/0.2.190/src/unix/bsd/apple/mod.rs#L3706-L3743)

## Run a witness session

Compile a source `noctium_control` declaration with `--emit control`. Construct the Control ABI begin envelope with the emitted plan, your invocation inputs and your host capability registrations. `WitnessSession` takes the envelope as UTF-8 JSON `Data` and owns the native session until deinitialization.

```swift
import Foundation
import Noctium

let session = try WitnessSession(begin: beginEnvelope)
let step = try session.advance()
```

On `need_host`, call `privateRequest()`, run the registered provider, then pass the correlated reply to `resume(_:typed:)`. Use `typed: true` for the v2 reply format. Call `advance()` again until completion or rejection. `cancel()` invalidates the pending request. Keep step data, provider arguments, replies and staged values inside the trusted application. The Rust ABI frees each temporary result token before Swift returns its own copy. Your application owns any copies or logs it creates.

## Prove a native witness locally

Select an authenticated entrypoint bundle and the matching public proof parameters. Pass the native target descriptor, initial state as `{"state":{...}}`, raw parameters and exact retained `witness.control.json` bytes. The begin envelope supplies inputs and host capabilities. The exact plan goes in the separate `plan` argument. Use the same provider loop on the bound session. [Native descriptor formats](../../runtime/include/noctium_native.h) · [Build an entrypoint bundle](portable-artifacts.md#build-and-use)

```swift
let invocation = try NativeWitness(
    targetDescriptor: descriptor, initialState: state, parameters: srs,
    plan: controlPlan, begin: beginEnvelope
)
// Drive invocation.session through its host requests until completion.
let proof = try invocation.prepareProof(descriptor: proofDescriptor)
let publicIntent = try proof.proveLocally()
```

Proof preparation consumes the exact completed witness and its target on success. The SDK obtains fresh entropy from Apple Security. It generates and verifies the proof in Rust and returns the proved public intent projection. Private transcript bytes stay in the runtime during proving. Run synchronous proving on a worker and use each session serially. Funding and submission are separate operations.

## Fund and submit on the development localnet

Build an opt-in Swift package for your selected Apple targets with `--localnet`. This links the Rust adapter that verifies the pinned public development genesis and accepts only loopback endpoints. The default package still supplies witness and proof execution. [Isolated development stack](../../scripts/localnet/README.md) · [Localnet adapter configuration](../../runtime/include/noctium_native.h)

```sh
bash sdk/swift/package.sh --localnet build/noctium-swift-localnet \
  aarch64-apple-darwin aarch64-apple-ios-sim
```

Open `DevelopmentLocalnet` with the localnet configuration and a funded public development seed. Use the completed `NativeProof` to start the retained deployment or the matching witness call. A call takes ownership of the source invocation's staged private writes.

- Send `.prepare` and resolve each returned `need_host` request. Use the exact returned bytes for `resolve`. Inspect the `approval.sign.v1` request before setting `approveSigning: true`. Requests default to no signing approval.
- Save the result of `recoveryContext()` privately before submission. Then send `.submit`. The Rust client journals the sealed transaction before broadcast. If a service cannot return a trustworthy result, use `reportServiceFailure` to leave the correct reconciliation state.
- Drive `.observe` until the client verifies a finalized receipt. Use `.commit` to apply staged private writes and record the acknowledgement. Call `close()` once the runtime accepts detach.

To resume, reopen the same journal, call `DevelopmentTransaction.recover` with the client descriptor and previously saved context, then drive the initial load request with `advance()` and `resolve`. Recovery needs no wallet seed or proving material. Keep the recovery context and journal private. Use a worker and retain the transaction object until unsettled requests and durable acknowledgements are resolved.

## Prove an entrypoint with explicit inputs

Use `NativeProof(descriptor:configuration:parameters:)` for a contract whose application already holds the input values. Pass the full native proof descriptor, including `bundleDirectory`, and a private JSON configuration with the plan's `inputs` and initial `state`. The native runtime authenticates the bundle and parameters before parsing that configuration.

```swift
let proof = try NativeProof(
    descriptor: proofDescriptor, configuration: privateConfiguration, parameters: srs
)
let publicIntent = try proof.proveLocally()
```

For a development call, use `startDevelopmentCall(descriptor:setup:)` to supply the private journal setup explicitly. The original private one-time claim uses this path. [Native C ABI formats](../../runtime/include/noctium_native.h) · [Private claim source](../../examples/PrivateClaim.lean)

## Read a ledger collection page

Pass the native ABI's UTF-8 request, original Impact plan and tagged
snapshot to the Swift binding.

```swift
import Noctium

let page = try LedgerSnapshot.collectionPage(
    request: requestData, plan: impactPlan, snapshot: taggedSnapshot
)
```

Use trusted metadata for `planSha256` and `stateSha256`. For a root List,
use an empty `keys` array and start at `offset: 0`. Follow `nextOffset`
until the result returns `null`. The binding copies the JSON to owned
`Data`, releases the native result token, and reports native errors as
`WitnessSession.Failure.nativeStatus`. [Collection request and response](../../runtime/include/noctium_native.h)

The macOS package test uses the retained public List fixture from
Compact 0.36.1 and Runtime 0.21.0 on the selected Ledger 9.1.0.1 /
ZKIR 3.2.1 profile. The empty List returns no entries. The populated
List returns `["11", "22"]` at offset zero and `["33"]` at the returned
offset two, then terminates. A mismatched or malformed state digest
returns native status `1` (`NOCTIUM_NATIVE_INVALID_ARGUMENT`). The replay
passed with a macOS ARM64 XCFramework built using Rust 1.100.0 and tested
with Xcode 27.2 and Swift 6.4.2.
[Fixture manifest and digests](../../tests/fixtures/native-collection-pages/manifest.json) ·
[Compact and native fixture reproduction](native-client-abi.md#replay-the-scalar-collection-fixture)

```sh
set -eu
mkdir -p build/experiments
scratch=$(mktemp -d "$PWD/build/experiments/swift-list-pages.XXXXXX")
trap 'rm -rf -- "$scratch"' EXIT
bash sdk/swift/package.sh "$scratch/package" aarch64-apple-darwin
swift test --package-path "$scratch/package" --filter LedgerSnapshotTests
```

### Read a Field/Bool Map

Use `fieldBoolMapPage` for a request that targets a
`Map<Field, Bool>` in the supplied plan. Entries expose Field keys as
canonical decimal strings and values as Swift `Bool`. The adapter
checks the page format and returns the native continuation offset.

```swift
let flags = try LedgerSnapshot.fieldBoolMapPage(
    request: flagsRequest, plan: impactPlan, snapshot: taggedSnapshot
)
```

The same `LedgerSnapshotTests` command replays two `flags` pages from the
pinned collection fixture. It follows offset `2` and joins `1 → true`,
`2 → false`, and `10 → true` in numeric key order. The Compact fixture
writes `true` at key `2` before overwriting it with `false`. The Swift
reader preserves the stored Boolean and rejects a mismatched snapshot
digest with native status `1`.
[Compact overwrite case](../../tests/compact/native-collection-pages.mjs) ·
[Pinned fixture rows](../../tests/fixtures/native-collection-pages/manifest.json)

### Read a Bytes32 Set

Use `collectionPage` with a request for the Set. Each entry has
`kind: "bytes"` and a `values` array containing the exact 32 octets. The
native reader sorts the complete byte arrays lexicographically. Follow
the reported `nextOffset` to join pages.

The macOS package test uses the same `LedgerSnapshotTests` command and
the pinned `members` rows. The empty snapshot has no members. The
Compact oracle inserts members filled with bytes 9, 1, and 4, then
inserts the member filled with 1 again. The packaged Swift replay reads
the corresponding native snapshot. Members 1 and 4 fill page one, and
offset `2` returns member 9 and ends the Set. After removal of member 4,
the replay returns exactly members 1 and 9. The test truncates the
populated snapshot to eight bytes and hashes those bytes for the test
request. The native snapshot parser rejects the malformed input with
status `1`. [Compact insertion and removal trace](../../tests/compact/native-collection-pages.mjs) ·
[Pinned fixture rows](../../tests/fixtures/native-collection-pages/manifest.json)

## Qualification

```sh
.lake/build/bin/noctium compile tests/WitnessSource.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit control --output build/swift-witness-plans
NOCTIUM_SWIFT_PLAN="$PWD/build/swift-witness-plans/TypedWitness.scalarHost.control.json" \
  swift test --package-path build/noctium-swift
```

The typed smoke case exercises five callbacks, reads a staged private value across callback boundaries, rejects a crossed attempt ID without advancing, and returns 14. It also checks that cancellation invalidates a pending private request.

The native test uses the `TypedWitness.ScalarWitness.claim` ledger entrypoint from the same Lean source. It rejects altered control bytes and an incomplete witness, generates and verifies a K7 proof, and checks the consumed session rejects further use. To run the opt-in proof test, set `NOCTIUM_SWIFT_PROOF_FIXTURE` to a directory containing `target.json` with the authenticated target descriptor and `srs` with the exact matching K7 proof parameters. Assemble the bundle with the selected profile, current compiler artifacts, matched keys and ledger parameters. Use `TEST_RUNNER_NOCTIUM_SWIFT_PROOF_FIXTURE` for the same test under Xcode.

Both tests passed on Apple Silicon macOS and the arm64 iOS 27.0 simulator. The iPhone slice linked for iOS 16.

The development transaction test uses the same K7 source witness. It deploys and calls the contract on the isolated chain, rejects an altered signing request, and requires durable detach. It reopens the journal with a fresh client and adapter using no wallet seed, checks the exact recovered sealed bytes, and commits staged private state after finality. Both runs match all 1,482 finalized contract-state bytes by SHA-256 with the reference typed-witness run. The macOS deployment and call finalized at blocks 28961 and 28964. The iOS simulator deployment and call finalized at 28977 and 28980. [Public receipts](swift-localnet-receipts.json)

To run this test, build with `--localnet`. Set `NOCTIUM_SWIFT_LOCALNET_FIXTURE` to the proof fixture directory with additional `client.json` and `localnet.json` files in the native header's formats. The test uses the funded public development seed and creates its own journal under the fixture directory. Use `TEST_RUNNER_NOCTIUM_SWIFT_LOCALNET_FIXTURE` with Xcode. Execute funded integration tests against the same seed serially.

The original one-time claim regression uses `NOCTIUM_SWIFT_PRIVATE_CLAIM_FIXTURE` (or `TEST_RUNNER_NOCTIUM_SWIFT_PRIVATE_CLAIM_FIXTURE` under Xcode). Supply `proof.json` with the full proof descriptor, `srs` with the K9 parameters, `runtime-config.json` with the published synthetic claim inputs, and the same localnet and client configuration files. Run the `testOriginalPrivateClaimLocalnet` test. It rejects an altered secret, verifies the proof, finalizes deployment and claim, and exports the finalized public state.

Run `noctium-runtime ARTIFACT_DIRECTORY --check-state STATE_FILE --expect-rejection` with the matching native profile. The artifact directory holds the bundle plan as `source-plan.json`, relation as `zkir/claim.zkir`, `ledger.params`, the original `runtime-config.json`, and `native-contract.json` with the finalized call's `address`. This re-executes the same claim against the Swift test's exported state in the native checker. [Private claim fixture workflow](native-contract.md#compile-the-actual-lean-source)

The K9 claim finalized at block 29056 on macOS and 29073 in the iOS simulator. Both captured 1,874-byte public states match the reference private-claim digest. The native checker rejected replay against both exported states without broadcast. [Original private claim receipts](swift-private-claim-receipts.json)

Physical-device execution and production wallet adapters remain open. [Swift smoke tests](../../sdk/swift/Tests/NoctiumTests/WitnessSessionTests.swift) · [Follow-up issue](https://github.com/awjreynolds/noctium/issues/87)

To repeat the simulator test, run the package scheme against a booted simulator ID.

```sh
export TEST_RUNNER_NOCTIUM_SWIFT_PLAN="$PWD/build/swift-witness-plans/TypedWitness.scalarHost.control.json"
cd build/noctium-swift
xcodebuild test -scheme Noctium -destination "id=SIMULATOR_ID" \
  -parallel-testing-enabled NO -derivedDataPath ../swift-ios-test
```
