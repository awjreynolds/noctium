# Native Rust client

The Rust SDK prepares, funds, approves, seals and submits native contract deployments, verifier installation updates and calls. The application path uses native Rust libraries throughout. `runtime/examples/native_client.rs` deploys the retained Lean claim and submits its claim call without a Node runtime, Compact compiler, toolkit executable or proof-server subprocess. C and C++ hosts use the [native client ABI](native-client-abi.md), which drives this same Rust transaction state machine through explicit host requests.

The host-neutral modules are `proof`, `funding` and `client`. The `localnet` feature adds an explicit loopback RPC adapter, development wallet adapter and filesystem journal. The added HTTP, BIP32 and metadata adapters build only with `localnet`. The core exposes no endpoint or seed policy.

## Transaction order

1. Authenticate the retained artifact manifest and select exactly one 3.2.0 or 3.2.1 contract profile. Supply separately trusted native SRS bytes. `PreparedProof` freezes the exact contract intent and verifies the returned proof with the retained verifier key before attaching ledger V3 proof bytes.
2. Obtain a finalized ledger snapshot through `ChainAdapter`. Check ledger network ID, genesis hash, runtime specification version, transaction version and selected contract profile before funding or approval.
3. Keep the proved contract intent unchanged in native segment 1. `DustFunding` selects native DUST outputs and proves a separate fee intent in segment 2. Merge the two native transactions. Iteration uses actual sealed size, the live ledger fee model and an explicit fee margin and budget. Selection is speculative. Replay accepted chain history before preparing another spend.
4. Ask `SigningAdapter` for explicit host approval and native sealing. `BoundTransaction::prepare` compares every intent field, proof and public commitment across funding and signing. It checks native signatures, proofs, balance, execution success and budget using the current ledger state. The resulting object freezes the exact serialized transaction, native transaction and intent hashes, expected contract address and exact predicted native contract state.
5. Bind the prepared host runtime journal to a fresh attempt ID and the frozen transaction. Persist the complete private record before broadcast. Only submit these frozen bytes on retry.
6. Validate canonical finalized ancestry, the exact submitted extrinsic, its event phase and index, and the native transaction hash. Full success requires exactly one `TxApplied`, the expected contract events, and the full predicted contract state at the inclusion block. A checkpointed call follows the prefix receipt checks below.
7. After acceptance, compare and exchange private writes against the journal's original private revision. Store the complete CAS identity and deduplication receipt atomically with private writes. Durably persist the validated terminal receipt before acknowledging the host runtime.

Use the [composed call flow](native-call-claims.md#fund-and-observe-on-localnet) for a Rust intent with multiple proved calls. The same funding and sealing path verifies the full intent, and the node adapter checks every call event and exact state in one finalized block. A composed Rust host manages its own retries. The private journal and C/C++ client admit single-action intents.

`PublicTransactionReference::from_composed_calls` supports read-only correlation for exactly two ordered calls. The caller supplies authenticated address, entrypoint and final-state bytes for each slot. The reference checks both action identities, derives the one-event count for each address, and binds the first state as the primary receipt state and the second as a secondary state. It reuses the canonical transaction envelope checks and `check_receipt` identity, finality-shape and state checks. `NetworkPolicy` binds the selected profile to the current runtime build, while transaction proof blobs remain opaque to this API. The constructor does not verify proofs, sign, submit or commit private state. The offline test uses public transaction and block-end state bytes from [the independent composition receipt](independent-composition-receipt.json). It pins the derived transaction ID and intent ID plus the caller and callee state digests. The report supplies inclusion height, block hash, extrinsic hash and index as trusted inputs. The test does not establish RPC receipt truth. The historical capture trusts the development RPC, and independent proof acceptance remains a separate assumption.

The development claim has no NIGHT offers or unshielded source accounts. Its signing adapter approves the complete transaction and creates native binding seals. The DUST spend proof authorizes fees using the host-held DUST key. This qualification does not cover a general unshielded-account signing wallet, shielded wallet or registration flow.

The legacy native DUST system precompile uses the pinned ledger's `midnight-zkir` 2.2.0 dependency. That system dependency is separate from the selected Lean contract target and does not change the exclusive 3.2.0/3.2.1 contract features. Both DUST and contract proofs are real native proofs.

## Host boundaries and recovery

`ChainAdapter`, `FundingAdapter`, `SigningAdapter` and `JournalStore` are explicit host capabilities. The core reads no environment variables, files, credentials or endpoints. The host owns transport deadlines, entropy, wallet state, signing approval, trusted manifests and parameters.

`JournalStore::load` must return the current authoritative full record and its storage revision. Importing caller-supplied recovery bytes does not satisfy this contract. A record's self-hash authenticates neither its phase nor acceptance. `persist` uses versioned compare and exchange and acknowledges the exact full-record digest, including progress and CAS receipt. Concurrent stale copies fail before rebroadcast or private mutation. Terminal records do not roll back to submitted or uncertain.

Recovery validates native transaction encoding and hashes, the complete journal identity and immutable body. Recovered acceptance and terminal CAS records require a fresh finalized chain observation before private mutation or runtime reconciliation. The runtime's exact attempt, transaction, base revision, target, journal digest, pending operation, capability and request ID are checked before external CAS. A lost CAS acknowledgement reuses the store's atomic receipt. Repeating a committed operation does not apply private writes twice.

Chain acceptance and private CAS success are separate outcomes. A transaction accepted on chain stays accepted when private storage reports a revision conflict. The SDK makes no atomicity claim across those systems.

Before broadcast, cancellation clears active runtime writes and records cancellation. Cancelled and rejected durable records retain private journal material until the host removes them under its retention policy. Cancellation prevents CAS and does not promise durable-record erasure. After broadcast, cancellation reports `CancellationAfterBroadcast` and preserves the journal. A deadline or lost transport acknowledgement records uncertainty and keeps the exact transaction available for reconciliation. Pool stale, banned, replaced or invalid responses after an unknown broadcast do not establish absence of ledger effects. The loopback adapter keeps these outcomes uncertain unless a matching finalized receipt already establishes acceptance. Hosts with a verified, fully correlated definitive rejection source may return `Observation::Rejected`.

### Checkpoint prefix receipts

For a single signed call with a guaranteed prefix and a checkpoint in its fallible transcript, the SDK records both native VM predictions at preparation. A finalized `TxPartialSuccess` event binds the transaction hash. The loopback adapter recovers the segment results by replaying the exact extrinsic and checking the inclusion block's native ledger root. It requires the guaranteed segment to succeed, the call's fallible segment to fail, and the contract state after the call and at block end to match the predicted prefix bytes.

`observe_once` returns `ObservedReceipt::Partial` for this terminal outcome. The journal retains the verified receipt and staged writes in `PartiallyAccepted`. Recovery returns the same classification from the authoritative journal. Resubmission and private CAS are disallowed for this phase.

Proof-service cancellation follows the separately documented host stop future in [native-proof-api.md](native-proof-api.md). Native proving and fee construction still have synchronous work between await points. Cancellation does not interrupt arbitrary native CPU work or reverse a submitted transaction.

`localnet::journal::DirectoryJournal` treats its caller-selected directory and current contents as a trusted host capability. Unix directories use mode 0700, files use 0600. New directory creation syncs each directory and its parent before the store acknowledges a record. Atomic no-follow, nonblocking Unix opens and regular-file checks reject symlinks, FIFOs and other special files. An OS lock serializes readers and writers. Updates use a new file, file sync, rename and directory sync. Versioned records, monotonic transitions and atomic private-state/CAS receipts survive process restart and lost acknowledgements. Hashes detect corruption and correlate records. They do not defend against a malicious owner editing the trusted directory. Production hosts should supply storage with their own authentication, access control, backup and durability guarantees. Rust-owned private journal buffers receive best-effort zeroization. JSON libraries and native proving dependencies retain additional copies outside a whole-process erasure guarantee.

## Loopback adapter

`Node::connect` accepts only an explicit loopback endpoint and pinned `NetworkPolicy`. It validates the network and negotiated metadata before opening a wallet seed. HTTP deadlines and response caps are mandatory. Redirects and ambient proxies are disabled.

The tested node reports genesis `823383ec0302be8417cfcbcc62f21df08f4047bca37aaea89e3f54b550ebae1d`, ledger network `undeployed`, runtime spec version 2001100 and transaction version 4. Default `state_getMetadata` returns V14. The adapter explicitly negotiates V16 with `Metadata_metadata_at_version`, at a pinned finalized block. It pins the negotiated metadata fingerprint and runtime code hash, checks metadata at finalized heads and genesis, and checks runtime code identity at every decoded historical block. Runtime transitions fail closed. It validates the actual call and event types, encodes `send_mn_transaction(midnight_tx: Bytes)` from metadata and uses unsigned Substrate extrinsic V4. Historical genesis bare V5 extrinsics are decoded only when advertised by metadata. These versions refer to the Substrate envelope, not the contract proof profile.

State hydration uses `system_properties.genesis_state`, published genesis extrinsics and finalized block replay through pinned native ledger APIs. System transactions, DUST events, timestamps and post-block cost updates run in order. The native stored ledger root must equal `MidnightRuntimeApi_get_ledger_state_root` at the finalized head. `Midnight.StateKey` is a storage-root key, not serialized full ledger state. There is no root-as-state shortcut.

Receipt scans verify numbered parent links from the matching block through the captured finalized head before returning acceptance. Development funding requires the wallet replay cache to match the supplied finalized snapshot, state and block context before accessing the DUST key or consuming randomness. The optional adapter uses bounded blocking HTTP. Async applications should run this adapter on a dedicated host thread.

The adapter trusts the loopback node's genesis, complete historical data, canonical block hashes and finality reports. Local replay and root equality detect mismatches within that boundary. This is not a consensus light client or an independent finality proof. Unsupported historical effects or changed runtime/profile assumptions fail closed. Retained key/circuit correspondence, SRS ceremony provenance and SRS pairing relations retain the external trust scope documented by the proof API.

Native algorithms and interfaces were checked against official `midnight-node` source commit `3ef49177d59a2f9735cabd044af8fae35fd808ca`, especially `util/toolkit/src/fetcher/{fetch_task,compute_task,runtimes}.rs` and `ledger/helpers/unsafe/src/ledger_9/{context,wallet/hd,wallet/dust}.rs`. Those reference files carry Apache-2.0 notices. The narrow adapter is independently written against public native APIs. No toolkit source was copied into MIT runtime files. The image's Earthly build label does not authenticate that source commit as the running toolkit revision. The native ledger dependency retains its existing exact git pin `a2b30128ca4b660b73a068e29b56b48ede8c9a74` and upstream license.

Tested optional dependencies are reqwest 0.13.5, bip32 0.5.3, frame-metadata 23.0.1, parity-scale-codec 3.7.5, scale-info 2.11.6, scale-value 0.18.2, blake2 0.10.6 and libc 0.2.191. `Cargo.lock` records the complete dependency resolution.

## Standalone example

Build and run with `cargo run --manifest-path runtime/Cargo.toml --features localnet --example native_client -- HOST_CONFIG.json`. Select 3.2.1 with `--no-default-features --features zkir-321,localnet`. A host configuration has this shape:

```json
{
  "endpoint": "http://127.0.0.1:19944",
  "policy": {
    "networkId": "undeployed",
    "genesis": "823383ec0302be8417cfcbcc62f21df08f4047bca37aaea89e3f54b550ebae1d",
    "specVersion": 2001100,
    "transactionVersion": 4,
    "profile": "midnight-ledger-9",
    "maxDust": 10000000000000000000000
  },
  "bundle": "/trusted/claim-bundle",
  "manifestSha256": "HOST_PINNED_MANIFEST_SHA256",
  "privateConfig": "/private/claim-config.json",
  "parameterCache": "/trusted/native-parameter-cache",
  "parameterSource": "https://srs.midnight.network/",
  "journalDirectory": "/private/native-client-journal",
  "seed": { "kind": "publicDevelopmentGenesis" },
  "approve": true,
  "waitSeconds": 90,
  "resumeAttempt": null
}
```

`publicDevelopmentGenesis` is an explicit example-only choice for the published synthetic genesis seed. The example rejects a different genesis with that choice. A host-owned raw seed file uses `{"kind":"file","path":"/private/wallet-seed"}` and contains 16 or 32 raw bytes. The SDK core has no seed default. `ProofCache` reads only the explicit parameter directory in synchronous mode. It checks pinned native provider hashes and bounded checked native encodings, and never downloads missing material.

The example's host policy stages a Boolean `claims/accepted` private write in an address-specific namespace. This illustrates the host journal API. It is not a claim about source-program private effects. Set `resumeAttempt` to the printed attempt ID to reopen the trusted journal and reconcile the same immutable transaction. Recovery opens neither the private claim configuration nor wallet seed. A timeout leaves a recoverable journal. Output contains public identifiers and private commit status, never witnesses, seed bytes or journal contents.

The adapter bounds responses at 64 MiB in the example, metadata at 2 MiB, native transactions at 4 MiB, exact contract states at 1 MiB, private records at 32 MiB, journal database files at 128 MiB and retained attempts at 256. Fee construction uses at most ten convergence rounds, up to 64 spends by policy and an eight-block maximum margin. Example policies use eight spends and a three-block margin. Replay limits, request deadlines and lock deadlines are explicit host choices. Larger history or journal retention needs a different bounded host policy or adapter.

## Retained qualification

[tests/native-client-evidence.json](../../tests/native-client-evidence.json) records public native receipts, full-state hashes, metadata and runtime-code fingerprints, both SRS digests, profile manifests and source hashes for both selected contract profiles. The opt-in Rust test `localnet::tests::real_rust_only_funded_deploy_and_claim` runs real local contract and DUST proofs, funds and seals native transactions, submits them through metadata-encoded RPC, and requires exact finalized contract state. The linked C++ client ABI also passes deployment, claim, lost-acknowledgement recovery, and separate-process restart qualification on both profiles. See [native client ABI evidence](../../tests/native-client-abi-evidence.json) for source binding, independent receipt checks, and scope.

The same test loses the first submission acknowledgement, persists uncertainty, rejects cancellation after broadcast, preserves a deadline as uncertainty, reopens the filesystem journal and retransmits identical bytes. It requires fresh finality after committed recovery. Both transactions remain chain-accepted when a shared private revision permits one CAS and conflicts the other. Invalid native proof bytes, a changed public commitment, the wrong network, wrong genesis/profile, altered receipt fields and replay all reject. The five retained invalid claim inputs are secret, path, direction, root and nullifier. All 34 adversarial scalar cases run against each linked native profile.

Focused tests cover stale recovered writers, forged progress and expected state, wrong runtimes and pending request IDs, lost CAS acknowledgements, live terminal-persistence retry, duplicate private commit, private revision conflict, corruption and bounded rejection of symlinks, FIFOs and nonregular files. Both core builds pass with `localnet` disabled. The separately executed standalone example commits deployment and claim private revisions, then a new process resumes the committed claim with seed, private configuration and bundle paths deliberately absent.

Run the ordinary suite with `cargo test --manifest-path runtime/Cargo.toml --locked --features localnet`. The real test additionally needs authenticated `NOCTIUM_TEST_BUNDLE`, `NOCTIUM_TEST_MANIFEST_SHA256` and `NOCTIUM_TEST_PRIVATE_CONFIG`, the explicitly selected loopback node and the qualified native parameter cache. Set `NOCTIUM_TEST_EVIDENCE` to retain public receipt JSON. Use the exclusive 3.2.1 feature flags shown above for the second profile. The test environment is test-harness policy, separate from the host-neutral core API.
