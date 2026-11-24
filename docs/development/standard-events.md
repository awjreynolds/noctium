# Standard public events

Use `emitEvent` with named fields inside a ledger entrypoint. The [example](../../examples/StandardEvents.lean) emits all eleven catalog events in one call and exercises a guarded event inline and through a checked helper.

Checked ledger helper bodies use `Statement.emitEvent kind payload`. The checker enforces the catalog payload width, preserves event order across helper calls, and carries the caller's branch into the event activity guard. Disclosure analysis requires a public guard and a public or explicitly disclosed payload.

```lean
emitEvent(Paused)
when active emitEvent(ShieldedSpend, nullifier := disclose(nullifier))
emitEvent(Unpaused)
```

Write arguments in any order. The compiler checks field names, duplicates, required fields, and exact types, then encodes them in the catalog order. Payload values and the decision to emit are public. Each private input to either needs an explicit `disclose`. Presence and address flags are public data too. Both slots of an address choice and the value of an absent optional are encoded. Put zero in slots you want left empty. [Pinned standard event catalog](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/compiler/midnight-events.ss) · [Disclosure policy](disclosure.md)

| Event | Named fields in wire order |
| --- | --- |
| `ShieldedSpend` | `nullifier` |
| `ShieldedReceive` | `commitment`, `hasCiphertext`, `ciphertext`, `hasContractAddress`, `contractAddress` |
| `ShieldedMint` | `commitment`, `domainSep`, `hasAmount`, `amount` |
| `ShieldedBurn` | `nullifier`, `hasAmount`, `amount` |
| `UnshieldedSpend`, `UnshieldedReceive` | `isUser`, `userKey`, `contractAddress`, `domainSep`, `tokenType`, `amount` |
| `UnshieldedMint` | `domainSep`, `tokenType`, `amount` |
| `UnshieldedBurn` | `isUser`, `userKey`, `contractAddress`, `tokenType`, `amount` |
| `Paused`, `Unpaused` | Empty |
| `Misc` | `name`, `payload` |

Flags have type `Bool`. Amounts are `UInt 128` and use 16 little-endian bytes. `ciphertext` takes `Bytes 512`, `payload` takes `Bytes 256`, and the other byte fields take `Bytes 32`.

Lean emits two Impact groups per event. The first pushes the version, tag and encoded bytes as three cells. The second executes `Log`. The ZKIR statement binds the ordered public groups and their activity. The Rust runtime returns the decoded native logs in `Execution::logs` during local simulation. [Ledger event format](https://github.com/midnightntwrk/midnight-improvement-proposals/blob/main/mips/mip-0002-public-contract-log-emission.md)

## Focused qualification

On Ledger 9.1.0.1 and ZKIR 3.2.1, native key generation reported K13 and 4,937 rows for the eleven-event call. The pinned Compact 0.36.1 toolchain and its 0.21.0 runtime produced the reference values. Noctium's native checker matches all eleven versions, tags, declared widths and SHA-256 digests of the full-width payloads. The fixtures exercise a 128-bit amount with the high bit set, both address branches, and a wide payload with a trailing zero. Lean rejects an undisclosed private event flag, missing or duplicate fields, and a non-Boolean flag. The helper event test checks active and inactive branches, event ordering around the helper call, its disclosed payload, and rejection of a private guard, an undisclosed payload, or a substituted public tape.

The Compact runner executes the same catalog inputs and checks the retained reference consumed by the Rust test. Pass the compiler binary and the Compact Runtime package directory. [Compact source](../../tests/compact/StandardEventCatalog.compact) · [Reference payloads](../../tests/standard-event-catalog-compact.json)

```sh
node tests/compact/standard-event-catalog.mjs "$COMPACTC" "$COMPACT_RUNTIME"
```

The catalog checks reject a 255-byte `Misc` memo and an amount of `2^128` on both runtimes. Native checking accepts separately prepared alternate payloads and rejects each altered event tape against its original call. The historical runner and source recorded in the finalized receipt remain pinned to their original files. [Finalized catalog receipt](../../tests/standard-event-catalog-localnet-evidence.json)

## Optional-field and address branches

`EventFlagBranches.emitFlagBranches` exercises six events across all four combinations of two public Bool inputs. The inputs independently control ShieldedReceive ciphertext and contract address presence, ShieldedMint and ShieldedBurn amount presence, and the user-key or contract-address arm for UnshieldedSpend, UnshieldedReceive, and UnshieldedBurn. Every absent optional and unselected address arm carries nonzero bytes or amount data, so the payload checks cover the discarded slots too.

The pinned Compact 0.36.1 runner and runtime 0.21.0 retain 24 ordered event digests. The ZKIR 3.2.1 native test checks the same four cases against the exact emitted Impact plan and ZKIR circuit. It compares version, catalog tag, order, aligned width, and SHA-256 over each full padded event payload. Replacing the false/false case's public flag tape with the true/true tape fails native checking. This is checker-only flag-branch evidence. It does not establish proof generation or ledger acceptance.

```sh
node tests/compact/standard-event-flag-branches.mjs "$COMPACTC" "$COMPACT_RUNTIME"
lake exe noctium compile tests/StandardEventFlagBranches.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --output build/experiments/1061-event-flags
NOCTIUM_EVENT_FLAG_ARTIFACTS="$PWD/build/experiments/1061-event-flags" \
  cargo test --manifest-path runtime/Cargo.toml --locked --no-default-features \
  --features zkir-321 --test standard_event_flag_branches -- \
  --ignored --exact standard_event_optional_and_address_flags_match_pinned_compact
```

The first catalog used a bytewise public prologue for the 256-byte memo. Its 19,217-byte call was rejected with pool error 111, `TransactionTooLarge`. A committed memo argument qualified at 9,918 bytes and 5,000 rows. The current compiler packs an ordinary public memo into nine fields and one push/readback pair.

| Memo layout | VM operations for the whole call | Circuit rows | K | Signed transaction bytes |
| --- | ---: | ---: | ---: | ---: |
| Bytewise public input | 538 | 7,966 | 13 | 19,217 |
| Packed committed argument | 26 | 5,000 | 13 | 9,918 |
| Packed public input | 28 | 4,937 | 13 | 10,477 |

The same full-width payload digests passed with each layout. [Public byte inputs](fixed-bytes.md#public-byte-arguments) · [Committed call arguments](committed-returns.md#native-call-arguments) · [Node error codes](https://docs.midnight.network/nodes/error-codes) · [Issue 74](https://github.com/awjreynolds/noctium/issues/74)

The funded isolated localnet accepted the catalog deployment and proved call. The checked helper also finalized on Ledger 9.1.0.1. Replay of the exact accepted transaction checked the ordered version 1 logs and their payload bytes. The active call at height 64918 emitted `Paused`, `ShieldedSpend` with the 32-byte nullifier, and `Unpaused`. The inactive call at height 64921 emitted `Paused` and `Unpaused`. The pinned Compact and fresh Noctium checks reject 31- and 33-byte nullifiers. Fresh `logHelperSpend` output matches the archived ZKIR and Impact plan hashes. [Finalized helper receipts](../../tests/standard-helper-event-localnet-evidence.json)

| Localnet action | Block | Transaction ID |
| --- | ---: | --- |
| Deploy | 30934 | `8fb8b254d3a39fac4d5b09a07a980d9015a872ecc8a05d8faf17f15d2ab1c729` |
| Call | 30937 | `1844e41af5c35a445d3f3a86d94c7fe661ce9186eb0a9a1b16051792d65e5f21` |

A later authenticated bundle deployed at block 83708 and finalized the catalog call at 83711. All eleven logs matched the pinned Compact reference in order, version, tag, aligned width, and full-width payload digest. The receipt records the bundle, source, profile, and tested optional and address flags. [Finalized catalog receipt](../../tests/standard-event-catalog-localnet-evidence.json)

```sh
lake build noctium
.lake/build/bin/noctium compile examples/StandardEvents.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --output build/experiments/standard-events
NOCTIUM_EVENT_ARTIFACTS="$PWD/build/experiments/standard-events" \
  cargo test --manifest-path runtime/Cargo.toml --locked --no-default-features \
  --features zkir-321 --test standard_events -- --ignored
```

Generate keys, assemble the authenticated bundle and submit with the Rust client for localnet qualification. [Bundle workflow](portable-artifacts.md#build-and-use) · [Native client](native-client.md)

To reproduce the funded catalog and helper checks, assemble verified bundles for all three `StandardEvents.Token` operations with the pinned target. Point `NOCTIUM_STANDARD_EVENTS_BUNDLES` at a directory with `logSpend/`, `logCatalog/`, and `logHelperSpend/` bundles. Set `NOCTIUM_STANDARD_EVENTS_MANIFESTS` to a JSON map of operation names to trusted manifest hashes. Set `NOCTIUM_STANDARD_EVENTS_PARAMETER_CACHE` to the verified parameter cache and `NOCTIUM_STANDARD_EVENTS_NODE` to the pinned loopback development RPC.

```sh
cargo test --manifest-path runtime/Cargo.toml --locked \
  --no-default-features --features zkir-321,localnet --lib \
  localnet::tests::standard_event_helper_finalizes_logs -- --ignored --exact --nocapture
```

Use `localnet::tests::standard_event_catalog_finalizes_all_logs` as the test filter to reproduce the eleven-event call.

The same variable-flag entrypoint finalized all four input pairs on the isolated Ledger 9.1.0.1 chain. Deployment finalized at block 84455, followed by calls at 84458, 84461, 84464 and 84467. The twelve optional-event logs and twelve address-choice logs matched Compact in order and full padded payload digest. The bundle records all source, key, ledger parameter and toolchain hashes. [Finalized flag-branch receipts](../../tests/standard-event-flag-branches-localnet-evidence.json)

To reproduce the flag-branch receipt, assemble an authenticated bundle for `EventFlagBranches.emitFlagBranches`. Set `NOCTIUM_EVENT_FLAG_BUNDLE` and `NOCTIUM_EVENT_FLAG_MANIFEST` to the bundle directory and trusted manifest digest. Set `NOCTIUM_EVENT_FLAG_PARAMETER_CACHE` to the verified proof and DUST material and `NOCTIUM_EVENT_FLAG_NODE` to the pinned loopback RPC.

```sh
cargo +1.100.0 test --manifest-path runtime/Cargo.toml --locked \
  --no-default-features --features zkir-321,localnet --lib \
  localnet::tests::standard_event_flag_branches_finalize_on_localnet -- --ignored --exact
```
