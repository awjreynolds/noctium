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

The first catalog used a bytewise public prologue for the 256-byte memo. Its 19,217-byte call was rejected with pool error 111, `TransactionTooLarge`. A committed memo argument qualified at 9,918 bytes and 5,000 rows. The current compiler packs an ordinary public memo into nine fields and one push/readback pair.

| Memo layout | VM operations for the whole call | Circuit rows | K | Signed transaction bytes |
| --- | ---: | ---: | ---: | ---: |
| Bytewise public input | 538 | 7,966 | 13 | 19,217 |
| Packed committed argument | 26 | 5,000 | 13 | 9,918 |
| Packed public input | 28 | 4,937 | 13 | 10,477 |

The same full-width payload digests passed with each layout. [Public byte inputs](fixed-bytes.md#public-byte-arguments) · [Committed call arguments](committed-returns.md#native-call-arguments) · [Node error codes](https://docs.midnight.network/nodes/error-codes) · [Issue 74](https://github.com/awjreynolds/noctium/issues/74)

The funded isolated localnet accepted the catalog deployment and proved call. The checked helper also finalized on Ledger 9.1.0.1. Replay of the exact accepted transaction checked the ordered version 1 logs and their payload bytes. The active call at height 64918 emitted `Paused`, `ShieldedSpend` with the 32-byte nullifier, and `Unpaused`. The inactive call at height 64921 emitted `Paused` and `Unpaused`. [Finalized helper receipts](../../tests/standard-helper-event-localnet-evidence.json)

| Localnet action | Block | Transaction ID |
| --- | ---: | --- |
| Deploy | 30934 | `8fb8b254d3a39fac4d5b09a07a980d9015a872ecc8a05d8faf17f15d2ab1c729` |
| Call | 30937 | `1844e41af5c35a445d3f3a86d94c7fe661ce9186eb0a9a1b16051792d65e5f21` |

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

To reproduce the funded helper checks, assemble verified bundles for all three `StandardEvents.Token` operations with the pinned target. Point `NOCTIUM_STANDARD_EVENTS_BUNDLES` at a directory with `logSpend/`, `logCatalog/`, and `logHelperSpend/` bundles. Set `NOCTIUM_STANDARD_EVENTS_MANIFESTS` to a JSON map of operation names to trusted manifest hashes. Set `NOCTIUM_STANDARD_EVENTS_PARAMETER_CACHE` to the verified parameter cache and `NOCTIUM_STANDARD_EVENTS_NODE` to the pinned loopback development RPC.

```sh
cargo test --manifest-path runtime/Cargo.toml --locked \
  --no-default-features --features zkir-321,localnet --lib \
  localnet::tests::standard_event_helper_finalizes_logs -- --ignored --exact --nocapture
```
