# Opaque Map values

Use `OpaqueBytes` for variable-length byte payloads stored as public Map values.
The selected route uses `Bytes32` keys and an opaque byte leaf. The native host
accepts `{"kind":"opaqueBytes","values":[0,1,255]}` as a payload and returns the
original bytes on read. Public ledger state retains the raw bytes. The circuit
uses one field projection and the same raw value supplies the state write.
[Lean fixture](../../tests/OpaqueByteMap.lean)

FAB stores one `Compress` atom. An empty payload projects to zero. A nonempty
payload projects to the pinned length-bound transient commitment. The native
codec rejects nonempty payloads ending in zero and caps payloads at 1 MiB.
[Pinned Compact reference](../../tests/compact/opaque-bytes.mjs)

Use `OpaqueString` as a public value in a root `Bytes32` Map. The native host
accepts and returns `{"kind":"opaqueString","value":"é\u0000λ"}`. Storage
preserves the exact UTF-8 bytes, including an embedded NUL, and binds the same
single `Compress` field in the circuit. Empty strings are valid. The codec
rejects a trailing NUL, malformed UTF-8 in stored state, and opaque byte
payloads presented to a string entrypoint. The string limit is 1 MiB of UTF-8.
[Lean fixture](../../tests/OpaqueStringMap.lean) · [Native check](../../runtime/tests/opaque_string_map.rs) · [Compact reference](../../tests/compact/opaque-string-cases.mjs)

Mutable root Cells accept both types through `cell text : OpaqueString` or
`cell bytes : OpaqueBytes`. The empty value initializes each Cell. A write
stores the exact public payload and binds its Compress projection. A read
binds one field and returns the original value. The native query-context check
matches Compact for the empty, embedded-NUL string and binary payload cases.
Altering a bound input or output makes the relation check fail.
[Lean fixture](../../tests/OpaqueCells.lean) · [Native check](../../runtime/tests/opaque_cells.rs) · [Compact fixture](../../tests/compact/OpaqueCells.compact)

Ledger 9.1.0.1 deployed both empty Cells at localnet height 51204. The
store finalized at 51207 with the exact UTF-8 string and bytes. The
proof-bound reads finalized at 51210 and 51213 and preserved the full
state bytes. The store circuit used K7 and 66 rows. Each read used K6
and 34 rows. [Finalized receipts](opaque-cells-localnet-receipt.json)

Use `when enabled reset text` or `when enabled reset bytes` to clear a
mutable root Cell. The active write stores a canonical empty Compress atom.
The inactive call preserves the existing value. The fixture reads both
Cells in the same call and binds both opaque returns to the proof. Compact
0.36.1 and the native checker agree on both guard outcomes.

On Ledger 9.1.0.1, the inactive call at height 51583 preserved the seeded
state bytes. The active call at 51586 restored the exact deployed empty
state. The clear relation used K7 and 98 rows.
[Lean fixture](../../tests/OpaqueCellReset.lean) ·
[Compact oracle](../../tests/compact/opaque-cell-reset.mjs) ·
[Finalized receipts](opaque-cell-reset-localnet-receipt.json)

```sh
lake exe noctium compile tests/OpaqueByteMap.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --output build/opaque-byte-map
NOCTIUM_OPAQUE_MAP_DIR="$PWD/build/opaque-byte-map" \
  cargo test --locked --manifest-path runtime/Cargo.toml --no-default-features \
  --features zkir-321 --test opaque_byte_map \
  opaque_bytes_map_round_trips_and_binds_one_compress_field -- --ignored --exact
```

The byte Map check uses fresh Lean plans and relations for an empty and a
nonempty payload. For the string Map check, use a fresh output directory.
[Native check](../../runtime/tests/opaque_byte_map.rs)

```sh
artifacts=$(mktemp -d)
trap 'rm -rf "$artifacts"' EXIT
lake exe noctium compile tests/OpaqueStringMap.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --output "$artifacts"
NOCTIUM_OPAQUE_STRING_MAP_DIR="$artifacts" \
  cargo test --locked --manifest-path runtime/Cargo.toml --no-default-features \
  --features zkir-321 --test opaque_string_map \
  opaque_string_map_round_trips_canonical_utf8 -- --ignored --exact
```

## Ledger 9 localnet runs

### OpaqueBytes

One source-derived run deployed `OpaqueByteMap`, stored `[0,1,255]` at a
`Bytes32` key, and read the same key. The finalized public state contains the
raw bytes in the Map's `Compress` cell. The read proof binds the disclosed
return to its public transcript, and the finalized state bytes stayed
unchanged after the read. [Receipt and artifact provenance](../../tests/opaque-byte-map-localnet-evidence.json)

Reproduce on the isolated development chain. Use its exact genesis and runtime
from the [localnet guide](../../scripts/localnet/README.md). Compile the Lean
fixture for the selected 3.2.1 profile, then generate K8 store keys and K7 read
keys with the pinned official CLI. Set `MIDNIGHT_PP` to a verified public
parameter directory containing `bls_midnight_2p8` and `bls_midnight_2p7`.
Assemble one bundle for each entrypoint using the [portable bundle recipe](portable-artifacts.md),
the profile-matched ledger parameters, native provenance file, and matching
prover and verifier keys. Verify and pin both manifest digests.

```sh
artifacts=$(mktemp -d)
lake exe noctium compile tests/OpaqueByteMap.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --output "$artifacts"
node scripts/zkir/bootstrap-native.mjs --version 3.2.1 /private/tmp/noctium-native-zkir-321
MIDNIGHT_PP=/path/to/verified-public-parameters \
  /private/tmp/noctium-native-zkir-321/bin/zkir compile \
  "$artifacts/OpaqueByteMap.store.zkir" \
  "$artifacts/OpaqueByteMap.store.prover" \
  "$artifacts/OpaqueByteMap.store.verifier"
MIDNIGHT_PP=/path/to/verified-public-parameters \
  /private/tmp/noctium-native-zkir-321/bin/zkir compile \
  "$artifacts/OpaqueByteMap.read.zkir" \
  "$artifacts/OpaqueByteMap.read.prover" \
  "$artifacts/OpaqueByteMap.read.verifier"
```

Build the host and bundler with Rust 1.100.0, then run the host with a JSON
configuration containing `endpoint`, `policy`, `storeBundle`,
`storeManifestSha256`, `readBundle`, `readManifestSha256`, `parameterCache`,
`parameterSource`, `journalDirectory`, `receiptOutput`,
`approveLocalDevelopment`, and `waitSeconds`. Set `journalDirectory` to an
absolute private directory with mode `0700`, and set
`approveLocalDevelopment` to `true` for this isolated fixture.

```sh
cargo +1.100.0 build --manifest-path runtime/Cargo.toml --locked \
  --no-default-features --features localnet,zkir-321 \
  --bin noctium-bundle --example opaque_byte_map_localnet
# Assemble and verify one portable bundle per entrypoint as described above.
cargo +1.100.0 run --manifest-path runtime/Cargo.toml --locked \
  --no-default-features --features localnet,zkir-321 \
  --example opaque_byte_map_localnet -- HOST_CONFIG.json
```

This qualifies the selected payload and entrypoints on one local ledger run. It
does not establish general opaque-byte equivalence, privacy guarantees or
public-network deployment.

### OpaqueString

A separate source-derived run deployed `OpaqueStringMap`, stored `é\u0000λ`
under one `Bytes32` key, then read the same key. The finalized Map cell matched
the exact UTF-8 `Compress` bytes. The public read result and its one-field
transcript matched the same string, and the finalized state stayed unchanged
after the read. Deployment, store and read finalized at heights 17, 20 and 23.
The store circuit measured K8 with 127 rows. The read circuit measured K7
with 115 rows. [Receipt and artifact hashes](../../tests/opaque-string-map-localnet-evidence.json)
· [Lean fixture](../../tests/OpaqueStringMap.lean).

The localnet driver retains the `OpaqueBytes` branch and selects the value
type from the verified entrypoint plans. This string run covers one value and
one Map entry only. It does not establish
general string equivalence, privacy guarantees or public-network deployment.

### Opaque Maybe values

Readable witness circuits accept `some(value)` and `none(OpaqueString)` or
`none(OpaqueBytes)`. The native session preserves each typed payload,
including embedded NULs. The call result binds each Bool tag and one
Compress field per payload. The pinned Compact fixture returns the same
four tag and payload pairs. The native checker rejects a modified payload
under the original relation. Source checking rejects publishing a private
payload through `some` without an explicit disclosure.
The POC workflow lowers fresh artifacts and replays the retained Compact
vectors. The live oracle reproduces those vectors separately.

The emitted relation sizes at K8 with 155 rows under ZKIR 3.2.1. A focused
run with the official K8 parameters generated fresh keys, proved and
verified the native statement, and rejected the original proof against the
commitment derived from a changed string return.
[Lean fixture](../../tests/OpaqueMaybe.lean) · [Compact oracle](../../tests/compact/opaque-maybe.mjs) · [Retained vectors](../../tests/compact/OpaqueMaybe.expected.json) · [Native test](../../runtime/tests/opaque_maybe.rs)

```sh
mkdir -p build/experiments
scratch=$(mktemp -d "$PWD/build/experiments/opaque-maybe.XXXXXX")
trap 'rm -rf "$scratch"' EXIT
node tests/compact/opaque-maybe.mjs "$COMPACTC_0361" "$COMPACT_RUNTIME_0210" > "$scratch/compact.json"
lake exe noctium compile tests/OpaqueMaybe.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --emit witness --output "$scratch/native"
NOCTIUM_OPAQUE_MAYBE_DIR="$scratch/native" \
NOCTIUM_OPAQUE_MAYBE_COMPACT="$scratch/compact.json" \
NOCTIUM_OPAQUE_MAYBE_PROOF_SRS="$PARAMS/bls_midnight_2p8" \
  cargo test --locked --manifest-path runtime/Cargo.toml --no-default-features \
  --features zkir-321 --test opaque_maybe -- --ignored
```

### Opaque Either values

Readable witness circuits support `either(tag, left, right)` with an
opaque string or byte array arm. The chosen opaque payload keeps its
type and exact contents. An inactive opaque arm uses its typed empty
value. ZKIR selects the Compress field using the same tag as the witness.

The Compact 0.36.1 fixture checks both tags with an opaque string on the
left and an opaque byte array on the right. The pinned native execution
matches both results and rejects an altered active return for either
type. The Lean authoring check rejects publishing a private tag or
payload without explicit disclosure. The emitted relation sizes at K8
with 174 rows. [Lean fixture](../../tests/OpaqueEither.lean) · [Compact oracle](../../tests/compact/opaque-either.mjs) · [Native checker](../../runtime/tests/opaque_either.rs)
