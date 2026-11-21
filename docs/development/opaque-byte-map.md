# Opaque byte Map values

Use `OpaqueBytes` for variable-length byte payloads stored as public Map values.
The selected route uses `Bytes32` keys and an opaque byte leaf. The native host
accepts `{"kind":"opaqueBytes","values":[0,1,255]}` as a payload and returns the
original bytes on read. Public ledger state retains the raw bytes. The circuit
uses one field projection and the same raw value supplies the state write.
[Lean fixture](../../tests/OpaqueByteMap.lean)

FAB stores one `Compress` atom. An empty payload projects to zero. A nonempty
payload projects to the pinned length-bound transient commitment. The native
codec rejects nonempty payloads ending in zero and caps payloads at 1 MiB.
`OpaqueString` remains a separate sealed constructor metadata type.
[Pinned Compact reference](../../tests/compact/opaque-bytes.mjs)

```sh
lake exe noctium compile tests/OpaqueByteMap.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --output build/opaque-byte-map
NOCTIUM_OPAQUE_MAP_DIR="$PWD/build/opaque-byte-map" \
  cargo test --locked --manifest-path runtime/Cargo.toml --no-default-features \
  --features zkir-321 --test opaque_byte_map \
  opaque_bytes_map_round_trips_and_binds_one_compress_field -- --ignored --exact
```

The local native check uses fresh Lean plans and relations. It exercises both an
empty and a nonempty payload. It is separate from the ledger run below.
[Native check](../../runtime/tests/opaque_byte_map.rs)

## Ledger 9 localnet run

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
