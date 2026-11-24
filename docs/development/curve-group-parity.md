# Curve group operation parity

The pinned Compact 0.36.1 fixture exercises `ecAdd`, `ecMul` and
`ecMulGenerator` for Jubjub, Secp256k1, Secp256r1 and Curve25519. Compact
0.36.1 exposes `ecNeg` for Jubjub only, which the fixture also covers.

The 18 vectors per family exercise the identity, generator and double generator,
with scalars zero, one, two and order minus one. They cover addition with the
identity, doubling and cancellation. The runner compiles pure Compact circuits
and records their 72 results. The Noctium checker compares each typed return to
its Compact result. The typed host also rejects a scalar equal to the group order
for each curve.

The proof test proves the generator-times-two vector for each family. It checks
the return commitment and rejects a changed commitment. The exact official SRS
hashes come from the pinned Ledger 9 provider table.

| Family | k | SRS SHA-256 |
| --- | ---: | --- |
| Jubjub | 11 | `9901589d7956ff58be0d85569b2f455b77b58c3758026ffb5bbe4807000b96d1` |
| Secp256k1 | 15 | `724c7c3d779148bb113c7ee9c034b2f27db16e6bdf315fde90105a9bad00b1de` |
| Secp256r1 | 16 | `09c877216d6589b370263e18af40a030a901b41a7a7c37ef58c9901db41f05c6` |
| Curve25519 | 17 | `4a9ef6c7c0619aab74eede44b13e753e3ba54508a02dd3b7106a949aabb73b74` |

The provider pins appear in [`data_provider.rs`](https://github.com/midnightntwrk/midnight-ledger/blob/a2b30128ca4b660b73a068e29b56b48ede8c9a74/base-crypto/src/data_provider.rs#L136-L169). Download only the four required files and verify their hashes before proof generation.

```sh
OUT=build/experiments/966/noctium
COMPACT_RESULTS=build/experiments/966/compact.json
SRS=build/experiments/966/srs
mkdir -p "$OUT" "$SRS"

lake exe noctium compile tests/CurveGroupParity.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json --output "$OUT"
node tests/compact/curve-group-parity.mjs \
  /path/to/compactc-0.36.1 /path/to/compact-runtime-0.21.0 "$COMPACT_RESULTS"

for k in 11 15 16 17; do
  curl --fail --location "https://srs.midnight.network/bls_midnight_2p$k" \
    --output "$SRS/bls_midnight_2p$k"
done
shasum -a 256 "$SRS"/bls_midnight_2p{11,15,16,17}

NOCTIUM_CURVE_GROUP_PARITY_DIR="$PWD/$OUT" \
NOCTIUM_CURVE_GROUP_PARITY_COMPACT_RESULTS="$PWD/$COMPACT_RESULTS" \
NOCTIUM_CURVE_GROUP_PARITY_SRS_DIR="$PWD/$SRS" \
CARGO_PROFILE_TEST_DEBUG=0 CARGO_INCREMENTAL=0 \
cargo +1.100.0 test --locked --offline --manifest-path runtime/Cargo.toml \
  --no-default-features --features zkir-321 --test curve_group_parity -- --ignored
```

These checks qualify the pinned Compact overloads, the native relations and
canonical host encodings.
