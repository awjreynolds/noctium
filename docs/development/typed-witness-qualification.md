# Typed-witness qualification

This record covers the source revision [`b1afd9f`](https://github.com/awjreynolds/noctium/commit/b1afd9f4afa9525a5031820ab7eeaaddbee7e299), with Git tree `c8569dd55f441cbed7bade7394b304cb038e175c`. The qualification used a fresh archive of that commit: 477 exact Git blob and mode entries. Independent snapshots matched 152 runtime files and 32 formal-review files. The machine-readable receipts and evidence summary are in [`qualification-evidence.json`](../../tests/witness62-public/qualification-evidence.json).

## Source and formal checks

`bash scripts/check-lean.sh` passed on the exact revision in 118.964 seconds. This suite covers 62 library modules and 45 standalone Lean tests. Fresh source compilation also matched all 50 retained artifact byte identities across profiles 3.2.0 and 3.2.1. The module and CLI regression check passed separately.

The formal review covered the actual invocation wrapper and input-map preservation theorem. The wrapper requires successful recording and replay validation, actual source-boundary admission, and both syntactic preflights. It derives equal results, cursors and tapes, and preserves the replay's initial private store with an empty journal. The reviewed public theorems use `propext`, `Classical.choice` and `Quot.sound`; no `sorryAx` was present. The failure theorem uses a one-shot model. Rejected source-only stage checks and malformed or contradictory callbacks fall outside its admitted runs. Native callback retries have separate runtime tests.

The scalar proof audit checked both current scalar roles against the previously reviewed model pin. It reported compatibility only. It adds no new model pin and no whole-compiler guarantee.

## Native qualification

Fresh native keys, authenticated nonzero-revision bundles, and runtime builds were checked for both supported profiles. Rust public-API proof and client tests ran separately from source-driven C++ lifecycle tests. The C++ Scalar workload completed proof, deployment, CALL and private compare-and-exchange (CAS) on the isolated development localnet. Five providers ran in each profile. An independent observer matched the complete 1,482-byte contract state at deployment and after CALL.

| Profile | Source target | Contract address | Deployment / CALL heights | Contract state after CALL |
| --- | --- | --- | --- | --- |
| 3.2.0 | [`midnight-ledger-9.json`](../../profiles/midnight-ledger-9.json) | `96978b3d73bb2ff0d372cd541a2aaebddd63258dc11129721587c3f32304a7a1` | 11285 / 11288 | `f9b24f4480110e62fe9333e5c3be687073922bd24b0935fbd62c0eb1b699c600` |
| 3.2.1 | [`midnight-ledger-9-zkir-3.2.1-target.json`](../../profiles/midnight-ledger-9-zkir-3.2.1-target.json) | `9b6f61451ca60d14f8eed8f38b4f1ef1c48c616122d743a79f4f6b121cfcab91` | 11302 / 11305 | `f9b24f4480110e62fe9333e5c3be687073922bd24b0935fbd62c0eb1b699c600` |

Both receipts report applied deployment and CALL events. The recorded before/after library hashes also match the independently checked resolved C++ library files. The separate public Rust integration test is [`witness_execution_public.rs`](../../runtime/tests/witness_execution_public.rs). For setup and profile-specific build steps, use the existing [native contract workflow](native-contract.md) and [3.2.1 integration guide](zkir-3.2.1-integrated.md), with the exact source commit and profile manifests above.

## Native Rust K7 localnet

The Rust client deployed and called the scalar witness contract on Ledger
9.1.0.1. Deployment finalized at block 49518 and the call at 49521. The Rust
provider received `cache`, `cache`, `lookup`, `cache`, `lookup` in order. The
client committed `cache/last = 14` after finality. [Rust receipt](rust-typed-witness-localnet-receipt.json)

The circuit SHA-256 matches the Swift K7 qualification. The complete
1,482-byte finalized state matches the browser and Swift receipts. The Rust
run used a fresh authenticated artifact set with its own manifest digest.
[Browser receipt](web-localnet-receipt.json) · [Swift receipts](swift-localnet-receipts.json)

Compile `tests/WitnessSource.lean` for ZKIR 3.2.1 and assemble the scalar
`TypedWitness.ScalarWitness.claim` bundle with its witness binding and
control files. Use a trusted parameter cache and a journal directory with
owner-only permissions. [Bundle workflow](portable-artifacts.md)

```sh
NOCTIUM_TYPED_WITNESS_BUNDLE=PATH_TO_BUNDLE \
NOCTIUM_TYPED_WITNESS_MANIFEST_SHA256=TRUSTED_MANIFEST_DIGEST \
NOCTIUM_TYPED_WITNESS_PARAMETER_CACHE=PATH_TO_TRUSTED_PARAMETER_CACHE \
NOCTIUM_TYPED_WITNESS_NODE=http://127.0.0.1:19944 \
NOCTIUM_TYPED_WITNESS_JOURNAL=PATH_TO_OWNER_ONLY_JOURNAL \
  cargo +1.100.0 test --locked --manifest-path runtime/Cargo.toml \
  --no-default-features --features zkir-321,localnet --test typed_witness_localnet \
  rust_typed_witness_k7_finalizes_and_commits -- --ignored --exact --nocapture
```

## Limits and reproduction

To reproduce the source suite, check out the exact commit, use its pinned Lean toolchain, and run:

```sh
git clone https://github.com/awjreynolds/noctium.git noctium-witness62
cd noctium-witness62
git checkout b1afd9f4afa9525a5031820ab7eeaaddbee7e299
bash scripts/check-lean.sh
```

The native qualification used Lean 4.35.0, Rust 1.100.0, pinned profile-specific ZKIR sources and tools, fresh keys, and the isolated development localnet. Follow the linked native workflow to recreate those prerequisites. Ledger receipts depend on a running isolated chain and a funded development identity.

Source stage statements currently support scalar private writes. The Scalar fixture has localnet proof and deployment evidence. Pair has fresh keys, authenticated bundles and checker coverage, without a ledger deployment claim. Unit and empty nominal results have source and runtime checks. These results do not establish general Helpers-to-circuit preservation, a verified Rust or FFI implementation, full ZKIR support, frontend preservation, complete privacy, or completion of project goals G1–G6. Private writes rely on truthful host persistence and are not circuit-proved state transitions. Committed-state reads also rely on the host storage service. The localnet receipts do not qualify public networks.
