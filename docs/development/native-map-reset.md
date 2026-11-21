# Native Map reset

`reset values` replaces a typed Map with an empty Map. The two-entry fixture
seeds `1 → 19` and `2 → 23`. Compact 0.36.1 returns false for membership and
zero for size after reset. Its final Map contains neither key. [Lean source](../../tests/NativeMapReset.lean) · [Compact oracle](../../tests/compact/native-map-reset.mjs)

Ledger 9.1.0.1 finalized the two inserts at blocks 49381 and 49384 and
accepted the exact empty Map state at block 49387. The funded case uses a
root `Map<Field, Field>`. [Finalized receipt](native-map-reset-localnet-receipt.json)

Compile the fixture with the ZKIR 3.2.1 target and assemble authenticated
`seed` and `clearMap` bundles. Supply the manifest digests as a JSON object
keyed by entrypoint name. Run the test on the funded development node.
[Bundle assembly](portable-artifacts.md)

```sh
NOCTIUM_MAP_RESET_BUNDLES=PATH_TO_BUNDLES \
NOCTIUM_MAP_RESET_MANIFESTS=JSON_OF_TWO_MANIFEST_DIGESTS \
NOCTIUM_MAP_RESET_PARAMETER_CACHE=PATH_TO_TRUSTED_PARAMETER_CACHE \
NOCTIUM_MAP_RESET_NODE=http://127.0.0.1:19944 \
  cargo +1.100.0 test --locked --manifest-path runtime/Cargo.toml --lib \
  --no-default-features --features zkir-321,localnet \
  native_map_reset_finalizes_an_exact_empty_state -- --ignored --nocapture
```

## Nested Map reset

`reset nestedValues[disclose(owner)]` replaces the selected inner Map with
an empty Map and keeps the outer entry. Compact 0.36.1 and Ledger 9.1.0.1
both initialized empty owner 30 on an active reset. The inactive reset kept
the state unchanged. Clearing owner 10 left owner 20’s `3 → 31` untouched.
The three calls finalized at blocks 49574, 49577 and 49580. [Finalized receipt](nested-map-reset-localnet-receipt.json)

Use the same source and profile. Assemble the `seedNested` and `clearInner`
bundles and pass their manifest digests to the funded test.

```sh
NOCTIUM_NESTED_MAP_RESET_BUNDLES=PATH_TO_BUNDLES \
NOCTIUM_NESTED_MAP_RESET_MANIFESTS=JSON_OF_TWO_MANIFEST_DIGESTS \
NOCTIUM_NESTED_MAP_RESET_PARAMETER_CACHE=PATH_TO_TRUSTED_PARAMETER_CACHE \
NOCTIUM_NESTED_MAP_RESET_NODE=http://127.0.0.1:19944 \
  cargo +1.100.0 test --locked --manifest-path runtime/Cargo.toml --lib \
  --no-default-features --features zkir-321,localnet \
  nested_map_reset_retains_initialized_empty_parent_and_sibling -- --ignored --nocapture
```
