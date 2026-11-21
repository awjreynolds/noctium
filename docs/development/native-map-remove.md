# Native map deletion

`remove escrow[disclose(owner)][disclose(spender)]` removes one entry from
an existing nested map. An absent final key is a no-op. An absent parent map
rejects, matching the pinned ledger VM. Removing a key preserves its siblings
and the other outer-map entries.

Removal accepts scalar and checked composite map values. It does not read the
removed value or require a caller-supplied replacement. Map keys and activity
guards follow the same disclosure checks as insertion and replacement.

The typed `removePath` effect lowers to a `mapRemove` plan operation. For N map
keys, the runtime emits four native VM operations:

1. Index the parent map with the path retained on the stack.
2. Push the final key using its declared alignment.
3. Remove the key with uncached `Rem`.
4. Reinsert the changed parent through the retained path with uncached `Ins(N)`.

Each operation has a separate Impact activity group. A false source guard skips
all four and avoids evaluating the removal path. No ZKIR instruction name is
added. This extends native ledger-state lowering.

The pinned Compact oracle and native checker agree on deleting a present
child, repeating an absent-child deletion, preserving sibling records,
rejecting an absent parent, and skipping an inactive path. [Lean source](../../tests/NativeMapRemove.lean) · [Compact oracle](../../tests/compact/native-map-remove.mjs) · [Native checker](../../runtime/tests/native_map_remove.rs)

Ledger 9.1.0.1 finalized leaf removal at block 49208 and whole-map entry
removal at 49214. The leaf removal preserved both sibling records. The
whole-map removal deleted the first owner's nested map and retained the
second owner's exact record. Repeated and inactive removals preserved the
finalized state bytes. An active removal with a missing parent rejected
during preparation and retained the admitted state token. This qualifies
the circuit method on supported typed paths. [Funded receipt](nested-map-remove-localnet-receipt.json)

Compile the fixture with the ZKIR 3.2.1 target and `--emit ledger`. Assemble
authenticated bundles for `seed`, `remove`, and `removeOwner` in separate
subdirectories of one folder. Supply their manifest digests as a JSON object
keyed by entrypoint name and run the test on isolated funded localnet.
[Bundle assembly](portable-artifacts.md)

```sh
NOCTIUM_MAP_REMOVE_BUNDLES=PATH_TO_BUNDLES \
NOCTIUM_MAP_REMOVE_MANIFESTS=JSON_OF_MANIFEST_DIGESTS \
NOCTIUM_MAP_REMOVE_PARAMETER_CACHE=PATH_TO_TRUSTED_PARAMETER_CACHE \
NOCTIUM_MAP_REMOVE_NODE=http://127.0.0.1:19944 \
  cargo +1.100.0 test --locked --manifest-path runtime/Cargo.toml --lib \
  --no-default-features --features zkir-321,localnet \
  nested_map_remove_finalizes_and_preserves_siblings -- --ignored --nocapture
```

The confidential-token port needs this primitive when refunding and replacing
an owner's prior escrow approval.
