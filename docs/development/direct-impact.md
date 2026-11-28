# Direct ledger transcript conformance

The Lean native backend compiles the private claim relation and state guards
without Compact. `Noctium.Backend.Impact.lower` builds a symbolic native VM
plan. `Noctium.Backend.Zkir.lowerEntrypoint` binds its complete field encoding,
including opcodes, alignments, keys, read results, and write values.
The relation emits one Impact group for each native VM operation. The checker
returns one activity entry per group, which transaction proving consumes in
operation order. A single group over the same flattened field values passes
standalone checking but fails this transaction-level requirement.
Native contract entrypoints also enable the communication commitment. The
ledger verifier always places this commitment after the binding input in the
proof's public instance. Standalone relations leave this flag disabled.

The state layout is a root array in declaration order. Native and boolean cells
use Native field alignment. Native VM map membership produces a byte-aligned
boolean. The lowerer binds each membership result to false before inserting the
nullifier. A circuit assertion binds the read root and campaign to the public
parameters. A state read alone does not enforce either comparison.

## Reproduce

Run from the repository root with the pinned Lean toolchain:

```sh
lake build Noctium.Backend.Zkir Noctium.Claim
mkdir -p build/direct-impact
lake env lean --run tests/Impact.lean > build/direct-impact/operations.json
lake env lean --run tests/Impact.lean --zkir > build/direct-impact/claim.zkir
npm ci --prefix scripts/zkir
node scripts/zkir/check-impact.mjs build/direct-impact/operations.json build/direct-impact/claim.zkir
```

The fixture uses public, deterministic test inputs. Its secret is 42, campaign
is 7, siblings are 17 and 23, and directions are false and true. Domain tags
1, 2, and 3 are Noctium application choices. The Lean operation fixture uses
root 99 and nullifier 123 as placeholders. The harness replaces those values
with the pinned ledger package's native hash results before constructing the
proof preimage and executing the VM.

## Verified boundaries

The locked dependencies are `@midnight-ntwrk/ledger-v9` 1.0.2 and the official
`@midnightntwrk/zkir-v3` 3.2.0 release tarball.

The official ZKIR implementation accepts the generated relation and its ledger
proof preimage. This covers preprocessing and assertion checking, with the
native full-transcript encoding rather than a synthetic list of public values.
The fixture has k=9 and serializes to 2,610 bytes. Its 21 native VM operations
produce 21 checker activity entries. The harness asserts this count as a
transaction-binding regression check.

Negative preprocessing checks reject a wrong secret, public root, public
campaign, stored root, and stored campaign. The native ledger VM separately
executes the matching transcript, records the nullifier, and rejects replay
because membership returns true where the transcript binds false. The initial
state stays unchanged. The immutable successful state remains intact after the
failed replay.

This harness does not generate a cryptographic proof, verify a proof, submit a
transaction, or establish Preview acceptance. Those stages require native key
generation and transaction integration. The VM and preprocessing checks are
reported separately in the JSON output.

## Encoding references

- [Ledger 9 VM opcode field representation](https://github.com/midnightntwrk/midnight-ledger/blob/ledger-9.1.0.1/onchain-vm/src/ops.rs)
- [Ledger aligned-value field representation](https://github.com/midnightntwrk/midnight-ledger/blob/ledger-9.1.0.1/transient-crypto/src/fab.rs)
- [Proof preimage construction from native operations](https://github.com/midnightntwrk/midnight-ledger/blob/ledger-9.1.0.1/onchain-runtime-wasm/src/primitives.rs)

## Write an ordinary Merkle tree

Declare a root tree with `merkleTree claims : 2`. Use
`insertHash claims := disclose(leafHash)` to append a private Bytes32 digest.
`isFull claims as full` reads the current capacity flag, including after an
append in the same call. `reset claims` restores the default empty tree.
Depths range from 2 through 32. The native runtime rejects appends at capacity.
The compiler rejects a private leaf written without disclosure.

The [Lean fixture](../../tests/MerkleTree.lean) and the
[Compact oracle](../../tests/compact/ordinary-merkle.mjs) use the same
depth-two tree. The native test checks the four append roots and cursors,
the fifth append rejection, a changed capacity result, and exact reset.

```sh
lake build noctium Noctium:shared
mkdir -p build/experiments
scratch=$(mktemp -d "$PWD/build/experiments/ordinary-merkle.XXXXXX")
trap 'rm -rf -- "$scratch"' EXIT
.lake/build/bin/noctium compile tests/MerkleTree.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --output "$scratch/contract"
NOCTIUM_NATIVE_TEST_ARTIFACTS="$scratch/contract" \
  cargo +1.100.0 test --manifest-path runtime/Cargo.toml --locked \
    --no-default-features --features zkir-321 --test ordinary_merkle \
    ordinary_merkle_appends_match_compact_and_reset_exactly -- --ignored --exact
```

On the isolated Ledger 9.1.0.1 localnet, the native client finalized deployment
at height 4 and the first append at height 7. The receipt state bytes matched
the native runtime prediction at both steps. The pinned ZKIR 3.2.1 tool
reported k=8 and 231 rows for the append relation.
[Localnet receipt](ordinary-merkle-localnet-receipt.json)

### Check the current root

```lean
checkRoot claims against disclose(expectedRoot) as rootMatches
```

The expected root is a Field. The comparison binds a Boolean and uses the
state after earlier effects in the call. The operation leaves the tree
unchanged. If a guard skips the comparison, `rootMatches` is false and the
runtime skips the ledger read. Declare the release when the expected root or
guard depends on private data.

The depth-two fixture checks current and stale roots and inactive guards on
empty and populated trees. It also checks a root written earlier in the same
call. The native checker rejects a changed comparison result.

Set `COMPACTC_0361` and `COMPACT_RUNTIME_0210` to the absolute paths to Compact
0.36.1 and its Runtime 0.21.0 package. Run the reference oracle with the same
scratch directory.

```sh
"$COMPACTC_0361" --version | grep -E '^0\.36\.1 \(7fa3a117c'
test "$(node -p 'require(process.argv[1]).version' "$COMPACT_RUNTIME_0210/package.json")" = '0.21.0'
"$COMPACTC_0361" --skip-zk tests/compact/OrdinaryMerkle.compact "$scratch/compact"
mkdir -p "$scratch/node_modules/@midnight-ntwrk"
ln -s "$COMPACT_RUNTIME_0210" "$scratch/node_modules/@midnight-ntwrk/compact-runtime"
cp tests/compact/ordinary-merkle.mjs "$scratch/ordinary-merkle.mjs"
node "$scratch/ordinary-merkle.mjs"
```

The native client finalized deployment at height 4 and the combined append
and root check at height 7 on Ledger 9 localnet. Both receipts matched the
predicted state bytes. The combined relation used k=8 and 232 rows.
[Localnet receipt](ordinary-merkle-root-check-localnet-receipt.json)

The standalone `checkCurrent` call also finalized on the funded development
ledger. It returned true for the empty depth-two tree root and preserved
the 7,144-byte deployed contract state exactly. The pinned ZKIR 3.2.1 tool
reported K7 and 63 rows for this standalone relation. The transaction ID in the
receipt commits to the proved transaction. The matched replay covers depth two.
[Standalone receipt](standalone-ordinary-merkle-root-localnet-receipt.json)

To replay the standalone check, assemble one authenticated public bundle for
each operation exported by `NativeMerkleTree`. Use the compiled source above
and the pinned ZKIR 3.2.1 tool, with the current development ledger parameters.
Put the five bundles in directories named for the operations. The manifest
pin map is a JSON object from operation names to trusted SHA-256 digests.
[Public bundle recipe](portable-artifacts.md)

```sh
NOCTIUM_STANDALONE_MERKLE_ROOT_NODE=http://127.0.0.1:19944 \
NOCTIUM_STANDALONE_MERKLE_ROOT_BUNDLES="$scratch/bundles" \
NOCTIUM_STANDALONE_MERKLE_ROOT_MANIFESTS="$(cat "$scratch/pins.json")" \
NOCTIUM_STANDALONE_MERKLE_ROOT_PARAMETER_CACHE=/private/tmp/noctium-proof-params \
  cargo +1.100.0 test --manifest-path runtime/Cargo.toml --locked \
  --no-default-features --features zkir-321,localnet --lib \
  localnet::tests::standalone_merkle_root_check_finalizes_without_state_change \
  -- --ignored --exact --nocapture
```

## Write an ordinary Merkle tree at an index

A root Merkle tree accepts both a prehashed Bytes32 leaf and a Field leaf at a
UInt64 index. Declare the releases for the index and the value independently.

```lean
insertHashIndex claims at disclose(position) := disclose(leafHash)
insertFieldIndex claims at disclose(position) := disclose(leaf)
```

An indexed write updates the selected leaf and sets the append cursor to the
larger of its current value and `position + 1`. It accepts replacement when the
cursor reaches capacity. The active operation rejects an index at or above
`2 ^ depth`. An inactive guard skips the write, so later reads see the unchanged
tree. Field leaves use the Compact-compatible `mdn:lh` hash domain.

The [Lean fixture](../../tests/MerkleIndexed.lean) and the
[Compact oracle](../../tests/compact/IndexedMerkle.compact) cover sparse writes,
lower indices and replacements after the tree reaches capacity. The Rust test
checks the exact roots and append cursors with the pinned native checker.

```sh
lake build noctium Noctium:shared
mkdir -p build/experiments
scratch=$(mktemp -d "$PWD/build/experiments/indexed-merkle.XXXXXX")
trap 'rm -rf -- "$scratch"' EXIT
.lake/build/bin/noctium compile tests/MerkleIndexed.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --output "$scratch/contract"
NOCTIUM_NATIVE_TEST_ARTIFACTS="$scratch/contract" \
  cargo +1.100.0 test --manifest-path runtime/Cargo.toml --locked \
    --no-default-features --features zkir-321 --test ordinary_merkle \
    indexed_merkle_writes_match_compact_and_keep_the_highest_cursor -- --ignored
```

To run the oracle in the same scratch directory, use Compact 0.36.1 and make
`@midnight-ntwrk/compact-runtime` 0.21.0 available to Node.

```sh
compactc --skip-zk tests/compact/IndexedMerkle.compact "$scratch/compact"
cp tests/compact/indexed-merkle.mjs "$scratch/"
node "$scratch/indexed-merkle.mjs"
```

The native client finalized deployment at height 5 and an indexed Field write
at height 8 on Ledger 9 localnet. It matched the predicted state bytes for both
receipts. The indexed Field relation used k=13 and 2176 rows.
[Localnet receipt](indexed-ordinary-merkle-localnet-receipt.json)

## Retain and clear Merkle root history

Declare `historicMerkleTree claims : 2` in a contract to retain historical
roots. Use the regular Merkle append and indexed write syntax. Choose
`insertHash` for a prehashed Bytes32 leaf or `insertField` for a Field.
Each write records the resulting root. `checkRoot` tests membership in the
retained history, including a root recorded earlier in the same call.

```lean
insertField claims := disclose(leaf)
checkRoot claims against disclose(expectedRoot) as knownRoot
resetHistory claims
```

`resetHistory` keeps the current root and cursor. The full `reset` restores
the empty tree, cursor zero and the empty root in history. For a root-level
Field tree, writing an explicit zero at an index matches the Field default
operation in Compact. [Midnight ledger data types](https://docs.midnight.network/compact/reference/ledger-adt#historicmerkletreenat-value_type)

The [Lean fixture](../../tests/HistoricMerkle.lean) and
[Compact oracle](../../tests/compact/historic-merkle.mjs) cover the two
resets, membership across writes, sparse insertion, and replacement at
capacity. The native checker validates the generated relation and rejects a
changed membership result.

```sh
lake build noctium Noctium:shared
mkdir -p build/experiments
scratch=$(mktemp -d "$PWD/build/experiments/historic-merkle.XXXXXX")
trap 'rm -rf -- "$scratch"' EXIT
.lake/build/bin/noctium compile tests/HistoricMerkle.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --output "$scratch/contract"
NOCTIUM_NATIVE_TEST_ARTIFACTS="$scratch/contract" \
  cargo +1.100.0 test --manifest-path runtime/Cargo.toml --locked \
    --no-default-features --features zkir-321 --test merkle_history -- --ignored
```

On Ledger 9 localnet, deployment finalized at height 4. The combined
append and past-root membership call finalized at height 7. Both
receipts matched the predicted state bytes. The combined relation used
k=8 and 245 rows. [Localnet receipt](historic-merkle-localnet-receipt.json)

## Store Merkle trees inside a map

A typed map path selects an ordinary or historic tree. Create the parent maps
before resetting the final tree slot. A reset creates the empty tree at the
final key. Reads and writes require the tree to exist.

```lean
tree archives : Bytes32 => Native => HistoricMerkleTree 2
```

```lean
reset archives[disclose(owner)][disclose(bucket)]
insertField archives[disclose(owner)][disclose(bucket)] := disclose(leaf)
checkRoot archives[disclose(owner)][disclose(bucket)] against disclose(digest) as knownRoot
```

Declare the release for each private path key, leaf or root used by the
operation. The same call sees its earlier map initialization and writes.
Resetting one tree preserves both adjacent buckets and trees under another
owner.

The [Lean fixture](../../tests/NestedMerkle.lean) and
[Compact oracle](../../tests/compact/nested-merkle.mjs) check initialization,
sparse insertion, replacement at capacity, root membership and both resets.
The native fixture checks exact roots, cursors and retained history. It also
checks a missing parent, an invalid index and a tampered read result.

The Ledger 9 localnet finalized deployment at height 4 and the combined
setup and append of both trees at height 7. Both receipts matched the
predicted state bytes. The relation used k=13 and 2651 rows.
[Localnet receipt](nested-merkle-localnet-receipt.json)
