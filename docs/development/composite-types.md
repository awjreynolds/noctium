# Canonical composite types and source layouts

`Noctium.Types.Composite` defines the Lean-owned type/layout foundation for unit, scalar leaves, structural tuples, nominal structs, nominal enums, fixed vectors and fixed byte sequences. [Checked composite values](composite-values.md) adds construction, flattening, native relation constraints and a Rust/C++ value codec. The source ledger path below reuses these checked layouts for a narrow Native-only record case.

## Identity and ordering

Struct and enum declarations use qualified ASCII identities such as `Wallet.Note`. A repeated identity across either declaration kind rejects. Field and variant names must be unique within their declaration. Field order, variant order and tuple element order are significant. Nominal declarations compare by their declaration identity, even when their fields have identical layouts. Tuple and vector subtyping is structural and requires matching arity or length.

`CompositeSubtype` is a proof relation. It admits exact Native and Bool types, inclusive-maximum UInt widening only within the existing `ScalarPolicy.maxUint` bound, recursive tuple/vector relationships, exact fixed-byte lengths and exact nominal identities. It defines no implicit cast or physical-size-based conversion.

The full environment fingerprint sorts declaration records by canonical identity, then encodes fields and variants in source order. A type fingerprint encodes the type and its reachable declaration closure, so unrelated declarations do not perturb a specialization key. The versioned fingerprint is the full canonical descriptor string. It is not a cryptographic hash.

## Layout preflight

`CompositeEnv.validate` checks identities, duplicate names, unknown references, direct and indirect recursive layouts, scalar ranges, vector/byte bounds, expanded leaf counts and expanded node counts. It reports the declaration or referring field span. Forward references are allowed when acyclic. Fingerprint functions expect an environment which has passed this validation.

`checkedLayout` runs validation and bounded size preflight before constructing the finite inductive `Layout`. A `CheckedLayout` carries kernel-checked bounds for leaves, logical expanded values, and retained layout constructors. It proves equalities between all three preflight counts and recursive counts over the returned layout. `layout` returns the same checked layout value for callers which do not need the certificate fields. Fixed vector layouts keep one element layout, even at length zero. Preflight separately bounds logical value expansion and retained type-layout size, so zero-length nesting cannot multiply retained layout constructors without limit.

The local resource limits are 1,024 declarations, 1,024 elements or bytes per fixed sequence, 4,096 scalar leaves, 16,384 logical expanded nodes and 16,384 retained layout nodes. Callers can lower these limits for tests but cannot raise them above the published policy. These limits bound this compiler implementation. They do not claim a Compact or ZKIR language limit.

Zero-length vectors and byte sequences represent empty values in this source model and consume no scalar leaves. The pinned source-language and native artifact cases still need qualification before aggregate compilation is enabled.

## Scalar representation inventory

[`tests/composite-types/manifest.json`](../../tests/composite-types/manifest.json) records the current source layout leaves. Native, Bool and UInt each occupy one logical field slot; their respective canonicality/range constraints remain distinct. A byte occupies one UInt8-shaped field. An enum uses a checked UInt tag with maximum `variantCount - 1`, then a payload area sized to the largest variant. The proposed policy pads shorter variants with zero slots.

The enum tag and padding rules describe the source layout proposal. This package does not claim correspondence with the current native ledger ABI, ZKIR aggregate encoding or proof relation. Those rules need an explicit checked flattening transformation and native conformance evidence before Noctium enables aggregate deployment.

## Bytes32 map-key slice

The selected ZKIR 3.2.1 path supports fixed-width `Bytes32` map keys with scalar map values. Circuit inputs expand to 32 ordered UInt8 leaves. Native map operations retain all 32 bytes under the pinned Bytes32 alignment and two-field encoding, and public byte inputs bind each leaf into the Impact transcript. `runtime/tests/fixtures/generic-state/issue69-bytes32/321` is generated from `tests/Issue69Bytes32Map.lean`. `runtime/tests/bytes32_map.rs` checks membership, guarded missing-key reads, insertion, scalar reads, and distinct byte strings whose scalar reductions would collide.

This slice does not enable byte arithmetic, equality, scalar casts, byte-valued state, circuit outputs, or direct byte witness bindings. `CompositeType.bytes` keeps its checked aggregate layout and codec. A scalar `.bytes` layout is rejected; a 32-byte composite layout retains 32 leaves.

## Bytes32-keyed Native record cells

Recursive `tree` state also accepts a checked composite value at a Bytes32 key. The source fixture `tests/Issue69CompositeMap.lean` declares one named four-Native-field record, writes each field through explicit `disclose`, and reads the selected cell back as separate source-bound aliases. A guarded read of an absent cell binds four zero fields without evaluating its key payload. The next call reads the record from state.

The native plan emits `pushFields` and `popeqFields` with the existing checked schema JSON. The VM stores one `Cell` using `AlignedValue::concat`, with one segment count, the ordered Field descriptors, then the ordered field values. State reads require the declared schema and exact Field alignment. `runtime/tests/composite_map.rs` covers insertion, replacement, readback, an untouched second key, skipped and active read groups, malformed leaf counts and altered transcript leaves.

The IR ledger gate accepts nonempty layouts made only from Native scalar leaves and their existing tuple, structure or vector containers. The current source syntax exposes inline named records. This slice does not enable mixed scalar records, bytes, enums or general aggregate operations. Ciphertext-shaped storage does not establish Jubjub point validity or ElGamal correctness; those remain in the cryptography workstream.

## Nested Bytes32 scalar maps

The native ledger source surface now accepts recursive map state through `tree`, with typed bracket paths for membership, scalar reads and writes. `tests/Issue69NestedCounter.lean` models `_escrowSpendEpochs` as Bytes32 owner → Bytes32 spender → UInt64 count. It checks each parent with `member`, creates an absent owner map with explicit `insert ... := emptyMap`, inserts a missing scalar count, increments with checked UInt arithmetic and reads the result again. Empty-map assignment replaces the selected map entry, so callers must guard it with membership when they intend initialization. The fixed `tree` source declaration currently accepts two map levels and scalar leaves; the IR schema is recursive so later value kinds do not change legacy `StateKind.map`.

Native plans use `indexPath` for typed key paths. Empty-map creation indexes the parent with `pushPath`, pushes the final key and native map tag `2`, runs `new`, then `insert`. Scalar paths use aligned keys and the existing native `insert` update behavior. The focused source/native fixture lives under `runtime/tests/fixtures/generic-state/issue69-nested/321`; broader records, lists and Counter ADT semantics remain outside this slice.

## Cases and check

`tests/CompositeTypes.lean` contains the TYC-IDENTITY, TYC-ORDER, TYC-LENGTH, TYC-CYCLE and TYC-SUBTYPE cases. It checks insertion-order-stable fingerprints, field-order changes, nominal distinction, forward references, cycles, missing names, duplicate declarations, scalar bounds, sequence limits, enum tags/payloads and recursive UInt widening proofs. Its S8 nested zero-vector regression has three logical expanded nodes and 1,021 retained layout constructors. A 100-node retained-layout limit rejects it before layout construction. At a 1,021-node bound, the returned counts are `(expandedNodes, layoutNodes, value.expandedNodeCount, value.nodeCount) = (3, 1021, 3, 1021)`.

```sh
lake build Noctium.Types.Composite
lake env lean tests/CompositeTypes.lean
```

## Nominal UInt fields in ledger records

Declare field types with `noctium_uint_type` when equal-width integers have
different meanings. Record reads, writes and List operations check their
declared identities, including the three-key Map paths in the fixture.
Use an explicit checked cast to convert from an unbranded UInt.
[Nested record fixture](../../tests/NominalUIntNestedRecords.lean)

`headOrDefault` followed by `returnMaybe` emits a checked logical record view.
The plan records alias names and maxima in `nominalUIntFields` at paths such
as `["value", "amount"]`. Native transcript fields retain their existing
encoding. The runtime checks the declared UInt maximum at each selected path.
Compact 0.36.1 and the native checker agree on both the empty-list default
and present `{amount = 19, count = 7, active = true}` payload.
[Lean fixture](../../tests/NominalRecordMaybe.lean) · [Native checker](../../runtime/tests/nominal_record_maybe.rs)

## Nested owner/spender records

`tree escrow : Bytes32 => Bytes32 => struct EscrowRecord { ... }` places a
checked Native-field record beneath two independent native map keys. Two-key
`read`, `write` and `insert ... := fields(...)` use the same recursive path and
record encoding as the one-key case. Outer maps require explicit initialization.
Each key and each stored field still needs disclosure when derived from private
values.

[`tests/NestedEscrow.lean`](../../tests/NestedEscrow.lean) uses an 11-field record
shaped for owner/spender ciphertexts and a memo. A focused native sequence checks
read-after-write, replacement, two spender keys, a second owner, preservation of
neighboring records and rejection of a missing field. Each record remains one
aligned Cell. Native coordinate fields alone establish no curve validity or
encryption property. Mixed typed records, lists and full token integration remain
separate work. No new keys, proofs or deployments were generated.

## Map defaults

`insertDefault balances[key]` inserts the declared value's default or replaces
the existing entry. `insertDefault balances[owner][key]` requires the owner map
to exist. Defaults use the existing scalar and record layouts, empty Map, Set
and List state, zero Counters, and empty ordinary or historic Merkle Trees.
Inserting a historic tree default starts with empty root history. Explicit
`reset` records root zero in history.

`when enabled insertDefault balances[owner][key]` skips the path and write when
disabled. Private keys and guards require explicit disclosure.
[Source example](../../tests/NativeMapDefault.lean)

## Typed Merkle leaves

`merkleTree claims : 2 of Bool` declares a depth-two tree of Boolean leaves.
`tree archives : Bytes32 => HistoricMerkleTree 2 of Bytes 3` declares one
historic tree per key. Leaf types include Native, Bool, bounded UInt and fixed
Bytes. A declaration with only a depth uses Native.

Use `insertLeaf claims := disclose(eligible)` to append,
`insertLeafIndex claims at position := disclose(eligible)` to write at an
index, and `insertLeafDefault claims at position` to write a hashed default.
These use the declared FAB byte layout and the ledger leaf hash. The explicit
`insertHash` and `insertHashIndex` forms accept a precomputed digest.
[Source example](../../tests/TypedMerkleLeaves.lean)

A Merkle leaf can use a named record with nested records of supported fields.

```lean
merkleTree claims : 2 of struct ClaimLeaf {
  tag : Bytes 3
  details : struct ClaimMeta {
    approved : Bool
    count : UInt 16
  }
}
```

Pass scalar fields in depth-first declaration order, for example
`insertLeaf claims := fields(disclose(tag), disclose(approved), disclose(count))`.
The indexed default hashes the scalar defaults in the same order. The checked
source layout limits the full leaf preimage to 1,024 bytes, including the hash
domain. Curve-valued record fields need separate evidence. The state artifact
describes the Merkle tree. A host reading a structured leaf path supplies its
own leaf schema.
[Flat record example](../../tests/RecordMerkleLeaves.lean) · [Nested record example](../../tests/NestedRecordMerkleLeaves.lean)

A standalone JubjubPoint leaf hashes its two canonical field coordinates with
the same ledger leaf domain. Its indexed default uses the curve identity.
[Source fixture](../../tests/JubjubMerkleLeaves.lean)

The ZKIR 3.2.1 foreign append check uses Base and Scalar value `1` and generator
points for Secp256k1, Secp256r1, and Curve25519. All nine leaf digests and roots
match the pinned Compact 0.36.1 vectors. Each cursor advances to `1`, and the
native runtime rejects an append to a full tree.
[Source](../../tests/ForeignMerkleLeaves.lean) · [Native check](../../runtime/tests/foreign_merkle_leaves.rs)
