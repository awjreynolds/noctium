# Compact qualified shielded coin collections

The reference runs Compact 0.36.1 (`7fa3a117c`) with runtime 0.21.0.
Each case qualifies the same five-unit coin as a self-contract recipient.
The receive creates one booked output, and the selected Cell, Set or List
stores the matching nonce, color, amount and index `0`. Each method rejects
the same coin without a booking and leaves all three containers unchanged.
The runner checks the booking and resulting state independently for each case.
[Pinned compiler documentation](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/doc/ledger-adt.mdx)

In each relation the guarded receive precedes a separate unguarded storage
sequence. That sequence pushes the tagged recipient's coin commitment as two
FAB fields (`%hash.17`, `%hash.16`) and looks up the current transaction's
allocated index with `0x61 0x01 0x01 0x01 -0x01`. The next push carries the
two aligned nonce fields, two color fields and one amount field (`%coin.0`
through `%coin.4`). `0x40` and `0x17 0x5b` join the coin with its index.
The storage suffix differs by container.

| Method | Impact instructions | Storage suffix after qualification |
| --- | ---: | --- |
| Cell `writeCoin` | 20 | Direct `0x91` insert |
| Set `insertCoin` | 22 | `0x11 0x00` marker, `0x91` insert, `0xa1` cached reinsertion |
| List `pushFrontCoin` | 33 | Cached reinsertion and list metadata writes through `0xa1` and `0xa2` |

The [fixture](../../tests/compact/QualifiedCoinCollections.compact) and
[runner](../../tests/compact/qualified-coin-collections.mjs) provide reference
evidence. Noctium lowers the root Cell, Set and List routes for a coin already booked
to the current contract. The [Set fixture](../../runtime/tests/qualified_coin_set.rs)
checks the emitted relation and the native state, including indices 17 and 42,
duplicate insertion, and missing or wrong-recipient bookings. The
[List fixture](../../runtime/tests/qualified_coin_list.rs) checks prepending
index 42 ahead of index 17 and the same booking boundary. The List lowering
pushes the node before its key so the cached insert receives the correct operands.
These checks use a native query context.

A funded Ledger 9 run stored one self-minted coin in a Map, root Cell, root
Set, and one-element root List in the same call. The test compares the Map,
Cell and Set records and the List head with the finalized contract-owned
output, including the assigned index. It also checks the List's empty tail
and length of one. Repeated List operations and finalized calls for other
recipient types remain open.
[Localnet receipt](shielded-coin-collections-localnet-receipt.json)

The [explicit-recipient case](../../tests/compact/explicit-booked-coin-recipients.mjs)
checks a booked wallet and a different contract through each collection.
Noctium's [matching source](../../tests/QualifiedCoinRecipient.lean) binds the
recipient tag and bytes to the ledger-allocated index. The native runtime
checks all six emitted relation cases at index `41` and rejects a missing
booking, a different address, or the same bytes under the other recipient tag.
The native check uses a query context with prebooked outputs.

The nested Set fixtures initialize two Bytes32 owners and insert the same
three coin values in owner order A, B, A. Compact and Noctium retain 5 and 7
under A and 11 under B. Each retains the index assigned by its query context.
The selected owner must exist. An absent owner, missing booking or wrong
recipient booking rejects without a Set write.
[Compact case](../../tests/compact/qualified-coin-collections.mjs),
[Noctium source](../../tests/NestedQualifiedCoinSet.lean), and
[native query-context check](../../runtime/tests/qualified_coin_set.rs).

The nested storage suffix uses index opcode `0x71` with the slot and owner
key, context duplicate `0x36`, and two-level cached reinsertion `0xa2`.
The native checker accepts both implicit and explicit contract recipient
paths. The root Set and root explicit-recipient artifacts match their previous
bytes. The nested Set checks use the query context and emitted relation.

## Booked coin Map

`insertShieldedCoinMap` writes an already booked coin into a root Bytes32 Map.
The key and nonce are independent. The recipient tag and address select the
commitment whose index the ledger assigned. Compact and Noctium accept
replacement at the same key. A missing or wrong-recipient booking rejects,
and the insertion adds no receive claim. The Noctium query-context test
checks both wallet and contract recipients. The emitted wallet case passed
the native relation check. The pinned ZKIR tool measured K13 and 6,856 rows.
[Lean fixture](../../tests/BookedCoinMap.lean) ·
[Compact fixture and runner](../../tests/compact/qualified-coin-collections.mjs)

The nested fixture selects one existing Bytes32 owner before inserting or
replacing the inner key. Both runtimes retain the assigned index and leave the
other owner's Map unchanged. Missing owners reject. The Impact suffix uses
`0x71` for the owner path, `0x37` for the context lookup and `0xa2` for cached
reinsertion. A private owner requires explicit disclosure because the path
appears in the public transcript. [Nested Lean fixture](../../tests/NestedBookedCoinMap.lean)

The query-context checks cover overwrite and missing owners. The funded
fixture below checks the first independent-key insertion on Ledger 9.

## Funded Maps, Set and List

The fixture initializes two Bytes32 owners, self-mints five units, then
stores the booked coin at the same independent key in a root Map and the
selected owner's nested Map. The selected owner's Set and List also store
the coin. Ledger 9.1.0.1 finalized the call at block 68,970. Both Maps, the
Set member and the List head match the finalized Zswap coin at index 37.
The other owner's buckets stayed empty. The harness rejects missing and
mismatched offers before submission. [Lean fixture](../../tests/FundedNestedQualifiedCoinCollections.lean)
· [Finalized receipt](funded-independent-coin-maps-localnet-receipt.json)

Compile the fixture for the pinned ZKIR 3.2.1 profile and assemble both
entrypoint bundles. Use the compiler revision and fixture hash in the receipt
for the pinned build. The initializer measured 284 rows at K9. The funded
`tip` measured 24,829 rows at K15. The localnet test uses the manifest pins
and a parameter cache with the pinned DUST and Zswap output material.
[Bundle setup](portable-artifacts.md) · [Localnet setup](../../scripts/localnet/README.md)

The earlier Set and List run has its own receipt. [Set and List receipt](nested-qualified-coin-collections-localnet-receipt.json)

```sh
NOCTIUM_RECEIVE_NODE=http://127.0.0.1:19944 \
NOCTIUM_RECEIVE_PARAMETER_CACHE=/path/to/verified/parameter-cache \
NOCTIUM_NESTED_QUALIFIED_COIN_COLLECTIONS_BUNDLES=/path/to/bundle-parent \
NOCTIUM_NESTED_QUALIFIED_COIN_COLLECTIONS_MANIFESTS='{"initializeOwners":"INITIALIZER_SHA256","tip":"TIP_SHA256"}' \
  cargo +1.100.0 test --locked --manifest-path runtime/Cargo.toml --lib \
  --no-default-features --features zkir-321,localnet \
  localnet::shielded_receive::tests::funded_shielded_receive_localnet -- --exact --ignored --nocapture
```

The [pinned VM opcode source](https://github.com/midnightntwrk/midnight-ledger/blob/a2b30128ca4b660b73a068e29b56b48ede8c9a74/onchain-vm/src/ops.rs)
defines opcode names and immediate encoding. The pinned runtime exports the
corresponding `Cell_write_coin!`, `Set_insert_coin!` and `List_push_front_coin!`
program fragments. [Native fragments](https://github.com/midnightntwrk/midnight-ledger/blob/a2b30128ca4b660b73a068e29b56b48ede8c9a74/onchain-runtime/vendored/program_fragments.rs)
