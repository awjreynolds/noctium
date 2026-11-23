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

The [pinned VM opcode source](https://github.com/midnightntwrk/midnight-ledger/blob/a2b30128ca4b660b73a068e29b56b48ede8c9a74/onchain-vm/src/ops.rs)
defines opcode names and immediate encoding. The pinned runtime exports the
corresponding `Cell_write_coin!`, `Set_insert_coin!` and `List_push_front_coin!`
program fragments. [Native fragments](https://github.com/midnightntwrk/midnight-ledger/blob/a2b30128ca4b660b73a068e29b56b48ede8c9a74/onchain-runtime/vendored/program_fragments.rs)
