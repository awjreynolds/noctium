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
evidence. Noctium lowers the root Cell and Set routes for a coin already booked
to the current contract. The [Set fixture](../../runtime/tests/qualified_coin_set.rs)
checks the emitted relation and the native state, including indices 17 and 42,
duplicate insertion, and missing or wrong-recipient bookings. These checks use
a native query context. Finalized Set execution and the List route remain open.

The [pinned VM opcode source](https://github.com/midnightntwrk/midnight-ledger/blob/a2b30128ca4b660b73a068e29b56b48ede8c9a74/onchain-vm/src/ops.rs)
defines opcode names and immediate encoding. The pinned runtime exports the
corresponding `Cell_write_coin!`, `Set_insert_coin!` and `List_push_front_coin!`
program fragments. [Native fragments](https://github.com/midnightntwrk/midnight-ledger/blob/a2b30128ca4b660b73a068e29b56b48ede8c9a74/onchain-runtime/vendored/program_fragments.rs)
