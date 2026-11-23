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

Noctium also checks a self-recipient List prepend under two Bytes32 Map
parents. The emitted ZKIR 3.2.1 relation accepts booked index 42 ahead of
index 31 and preserves the neighboring bucket and the other owner's List.
Missing parents, a missing booking and a wrong-recipient booking reject
in the native query context. The matched Compact 0.36.1 and Runtime 0.21.0
case uses two owners and two groups. It checks the same List order and
sibling preservation, assigned indices 0 and 1, and the same rejection
cases. The index-1 case mints a distinct output before the selected coin
in the same circuit execution. [Compact runtime case](../../tests/compact/two-parent-qualified-coin-list.mjs)
[Lean fixture](../../tests/TwoParentQualifiedCoinList.lean) ·
[Native check](../../runtime/tests/two_parent_qualified_coin_list.rs)

The four-parent Noctium fixture accepts a List below four existing Bytes32
Maps. The native ZKIR 3.2.1 check prepends a coin booked to an explicit
contract at index 42 ahead of the self-recipient coin at index 31. Two
seeded sibling Lists stay intact. Missing and wrong bookings and absent
paths reject. The direct pinned fragment uses context `Dup` depth 15
at four parents. The root and two-parent checks pass on the same compiler build. [Lean fixture](../../tests/FourParentQualifiedCoinList.lean) ·
[Native query-context test](../../runtime/tests/four_parent_qualified_coin_list.rs)

The matching Compact 0.36.1 and Runtime 0.21.0 case also prepends beneath
four Bytes32 Map parents. The selected List stores the new booked index
1 ahead of index 0, and two seeded siblings retain their records. The
case rejects missing and wrong bookings and an absent path.
[Compact fixture and runner](../../tests/compact/four-parent-qualified-coin-list.mjs)

Two focused four-parent List calls finalized on development Ledger
9.1.0.1 at blocks 72,222 and 72,225. The selected List held booked indices
48 and 47 in newest-first order, with three sibling Lists empty. Read-only
recovery matched the two stored coin commitments to their contract-owned
outputs in the finalized extrinsics. The normal receipt observer returned
a response error on the second call. Independent Zswap replay and the
observer error remain under investigation. [Finalized evidence](funded-four-parent-coin-list-localnet-receipt.json) ·
[Observer ticket](https://github.com/awjreynolds/noctium/issues/791)

The deeper List route qualifies the coin before reading the List, then
rebuilds cached Map ancestors one key at a time. The emitted ZKIR 3.2.1
case passes at thirteen Bytes32 Map parents, the ordinary native List
schema limit. It checks index 42 ahead of 31, an unchanged seeded sibling,
and rejection of missing or wrong bookings and a missing path. Source
and native-plan admission reject fourteen. The four-parent route and
the existing fourteen-parent booked Map case pass the native checks.
[Boundary fixture](../../tests/DeepBookedCoinListBoundary.lean) ·
[Native query-context check](../../runtime/tests/four_parent_qualified_coin_list.rs)

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

Noctium source admits qualified Set insertion under up to five Bytes32 Map
parents. The ZKIR 3.2.1 fixture checks self-recipient insertion at depth two
and explicit contract-recipient insertion at depth five. It stores the
booked indices 41 and 42, preserves the seeded sibling Sets, and rejects
missing parents or missing and wrong-recipient bookings. A sixth parent
rejects at source and native plan admission. The root and one-parent
artifacts match the earlier bytes. The deeper cases use a native query
context. [Lean fixture](../../tests/DeepQualifiedCoinSet.lean) ·
[Native query check](../../runtime/tests/qualified_coin_set.rs)

The pinned Compact 0.36.1 and Runtime 0.21.0 query test also inserts under
five Bytes32 Map parents. It adds a selected Set member with booked index 1
after a distinct transaction-local mint, keeps the original member and
five seeded siblings, and rejects missing bookings, wrong-recipient
bookings and an absent Set path. [Compact fixture and runner](../../tests/compact/five-parent-qualified-coin-set.mjs)

The focused Noctium self-mint finalized on isolated Ledger 9.1.0.1. The
selected Set stored the complete qualified record at booked index
46, matching the finalized contract-owned Zswap output. The three
sibling Sets stayed empty. Missing and mismatched offers rejected before
submission. The tip relation measured K14 and 12,824 rows with pinned
ZKIR 3.2.1. [Source fixture](../../tests/FundedFiveParentQualifiedCoinSet.lean) ·
[Finalized receipt](funded-five-parent-coin-set-localnet-receipt.json)

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

A two-parent source case selects both existing Bytes32 Maps before writing
the independent leaf key. The native query checks insertion, replacement,
missing parents at both levels, booking recipient checks and unchanged
siblings. The emitted Lean circuit passes the pinned native relation
checker against the same query context. Compact 0.36.1 and Runtime 0.21.0
also completed a two-parent insertion and overwrite in their query context.
[Lean fixture](../../tests/DeepBookedCoinMap.lean) ·
[Compact runner](../../tests/compact/qualified-coin-collections.mjs)

The original Impact sequence uses a four-bit `Dup` index of
`5 + 2 * parentCount` for up to five parents. From six to fourteen, the
native sequence reads the transaction booking before traversing the Map
path. It writes the leaf and rebuilds each parent with cached lookups.
The Lean compiler binds the expanded sequence to the circuit transcript.
The six- and fourteen-parent source artifacts pass the pinned native circuit
and query checks. At fourteen parents, the insert consumes 99 Impact groups,
uses the booked index, and preserves every sibling Map. A fifteen-parent path
rejects at both admission boundaries. The funded Ledger evidence reaches six
parents.
[Six-parent Lean fixture](../../tests/DeepBookedCoinMapSix.lean) ·
[Fourteen-parent Lean fixture](../../tests/DeepBookedCoinMapBoundary.lean) ·
[Wider lowering](https://github.com/awjreynolds/noctium/issues/716)

A pinned five-parent Compact probe completed insertion and overwrite. The
reduced six-parent Compact probe reached its 180-second timeout with no
artifacts or compiler diagnostic. The six-parent runtime comparison remains
open. [Compact probe result](https://github.com/awjreynolds/noctium/issues/716)

The query-context checks cover overwrite and missing owners. The funded
fixture below exercises independent-key insertion and overwrite on Ledger 9.

## Funded Maps, Set and List

The fixture initializes two Bytes32 owners, self-mints five units, then
stores the booked coin at the same independent key in a root Map and the
selected owner's nested Map. The selected owner's Set and List also store
the coin. Ledger 9.1.0.1 finalized the call at block 68,970. Both Maps, the
Set member and the List head match the finalized Zswap coin at index 37.
The other owner's buckets stayed empty. The harness rejects missing and
mismatched offers before submission. [Lean fixture](../../tests/FundedNestedQualifiedCoinCollections.lean)
· [Finalized receipt](funded-independent-coin-maps-localnet-receipt.json)

A second run used the same bundles and called the same entrypoint twice on
one deployment. The calls finalized at blocks 69,242 and 69,245. The root
and owner Maps kept one entry each at the same key and replaced coin index
38 with index 39. Both coins remained in the nonce-keyed Map, the owner's
Set and the owner's List, with the replacement at the head. The other
owner's buckets stayed empty. The recorded block hashes and three contract
state digests matched direct queries at the recorded blocks.
[Overwrite receipt](funded-coin-map-overwrite-localnet-receipt.json)

The two-parent fixture initializes both groups under each owner. Its calls
finalized at blocks 69,511 and 69,514. The same independent leaf key
stored index 40 and then index 41 in the selected owner and group Map.
The root Map made the same replacement. The nonce Map, Set and List
retained both coins. The other group and both groups under the other
owner stayed empty. Exact inclusion and finalization hashes and the three
state digests matched direct node queries.
[Two-parent Lean fixture](../../tests/FundedDeepQualifiedCoinMaps.lean) ·
[Ledger receipt](funded-two-parent-coin-maps-localnet-receipt.json)

The two-parent List fixture adds four Lists under two owners and two
groups. Two funded calls finalized at blocks 71,239 and 71,242. The
selected List stores the two contract-owned Zswap outputs in newest-first
order, with assigned indices 45 and 44. The other three Lists stayed
empty. Direct node queries matched four inclusion and finalization
identities and three retained state digests.
[Lean fixture](../../tests/FundedTwoParentQualifiedCoinList.lean) ·
[Ledger receipt](funded-two-parent-coin-list-localnet-receipt.json)

The six-parent fixture initializes a chain below each owner and group.
Its two calls finalized at blocks 69,757 and 69,760. The independent
leaf key stored index 42 and then index 43 in the selected chain.
All sibling leaves stayed empty. The nonce Map, Set and List retained
both coins, and direct node queries matched the recorded inclusion and
finalization hashes and three state digests. Six is the deepest funded
path verified here.
[Six-parent funded fixture](../../tests/FundedSixParentQualifiedCoinMaps.lean) ·
[Ledger receipt](funded-six-parent-coin-maps-localnet-receipt.json)

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

Set `NOCTIUM_FUNDED_MAP_OVERWRITE=1` for a two-call run. For the two-parent
run, select bundles from `FundedDeepQualifiedCoinMaps` or
`FundedTwoParentQualifiedCoinList` and also set
`NOCTIUM_FUNDED_TWO_PARENT_MAP=1`. For six parents, select
`FundedSixParentQualifiedCoinMaps` bundles and set
`NOCTIUM_FUNDED_SIX_PARENT_MAP=1` instead. Run against a
dedicated development chain to keep Zswap booking indices stable during
funding and submission.

The [pinned VM opcode source](https://github.com/midnightntwrk/midnight-ledger/blob/a2b30128ca4b660b73a068e29b56b48ede8c9a74/onchain-vm/src/ops.rs)
defines opcode names and immediate encoding. The pinned runtime exports the
corresponding `Cell_write_coin!`, `Set_insert_coin!` and `List_push_front_coin!`
program fragments. [Native fragments](https://github.com/midnightntwrk/midnight-ledger/blob/a2b30128ca4b660b73a068e29b56b48ede8c9a74/onchain-runtime/vendored/program_fragments.rs)
