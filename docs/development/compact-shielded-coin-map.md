# Shielded coin map comparator

The Compact 0.36.1 fixture uses language 0.28 and runtime 0.21.0. Its compiler source pin is `7fa3a117c5e7efe9d2c51da04263e5f0b3509144`. The comparison profile pairs with Midnight Ledger 9.1.0.1. The contract follows the private tip jar receive path. It rejects an existing nonce, calls `receiveShielded(disclose(coin))`, then inserts the coin into `Map<Bytes<32>, QualifiedShieldedCoinInfo>` under the nonce with `kernel.self()` as recipient.

The focused oracle compiles with `--skip-zk` and checks the in-memory Compact runtime. A store-only circuit on a fresh context fails with `Coin commitment not found` and leaves both the receive effects and map empty. A successful call records one shielded receive and one output to the contract. The map stores the submitted `nonce`, `color`, and `value` plus `mt_index: 0n`, resolved from that call's newly created output. A second call with the same nonce fails before it records another receive.

Run with the pinned compiler and runtime directories:

```sh
node tests/compact/shielded-coin-map.mjs /path/to/compactc-0.36.1 /path/to/compact-runtime-0.21.0
```

The in-memory Compact check uses a synthetic `ShieldedCoinInfo`. The Noctium localnet run below exercises proof generation and transaction acceptance.

The pinned Ledger runtime books output commitments before a contract call. The query context exposes the assigned index in its commitment table. The receive effect claims the commitment, and the Map write reads the index from the context and appends it to the stored coin value. A native VM probe ran the same operation sequence with context indices `0` and `42`. It stored the corresponding index and rejected a missing commitment without changing the input state or effects.

The Compact-generated Map write uses `Dup 5` to reach the context for this top-level Map. The vendored `Map_insert_coin!` fragment expands to `Dup 4` for the same path and fails the native probe with `ExpectedCell(null)`. The checked operation sequence uses the generated stack offset. [Native receive and Map qualification](https://github.com/awjreynolds/noctium/issues/205)

Noctium exposes this path as `receiveShieldedToMap(pot, disclose(nonce), disclose(color), disclose(amount))`. The native fixture checks the emitted ZKIR 3.2.1 and Impact transcript, including index 42 supplied by the query context. It also checks duplicate and missing commitments without a funded transaction.

```sh
lake exe noctium compile tests/ShieldedReceive.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --output build/shielded-receive
NOCTIUM_SHIELDED_RECEIVE_DIR="$PWD/build/shielded-receive" \
  cargo test --locked --manifest-path runtime/Cargo.toml \
  --no-default-features --features zkir-321 --test shielded_receive -- --include-ignored
```

## Deep booked Map writes

Noctium qualifies the coin before traversing the Map path and rebuilds
each cached parent separately. The emitted ZKIR 3.2.1 fixture checks
insertion at fourteen Bytes32 Map parents, including the exact booked
index, sibling preservation and rejection of invalid bookings and
missing parents. Source admission rejects fifteen parents. Two funded
six-parent calls finalized at blocks 69,757 and 69,760 and stored
indices 42 and 43 at the same key. [Boundary fixture](../../tests/DeepBookedCoinMapBoundary.lean) ·
[Funded receipt](funded-six-parent-coin-maps-localnet-receipt.json)

Compact 0.36.1 and Runtime 0.21.0 passed insertion and overwrite through
five parents. The reduced six-parent source declared seven nested Maps.
The pinned compiler reached the 180-second limit with `--skip-zk` before
emitting a relation. Upstream reproduced exponential memory growth from
the same nesting depth with an empty circuit on Compact 0.34.100. The
six-parent comparison stays open in a separate ticket. [Recorded timeout](https://github.com/awjreynolds/noctium/issues/716#issuecomment-7095636326) ·
[Upstream compiler issue](https://github.com/LFDT-Minokawa/compact/issues/734) ·
[Six-parent comparison ticket](https://github.com/awjreynolds/noctium/issues/797)

## Funded Noctium localnet receipt

The Lean fixture mints five units and receives one contract-owned output in the same guaranteed section. The Rust host books its index against the finalized Zswap state, proves the contract call and output, and funds fees from the development DUST wallet. Before funding, the host rechecks the booking and the initial contract state against the latest finalized snapshot.

Ledger 9.1.0.1 finalized the call at block 140. The stored coin matched the nonce, color, value and Ledger index 29. The native host rejected missing and mismatched offers before submission and checked the Map remained unchanged. The ZKIR 3.2.1 circuit used k=13 and 6,646 rows. Wallet-funded receive is a separate focused test below, with no receipt recorded here. [Receipt](shielded-receive-localnet-receipt.json)

Compile `tests/FundedShieldedReceive.lean` with the ZKIR 3.2.1 target above and select `FundedShieldedReceive.tip.zkir` and its Impact plan in the bundle recipe. Generate keys with the pinned ZKIR CLI and use the isolated node's Ledger parameters. [Bundle setup](portable-artifacts.md) · [Localnet setup](../../scripts/localnet/README.md)

```sh
NOCTIUM_RECEIVE_NODE=http://127.0.0.1:19944 \
NOCTIUM_RECEIVE_PARAMETER_CACHE=/path/to/verified/dust/zswap-and-srs-cache \
NOCTIUM_RECEIVE_BUNDLE=/path/to/funded-receive-bundle \
NOCTIUM_RECEIVE_MANIFEST_SHA256=YOUR_MANIFEST_SHA256 \
  cargo test --locked --manifest-path runtime/Cargo.toml --lib \
  --no-default-features --features zkir-321,localnet \
  funded_shielded_receive_localnet -- --ignored --nocapture
```

## Wallet-funded receive into a Map

The focused test follows one wallet-owned input into the deposit contract's `pot` Map. `ShieldedSpend.tip` mints and books a seed coin. `ShieldedSpend.spend` sends it to a temporary Rust wallet, which applies the two proved offers to its local wallet state and constructs the spend input. The wallet keeps its keys and state and gives the receive host the input preimage. It checks that the input belongs to a wallet, uses the guaranteed segment, and matches the contract output's token and value.

The host creates one contract-owned output, applies the offer to the current Zswap snapshot to obtain its Ledger index, and passes that index into the contract proof context. It binds the exact offer before signing. After finalization, the test checks the `pot` entry, output commitment and owner at that index, plus the spent input nullifier. It also checks that a changed opening and replayed input do not alter the finalized Map.

Ledger 9.1.0.1 finalized the wallet-funded receive at block 480. The Map held the five-unit contract output at index 42, and the finalized Zswap state included the spent wallet input nullifier. The harness rejected unequal value and replay before submission. [Receipt](wallet-shielded-receive-localnet-receipt.json)

Export the 3.2.1 ledger artifacts from `tests/ShieldedSpend.lean` and `tests/ShieldedReceive.lean`. Prepare authenticated bundles for `ShieldedSpend.tip`, `ShieldedSpend.spend` and `ShieldedReceive.tip`, using the same development node and ledger parameters. [Bundle setup](portable-artifacts.md)

```sh
NOCTIUM_WALLET_RECEIVE_NODE=http://127.0.0.1:19944 \
NOCTIUM_WALLET_RECEIVE_PARAMETER_CACHE=/path/to/verified/parameter-cache \
NOCTIUM_WALLET_RECEIVE_DEPOSIT_BUNDLE=/path/to/deposit-bundle \
NOCTIUM_WALLET_RECEIVE_DEPOSIT_MANIFEST_SHA256=YOUR_DEPOSIT_MANIFEST_SHA256 \
NOCTIUM_WALLET_RECEIVE_SEED_TIP_BUNDLE=/path/to/seed-tip-bundle \
NOCTIUM_WALLET_RECEIVE_SEED_TIP_MANIFEST_SHA256=YOUR_SEED_TIP_MANIFEST_SHA256 \
NOCTIUM_WALLET_RECEIVE_SEED_SPEND_BUNDLE=/path/to/seed-spend-bundle \
NOCTIUM_WALLET_RECEIVE_SEED_SPEND_MANIFEST_SHA256=YOUR_SEED_SPEND_MANIFEST_SHA256 \
  cargo test --locked --manifest-path runtime/Cargo.toml --lib \
  --no-default-features --features zkir-321,localnet \
  funded_wallet_shielded_receive_localnet -- --ignored --nocapture
```

## Wallet-funded standalone receive

`FundedRawShieldedClaim.helperClaimReceive` calls the checked raw receive
helper with the exact contract-owned output commitment. The isolated
Ledger 9.1.0.1 chain finalized the call at block 66. The test confirmed the
output owner and commitment at index 30, the wallet input nullifier, and
unchanged contract state. Changing one digest byte rejected before submission.
[Receipt](funded-raw-shielded-receive-localnet-receipt.json)

Use the same development node, parameter cache and seed bundles as the
wallet-funded Map test above. Compile `tests/RawShieldedClaims.lean` for
ZKIR 3.2.1 and assemble a bundle for the single exported
`FundedRawShieldedClaim.helperClaimReceive` operation. Set
`NOCTIUM_RAW_SHIELDED_CLAIMS_HELPER_RECEIVE_BUNDLE` and
`NOCTIUM_RAW_SHIELDED_CLAIMS_HELPER_RECEIVE_MANIFEST_SHA256` in place of the
Map deposit bundle variables. Run the same filtered Cargo command with
`funded_wallet_raw_shielded_receive_helper_localnet` as the test name.

The guarded spend and nullifier helper also matches Compact 0.36.1. Its inactive
branch produces no claim. Its active branch retains two distinct digests per
kind and deduplicates repeat claims. The native checker validates the exact
digests in the emitted ZKIR. [Paired runner](../../tests/compact/raw-shielded-claims.mjs)

## Whole-coin spend from a Map

`tests/ShieldedSpend.lean` defines two entries. `tip` mints and receives five units into the Map. `spend` consumes the recorded coin, derives its nullifier and a commitment to one user-owned output, then removes the old key. The native host builds the spend proof from the coin's assigned index and the finalized Zswap tree. The Compact runner also checks the exact effects, output nonce, Map removal and replay rejection for a deterministic full-value send.

Ledger 9.1.0.1 finalized this native spend at block 372. The recipient decrypted the five-unit output at Ledger index 29, and the finalized Map no longer contained the input coin. The harness rejected a mismatched nonce and a replay before submission. The spend circuit used k=14 and 12,770 rows. [Receipt](shielded-spend-localnet-receipt.json)

Compile the fixture with the 3.2.1 target and create separate authenticated `ShieldedSpend.tip` and `ShieldedSpend.spend` bundles. Use the same source, profile and ledger parameters for both. [Bundle setup](portable-artifacts.md)

```sh
NOCTIUM_TRANSFER_NODE=http://127.0.0.1:19944 \
NOCTIUM_TRANSFER_PARAMETER_CACHE=/path/to/verified/parameter-cache \
NOCTIUM_TRANSFER_TIP_BUNDLE=/path/to/tip-bundle \
NOCTIUM_TRANSFER_TIP_MANIFEST_SHA256=YOUR_TIP_MANIFEST_SHA256 \
NOCTIUM_TRANSFER_SPEND_BUNDLE=/path/to/spend-bundle \
NOCTIUM_TRANSFER_SPEND_MANIFEST_SHA256=YOUR_SPEND_MANIFEST_SHA256 \
  cargo test --locked --manifest-path runtime/Cargo.toml --lib \
  --no-default-features --features zkir-321,localnet \
  funded_shielded_map_spend_localnet -- --ignored --nocapture
```

### Funded spend with standalone claims

`FundedRawShieldedSpend.spendRaw` checks the nonce and removes the Map entry.
Only the two standalone claims bind the contract input nullifier and the
recipient output commitment. The Ledger 9.1.0.1 development chain finalized
the spend at block 52. The recipient decrypted five units at index 29. A
changed output commitment and a replay were rejected before submission.
[Receipt](funded-raw-shielded-spend-localnet-receipt.json)

Compile `tests/FundedRawShieldedSpend.lean` with the 3.2.1 target. Assemble its
`tip` and `spendRaw` bundles with their matching keys. Use the same six
settings as the whole-spend command with the `NOCTIUM_RAW_SPEND_` prefix.
Run `funded_shielded_map_raw_spend_localnet` as the test name.

## Immediate shielded relay to a destination contract

The pinned Compact fixture receives a contract-owned coin, sends its full value with `sendImmediateShielded`, rejects change, then binds a `claimContractCall` to the destination using the child call's communication opening. The in-memory runner checks the receive, spend and nullifier claims, both contract-owned outputs, the destination call commitment, and the empty relay Map. [Compact source](../../tests/compact/ShieldedCoinMap.compact) · [Runner](../../tests/compact/shielded-coin-map.mjs)

`tests/ShieldedImmediateRelay.lean` exercises the same bounded flow through two native calls. Relay mints five units, forms a contract-owned transient, sends an equal-value contract output to Destination, and binds the child call to the same opening. Destination receives the output into its qualified coin Map. The localnet host books the transient and destination commitments against one finalized snapshot, prepares Relay then Destination with that index map, and rechecks both contract states before DUST funding.

Ledger 9.1.0.1 finalized the composed call at block 136. The Destination Map stored value 5 at output index 30. The transient used index 31, its nullifier appeared in finalized Zswap state, and the harness rejected a wrong recipient and wrong color. The relay and destination circuits used k=15/18,644 rows and k=13/6,436 rows. [Receipt](shielded-immediate-relay-localnet-receipt.json)

This qualifies a related native subset of `sendImmediateShielded`. General token domains, amounts, and call shapes remain open, and feature equivalence is unverified.

Run the focused funded case with the two authenticated bundles and verified Ledger parameter cache:

```sh
NOCTIUM_RELAY_NODE=http://127.0.0.1:29944 \
NOCTIUM_RELAY_PARAMETER_CACHE=/path/to/verified/parameter-cache \
NOCTIUM_RELAY_BUNDLE=/path/to/relay-bundle \
NOCTIUM_RELAY_MANIFEST_SHA256=YOUR_RELAY_MANIFEST_SHA256 \
NOCTIUM_DESTINATION_BUNDLE=/path/to/destination-bundle \
NOCTIUM_DESTINATION_MANIFEST_SHA256=YOUR_DESTINATION_MANIFEST_SHA256 \
  cargo test --locked --manifest-path runtime/Cargo.toml --lib \
  --no-default-features --features zkir-321,localnet \
  funded_shielded_immediate_relay_localnet -- --ignored --nocapture
```

## Partial spend from a Map

`tests/ShieldedMapPartialSpend.lean` adds `sendShieldedFromMap`. It spends one contract-owned coin into a user output and contract change. The native runtime enforces `0 < sendAmount < inputAmount`, derives the user nonce with `midnight:kernel:nonce_evolve` and the change nonce with `midnight:kernel:nonce_evolve/2`, removes the old Map row, then receives the change under its derived nonce. The native plan binds the nullifier and both output commitments, and allows only read-only change-key checks before the change receive.

The pinned Compact 0.36.1 runner checks a 5-unit input split into a 2-unit user output and 3-unit contract change, including exact claim hashes, Map contents, amount bounds and replay rejection. Noctium's focused VM test and opt-in compiled-plan/ZKIR check pass against the same vector. On the ZKIR 3.2.1 mock, sharing the immutable contract-address read changes the circuit size from 25,493 rows to 19,599 rows. Both versions report k=15.

Ledger 9.1.0.1 finalized the split at block 231. The recipient decrypted two units at output index 32. The contract Map held three units at change index 33 and no longer held the original coin. The harness rejected a mismatched nonce, a full-value request through the split entry and replay before submission. [Receipt](shielded-partial-spend-localnet-receipt.json)

Export the Lean fixture:

```sh
lake exe noctium compile tests/ShieldedMapPartialSpend.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --output build/experiments/214/lean-partial-spend-shared-address
```

Run the Compact comparator with the pinned compiler and runtime directories:

```sh
node tests/compact/shielded-coin-map.mjs \
  /path/to/compactc-0.36.1 \
  /path/to/compact-runtime-0.21.0
```

Run the funded Noctium localnet test after preparing authenticated `tip` and `spend` bundles and a local development node:

```sh
NOCTIUM_PARTIAL_SPEND_NODE=http://127.0.0.1:19944 \
NOCTIUM_PARTIAL_SPEND_PARAMETER_CACHE=/path/to/verified/parameter-cache \
NOCTIUM_PARTIAL_SPEND_TIP_BUNDLE=/path/to/tip-bundle \
NOCTIUM_PARTIAL_SPEND_TIP_MANIFEST_SHA256=YOUR_TIP_MANIFEST_SHA256 \
NOCTIUM_PARTIAL_SPEND_SPEND_BUNDLE=/path/to/spend-bundle \
NOCTIUM_PARTIAL_SPEND_SPEND_MANIFEST_SHA256=YOUR_SPEND_MANIFEST_SHA256 \
  cargo test --locked --manifest-path runtime/Cargo.toml --lib \
  --no-default-features --features zkir-321,localnet \
  funded_shielded_map_partial_spend_localnet -- --ignored --nocapture
```

## Merge two finalized coins

`mergeShieldedFromMap(pot, nonceA, nonceB)` consumes two distinct, finalized contract-owned coins of the same color. It uses a checked UInt128 sum and derives the new nonce from the first coin. The native host checks both nullifiers and their Merkle roots and owner after the ledger normalizes the offer order. The proved call claims the exact output commitment and stores one new qualified coin.

The pinned Compact comparator and native VM fixture agree for values 5 and 7, including the nonce, commitment, and both nullifiers. The fixture checks duplicate inputs, a different color, and overflow. The Compact JavaScript booking codec limits amounts to UInt64, so the UInt128 overflow check uses the native fixture.

Ledger 9.1.0.1 finalized the funded merge at block 48303. The two input nullifiers were spent, and the new Map row and Zswap leaf recorded value 12 at index 32. [Receipt](shielded-map-merge-localnet-receipt.json)

Compile `tests/ShieldedCoinMerge.lean` with the ZKIR 3.2.1 target and prepare authenticated `mint` and `merge` bundles using the verified localnet parameters. [Bundle assembly](portable-artifacts.md)

```sh
NOCTIUM_MERGE_NODE=http://127.0.0.1:19944 \
NOCTIUM_MERGE_PARAMETER_CACHE=/path/to/verified/parameter-cache \
NOCTIUM_MERGE_MINT_BUNDLE=/path/to/mint-bundle \
NOCTIUM_MERGE_MINT_MANIFEST_SHA256=YOUR_MINT_MANIFEST_SHA256 \
NOCTIUM_MERGE_BUNDLE=/path/to/merge-bundle \
NOCTIUM_MERGE_MANIFEST_SHA256=YOUR_MERGE_MANIFEST_SHA256 \
  cargo test --locked --manifest-path runtime/Cargo.toml --lib \
  --no-default-features --features zkir-321,localnet \
  funded_shielded_map_merge_localnet -- --ignored --nocapture
```

## Merge a coin minted in the same operation

`mergeShieldedImmediateFromMap(pot, nonceA, nonceB, colorB, amountB)` consumes a finalized Map coin and a new transient coin of the same color. The output uses the first coin's evolved nonce and a checked UInt128 sum. The development binder checks the exact guaranteed offer, both nullifiers, both receive commitments, the durable output spend and the proved mint domain and amount.

The pinned Compact 0.36.1 comparator and the native checker agree on the 5 + 7 result, nonce, nullifiers and commitments. The native checker rejects a detached transient and a commitment booked under a different owner. The host check rejects a different mint amount, a different domain and a duplicate transient.

Ledger 9.1.0.1 finalized the funded call at block 48573. Both input nullifiers were spent. The Map contained one output worth 12 at index 34, with the spent transient recorded at index 35. This covers one same-operation mint and merge. [Receipt](shielded-map-immediate-merge-localnet-receipt.json)

To repeat the funded case, compile `tests/ShieldedCoinImmediateMerge.lean` and assemble its `mint` and `merge` bundles. Run the command above with their manifest hashes and the test name `funded_shielded_map_immediate_merge_localnet`.

Pins and source behavior are recorded in the [Compact 0.36.1 release](https://github.com/LFDT-Minokawa/compact/releases/tag/compactc-v0.36.1), [Compact private tip jar](https://docs.midnight.network/tutorials/private-tip-jar/smart-contract), [Compact ledger ADTs](https://docs.midnight.network/compact/reference/ledger-adt), and [Ledger 9.1.0.1 release](https://github.com/midnightntwrk/midnight-ledger/releases/tag/ledger-9.1.0.1).
