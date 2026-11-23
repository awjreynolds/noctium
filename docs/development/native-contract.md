# Source-driven native contract workflow

Noctium's compiler is Lean. The [native Rust runtime](native-rust-runtime.md) executes its emitted plan and the [Rust assembler](native-assembler.md) constructs real native intents from retained authenticated bundle bytes. Neither execution nor assembly requires Node. The [C ABI](native-runtime-abi.md) exposes witness acquisition and private-state journals.

The commands below reproduce the earlier JavaScript development harness. They use native ledger/proving formats, but their orchestration and one assembler are JavaScript. This is an optional development workflow. New native applications should start with the [Rust client](native-client.md), which integrates [proof construction](native-proof-api.md), funding, signing, submission, finalized receipt validation and durable recovery. The [full host-neutral transaction ABI](https://github.com/awjreynolds/noctium/issues/61) remains separate work. Native key generation uses the pinned independent ZKIR CLI.

The helpers consume generated plans and ZKIR. They do not parse Lean source or invoke another source-language compiler. Use the linked Rust assembler workflow when embedding execution and assembly in a native application.

## Prepare the tools and chain

Install the pinned Lean toolchain, Rust 1.100.0, Node.js, Git, and a native C build toolchain. The isolated chain requires the pinned cached Docker images and verified public parameters described in [the localnet guide](../../scripts/localnet/README.md).

```sh
lake build
npm ci --prefix scripts/zkir --ignore-scripts
npm ci --prefix scripts/preview --ignore-scripts
node scripts/zkir/bootstrap-native.mjs /private/tmp/noctium-native-zkir
node scripts/localnet/stack.mjs up
mkdir -p build/native-claim
node scripts/localnet/ledger-parameters.mjs build/native-claim/ledger.params
```

The bootstrap builds the official independent ZKIR 3.2.0 CLI from pinned source with its lockfile. `ledger-parameters.mjs` checks the development genesis and reads real parameters from the isolated node. The runtime uses `parameters.transactionCostModel.runtimeCostModel` and the official `partitionTranscripts` API, rather than treating query cost as an execution budget.

## Compile the actual Lean source

Place a target requirement before the contract declarations in any source file that needs a specific profile.

```lean
set_option noctium.requiredTarget "midnight-ledger-9-zkir-3.2.1"
```

Use `--target profiles/midnight-ledger-9-zkir-3.2.1-target.json` for both `noctium check` and `noctium compile`. A mismatched or unknown requirement fails before artifact publication.

```sh
.lake/build/bin/noctium compile examples/PrivateClaim.lean --output build/native-claim/source
/private/tmp/noctium-native-zkir/bin/zkir compile build/native-claim/source/PrivateClaim.claim.zkir build/native-claim/claim.prover build/native-claim/claim.verifier
node scripts/zkir/claim-config.mjs build/native-claim/inputs.json
node scripts/zkir/native-contract.mjs build/native-claim/source/PrivateClaim.claim.impact.json build/native-claim/source/PrivateClaim.claim.zkir build/native-claim/claim.prover build/native-claim/claim.verifier build/native-claim/artifacts --ledger-params build/native-claim/ledger.params --config build/native-claim/inputs.json --prove
node scripts/localnet/deploy-native.mjs build/native-claim/artifacts build/native-claim/local
```

The config generator uses publicly known development values: secret 42, campaign 9, siblings 17 and 23, and directions false and true. It computes the public root and nullifier through the official Native-field Poseidon implementation. It also defines the five invalid cases for the harness. The compiler source defines the hash domains and relation. The config file supplies example data only.

`--prove` is optional. It creates a diagnostic standalone proof with binding input 42. The funded transaction runner creates its own correctly bound proof and does not reuse that diagnostic proof. Proving requests contain witnesses, so the optional proof-server override accepts HTTP or HTTPS on loopback only and refuses credentials and redirects.

If SDK dependencies are installed outside `scripts/preview`, set `NOCTIUM_WALLET_DEPENDENCIES` to their package directory before running `deploy-native.mjs`. The qualified setup used `/private/tmp/noctium-preview-wallet`.

## Emitted artifacts and validation

The assembler reads schema version 1 from `PrivateClaim.claim.impact.json`. This file contains the actual source contract's state schema, circuit input/output schema, expression trees, state guards, VM operations, and ordered reads. No placeholder root or nullifier replacement occurs.

The runtime materializes supported cell reads and empty initial maps, computes declared outputs, builds the exact VM transcript, and registers the native verifier key in a `ContractOperation`. It constructs `ContractState`, `ContractDeploy`, `ContractCallPrototype`, and serialized intents using the official ledger API. It rejects unsupported schemas, unsafe entrypoint artifact names, unknown options, duplicate options, unknown inputs, and noncanonical field values.

The output directory contains `source-plan.json`, `runtime-config.json`, `ledger.params`, native keys and circuits, serialized initial/predicted state, deployment/call intents, and `native-contract.json`. Witness-bearing files use mode 0600. Keep the directory private. Each assembly invocation randomizes the deployment address, so keys, address, state, and intents must stay together.

The transaction runner refuses the wrong genesis, funds through the published local development identity, requires finalized matching receipts, checks accepted state against predicted state, and verifies invalid witnesses and replay rejection. Its accepted evidence is `local/native-localnet.json`.

Funding and contract-state queries use two RPC fetch workers, two fetch-compute workers and two wallet replay workers. Each toolkit command has a ten-minute timeout. These explicit flags override the pinned toolkit's 20-worker fetch default, which exhausted the development node's 3 GiB memory limit during a historical scan. The runner keeps fetch data and wallet snapshots in a private `.native-toolkit-*` directory inside the work directory. Sequential commands share these disk caches. Each invocation, including `--resume-call`, starts with fresh caches, so a reset development chain or abandoned run does not supply old snapshots. Completed cache directories are disposable development data.

Check the bounded configuration without a running chain:

```sh
node --test tests/localnet-toolkit-config.mjs
```

The 2026-11-16 check also exercised the pinned toolkit with network-disabled funding/state dry runs, including an inherited 20-thread replay setting. The explicit two-thread flag prevailed. Two live read-only state queries then used this configuration on the isolated chain. The first fetched 1,083 blocks with two fetch and two compute workers. The second fetched two new blocks and read 1,082 from the shared disk cache. Both returned the accepted state bytes with SHA-256 `d03deaed2a47e077412acd4db0fb3069e47cd41d05472eebb3c8182f0c938dc3`. The node stayed running at 256.5 MiB after the checks. No new deployment or claim was submitted for this configuration check.

The standalone checks are also reusable:

```sh
node scripts/zkir/check-native-cases.mjs build/native-claim/artifacts build/native-claim/artifacts/initial-state.bin negative
node scripts/zkir/check-native-cases.mjs build/native-claim/artifacts build/native-claim/local/observed-state.bin replay
```

The current helper supports the initial source subset: Native-field and Boolean inputs, field arithmetic, equality, eager selection, Poseidon, state-cell reads, and empty initial maps with member checks and insertion. Unsupported source features must fail before a support claim. The accepted source-to-ledger evidence is [native-localnet.md](native-localnet.md).

## Checkpoint a ledger transcript

Use `checkpoint` between ledger effects. A guarded checkpoint contributes a
native marker only when its guard is true. Disclose a private guard before
using it, since the marker changes the public transcript.

```lean
write firstMark := 1
when enabled checkpoint
write secondMark := 2
```

A successful Lean reference run produces the same final cells with or without
the marker. The pinned Ledger runtime uses the marker to partition the
transcript. With the fixture's bounded dismissal budget, the guaranteed
prefix writes `firstMark` and the fallible continuation starts at the
checkpoint. [Midnight checkpoint semantics](https://docs.midnight.network/compact/reference/ledger-adt#checkpoint)

The [Compact oracle](../../tests/compact/checkpoint.mjs) checks both guarded
paths. The [native test](../../runtime/tests/native_checkpoint.rs) reads the
actual emitted ZKIR and Impact plan, checks the ordered marker and rejects a
changed marker.

Ledger 9 localnet finalized the deployment at height 4 and the
active-checkpoint call at height 7. Both receipts matched the
predicted state bytes. The relation used k=7 and 68 rows.
[Localnet receipt](native-checkpoint-localnet-receipt.json)

### Finalize and recover a checkpoint prefix

The [timed fixture](../../tests/NativeCheckpointPartial.lean) prepares a call
before its cutoff and submits the signed bytes after the cutoff. Its ordered
suffix writes make the continuation exceed the live Ledger 9 guaranteed
budget. The Rust SDK checks the actual split before submitting.

The pinned node finalized `TxPartialSuccess` at block 139. Replay showed
segment 0 and the funding segment succeeded, and call segment 1 failed.
`firstMark` advanced to 1 and `secondMark` stayed at 0. The finalized
contract bytes matched the guaranteed-prefix prediction exactly. Reopening the
durable journal kept the synthetic private write staged and disallowed both
resubmission and private CAS.
[Retained localnet receipt](native-checkpoint-partial-localnet-receipt.json)

For the [opt-in Rust fixture](../../runtime/tests/native_checkpoint_partial.rs),
emit the timed contract with the 3.2.1 ledger profile and assemble a public
bundle using the pinned native tools and the live parameters.
[Artifact workflow](portable-artifacts.md#build-and-use)

```sh
NOCTIUM_CHECKPOINT_BUNDLE=/path/to/bundle \
NOCTIUM_CHECKPOINT_MANIFEST_SHA256=MANIFEST_SHA256 \
NOCTIUM_CHECKPOINT_PARAMETER_CACHE=/path/to/verified/parameter-cache \
NOCTIUM_CHECKPOINT_NODE=http://127.0.0.1:19944 \
NOCTIUM_CHECKPOINT_JOURNAL=/absolute/path/to/development-journal \
cargo test --manifest-path runtime/Cargo.toml --locked \
  --no-default-features --features zkir-321,localnet \
  --test native_checkpoint_partial -- --ignored --nocapture
```

## Use a ledger set

A set stores each member as a key with a native `Null` value. Declare a
top-level set with `set registered : Bytes32`, or a map of sets with
`tree groups : Native => Set Bytes32`. Use ordinary keyed `insert`,
`member` and `remove`. Read the cardinality with `size`, test emptiness with
`isEmpty`, and clear the selected set with `reset`.

Inserting a member twice preserves cardinality. Removing an absent member
preserves the set. A nested call must initialize its parent path first.
Resetting one nested set leaves neighboring sets intact. A guarded
inactive read uses the usual zero or false value without traversing
the guarded path. As with map keys, explicitly disclose any private
input used to select a public ledger key.

The [Lean example](../../tests/NativeSet.lean) and
[Compact oracle](../../tests/compact/native-set.mjs) cover Bytes32
members under a Native/Field parent key.
[Midnight Set reference](https://docs.midnight.network/compact/reference/ledger-adt#setvalue_type)

The native VM and ZKIR checker replayed the Compact transitions with fresh
Lean artifacts. The read-only `isEmpty` case produced the same public
transcript for two different nonempty cardinalities. The Rust SDK
finalized a first insertion into both sets at Ledger 9.1.0.1 localnet
block 151. The observed state matched the exact prediction, and the
relation measured K9 and 467 rows. The remaining differential cases ran
off chain. Shielded coin insertion and SDK host enumeration remain
separate. [Native fixture](../../runtime/tests/native_set.rs) · [Localnet receipt](native-set-localnet-receipt.json)

## Read the ledger caller

`readCaller as (present, isContract, contractId, userId)` binds two
Boolean flags and two `Bytes32` addresses. A contract caller sets both
flags and fills `contractId`. A user caller sets only `present` and
fills `userId`. An absent caller or inactive guard yields false flags
and zero bytes. A private guard needs disclosure.

The native ledger context supplies the caller. The Impact plan checks
the presence, tag and active address against the ZKIR statement. A
different ledger caller fails the same transcript check. The Rust SDK
ordinary-call path prepares an absent caller. For a top-level user call,
`prepare_call_with_unshielded_caller` derives the address from a snapshot
and selected NIGHT outpoints. `prepare_unshielded_caller` checks those
outpoints against a fresh snapshot and requests signing through a funding
adapter with explicit caller support. [Midnight caller semantics](https://docs.midnight.network/compact/reference/ledger-adt#caller)

[Lean fixture](../../tests/NativeCaller.lean) ·
[Compact oracle](../../tests/compact/caller.mjs) ·
[Native checker](../../runtime/tests/native_caller.rs)

The Rust SDK finalized the deployment at Ledger 9.1.0.1 localnet block
67 and the active top-level call at block 70. Exact state bytes matched
the prediction. A separate decoder verified that the `recorded` cell
changed from true to false. The relation measured K9 and 312 rows. The
contract and user variants ran in the native VM and Compact runtime.
[Localnet receipt](native-caller-localnet-receipt.json)

A composed call on localnet finalized at block 50468. The parent bound the
child's four typed caller results through the communication commitment and
stored the child-reported contract address. The finalized value matched the
parent's address. A mismatched expected address failed assembly before
submission. [Lean fixture](../../tests/NativeCallerComposition.lean) ·
[Composed caller receipt](native-typed-caller-localnet-receipt.json)

A signed user call finalized at localnet block 51112 and stored the
expected user address. The transaction spent the selected guaranteed NIGHT
outpoint and returned the same amount to the same owner. The ordinary
funding route rejected this offer. The focused test also rejected a wrong
signing key, an altered principal return, and reuse of the spent outpoint.
The relation measured K8 and 231 rows.
[Lean fixture](../../tests/NativeUserCaller.lean) ·
[Signed user caller receipt](native-user-caller-localnet-receipt.json)

## Store a byte-aligned UInt128

```lean
cell totalSupply : UInt 128 alignedBytes
```

This direct cell retains its UInt128 type and stores one 16-byte FAB atom.
The compiler emits `cellAlignment: "u128"` in the state schema. Constructors,
writes and transcript reads use the same alignment. Ordinary UInt128 cells
keep their field encoding. Default builds retain all range checks.

The native fixture reads and writes zero and the UInt128 maximum in both
directions. An inactive write preserves state and its guarded read returns
zero. Plan admission rejects a field-aligned typed push to the cell.
The pinned ledger parser rejects 2^128 for the 16-byte atom.
The VM rejects a field-aligned cell even when it carries the same number.
[Lean fixture](../../tests/ByteAlignedUInt128Cell.lean) · [Native fixture](../../runtime/tests/uint128_fab_read.rs)

The opt-in `--ledger-read-bound Contract.entrypoint` build accepts one direct,
unguarded read from a byte-aligned UInt128 cell on the pinned ZKIR 3.2.1 profile.
Choose the operation by its fully qualified name and emit ledger artifacts.
The selected operation must satisfy the checked scalar relation decoder.

```sh
lake exe noctium compile tests/UInt128BoundProbe.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json --emit ledger \
  --ledger-read-bound UInt128BoundProbe.readSupply --output build/uint128-bound
```

The compiler removes the corresponding range instruction after matching the
exact public input and Bytes(16) Popeq group. The metadata records the cell,
input and encoding for the verifier premise. The Lean theorem compares both
exact decoded relations under the premise supplied by the typed Ledger read.
Key generation must use the optimized ZKIR for that operation.
[Optimization fixture](../../tests/UInt128LedgerReadBound.lean) · [Ledger acceptance evidence](https://github.com/awjreynolds/noctium/issues/408)

## Reset a ledger cell

`reset cellName` writes the canonical default of the cell's declared scalar
type. Use `when flag reset cellName` for a conditional reset. The usual
public-state disclosure and sealed-cell checks apply, and a following read
sees the reset when execution takes the guard. The compiler lowers the reset
as a typed write through the existing Impact path.

[The Lean fixture](../../tests/NativeCellReset.lean) and
[the Compact fixture](../../tests/compact/CellReset.compact) exercise seeded
UInt64, Native/Field, Boolean and Bytes4 cells. Run the
[native checker fixture](../../runtime/tests/native_cell_reset.rs) with
`NOCTIUM_CELL_RESET_DIR` pointing to fresh Lean ZKIR 3.2.1 ledger outputs.
The scalar fixture covers both guard outcomes. Aggregate Cell defaults and
other type combinations need separate equivalence evidence.

Ledger 9.1.0.1 finalized the seed at height 49664, the inactive reset at
49667, and the active reset at 49670. The inactive call preserved the exact
finalized bytes. The active call wrote the canonical UInt64, Field, Bool and
Bytes4 defaults. The `clear` circuit uses K8 and 192 rows.
[Finalized receipt](native-cell-reset-localnet-receipt.json)

A checked qualified Coin Cell also accepts `reset coinSlot`. Its default
uses the ledger's Bytes32, Bytes32, Bytes16 and Bytes8 FAB alignment. The
native checker and pinned Compact fixture agree on both guard outcomes and
preserve the adjacent marker Cell. The normal booked Coin writer retains its
transaction-index test. [Lean source](../../tests/QualifiedCoinCell.lean) ·
[Compact oracle](../../tests/compact/qualified-coin-cell-reset.mjs) ·
[Native checker](../../runtime/tests/qualified_coin_cell.rs)

An opt-in funded test initialized marker 37 and a Coin with nonce bytes 2,
color bytes 1, value 5 and `mtIndex` 42. One active `guardedClear` call
finalized at Ledger 9.1.0.1 height 50102. The decoded native state matched
the plan-derived typed defaults, including zeroed Bytes32 fields, value and
index, while preserving marker 37. The receipt records both pinned bundle
hashes, deployment and call receipts, and the final state digest. It pins
Compact 0.36.1, ZKIR 3.2.1 and source compiler revision
`247ea6b7e09e14354e3ffc847573e5b496435bd7`.
[Funded Rust test](../../runtime/src/localnet.rs) ·
[Finalized receipt](qualified-coin-cell-reset-localnet-receipt.json)

An ordinary checked record Cell with two Native fields resets both fields
to zero. The native checker and Compact 0.36.1 agree on both guard outcomes
and preserve the neighboring marker. The native checker rejects a sealed
Cell and a mismatched declared schema. This fixture covers the flat Native
layout in the VM. Funded execution and other record layouts remain open.
[Lean fixture](../../tests/FlatRecordCellReset.lean) ·
[Compact oracle](../../tests/compact/flat-record-cell-reset.mjs) ·
[Native checker](../../runtime/tests/flat_record_cell.rs)

## Record standalone token mints

```lean
when enabled mintShielded(domain, disclose(amount))
when enabled mintUnshielded(domain, disclose(amount))
```

Both effects take a 32-byte domain and a `UInt 64` amount. The domain, amount
and guard must be public or explicitly disclosed. Active effects accumulate by
domain in separate shielded and unshielded mint maps. Accumulation beyond
`UInt 64` fails. The ledger derives each token type from the issuer address
and domain. These effects record issuance. A transfer or settlement requires
its own ledger effects and transaction outputs.

The [Lean fixture](../../tests/NativeStandaloneMints.lean) and
[Compact reference fixture](../../tests/compact/StandaloneMints.compact)
exercise guarded minting, separate effects and the accumulation limit.

The [localnet receipt](native-standalone-mints-localnet-receipt.json) records
an active call with two mint amounts, 17 and 2, in each namespace. Ledger
9.1.0.1 finalized the call with the predicted contract state. The transaction
settled no tokens to a recipient.

## Mint an unshielded token to a tagged recipient

`mintUnshieldedTo` records the native mint and spend claim, then binds the
token color derived from the executing contract and domain. The amount is
`UInt 64`. The Boolean recipient tag selects `ContractAddress` or
`UserAddress`.

```lean
when enabled mintUnshieldedTo(domain, amount, isContract, recipient) as mintedColor
return color : Bytes32 := mintedColor
```

Self-credit applies when the recipient is a `ContractAddress` equal to the
current contract. A skipped mint binds zero bytes and leaves settlement
effects empty. Private amounts, recipients and control require explicit
disclosure before use in the public ledger.

The [Lean fixture](../../tests/NativeUnshieldedMintRecipient.lean),
[Compact reference](../../tests/compact/UnshieldedMintRecipient.compact),
and [native checker](../../runtime/tests/native_unshielded_mint_recipient.rs)
cover self-contract, other-contract, same-bytes user and inactive calls.
The native checker also rejects a changed recipient tag.

For a proved user-tagged mint, Rust callers use
`BoundTransaction::prepare_unshielded_mint` with their chain, funding and
signing adapters. It derives the exact recipient, amount and custom token
from one guaranteed call transcript. The funding adapter receives the
resulting output-only offer, and signing preserves it. Native ledger validation
checks the proof and matching output before submission. Self-credit uses
ordinary transaction preparation.

On Ledger 9.1.0.1 with ZKIR 3.2.1, the Rust fixture deployed at block 59306.
At 59309, the contract-tagged mint credited 7 tokens to the contract. At
59312, the user-tagged mint used the same recipient bytes, left the contract
balance at 7, and created a separate 7-token output. The test found that exact
output in a replayed ledger state whose root matched the finalized node.
[Finalized receipt](native-unshielded-recipient-mint-localnet-receipt.json)

## Read the current contract address

`readSelf as own` binds the executing contract's `Bytes32` address.
`when enabled readSelf as own` produces zero bytes when inactive. A
private guard needs disclosure before it controls this public read.
The compiler encodes the query-context address as a native Impact read
and binds its two byte limbs in ZKIR. [Midnight self reference](https://docs.midnight.network/compact/reference/ledger-adt#self)

The address comes from the contract execution context. This allows a
caller-dependent entrypoint to use the callee's own address alongside
the separate caller value. Native replay against a different address
fails the equality check. [Lean fixture](../../tests/NativeContractAddress.lean) ·
[Compact oracle](../../tests/compact/contract-address.mjs) ·
[Native checker](../../runtime/tests/native_contract_address.rs)

Ledger 9.1.0.1 finalized the active call at block 49730 and stored the
target's deployment address in `lastAddress`. The inactive call finalized at
49733 with the same contract state bytes. The native checker also rejects
wrong-address replay and a changed address output. The `identify` circuit
uses K8 and 146 rows. [Finalized receipt](native-contract-address-localnet-receipt.json)

## Derive token colors

`nativeToken()` returns the canonical all-zero color. `tokenType(domain, address)` takes a Bytes32 separator and explicit contract-address bytes. Compact 0.36.1 and Noctium both hash the padded `midnight:derive_token` opening, the separator, and the address bytes in that order. This qualifies the standalone color operations and their native Bytes32 ABI. The matrix tracks nominal address authoring and token settlement separately. [Pinned Compact definitions](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/compiler/standard-library.compact#L113-L119)

The Compact oracle and fresh ZKIR 3.2.1 relations agree on four vectors, including zero and all-255 inputs. The native runtime rejects 31-byte and 33-byte addresses and byte values above 255. The verified native proof rejects substitution of the separator or address. [Lean source](../../tests/NativeTokenColors.lean) · [Compact oracle](../../tests/compact/native-token-colors.mjs) · [Native checker and proof](../../runtime/tests/native_token_colors.rs)

Compile the fixture at compiler revision `b60c97a635dc40dc576e10884ba895c390943d11` with the ZKIR 3.2.1 target and `--emit ledger`. Generate the `deriveFor` keys and assemble the public bundle using the pinned Ledger 9.1.0.1 parameters. The checked relation used K13 and 4,059 rows. The retained bundle digest was `e49eb53b5aec69f551288f7cefb650440b9150612f7ed290ef0ba93a2ff1984e`. Its proof parameters digest was `d3324910969c4cc54143b8045b649e5c3a4bd5fb7b8f85fe1b770f640ce1c803`. [Bundle assembly](portable-artifacts.md)

```sh
NOCTIUM_NATIVE_TOKEN_COLORS_DIR=PATH_TO_COMPILER_OUTPUT \
NOCTIUM_NATIVE_TOKEN_COLORS_BUNDLE=PATH_TO_VERIFIED_BUNDLE \
NOCTIUM_NATIVE_TOKEN_COLORS_MANIFEST_SHA256=VERIFIED_MANIFEST_DIGEST \
NOCTIUM_NATIVE_TOKEN_COLORS_PROOF_PARAMETERS=PATH_TO_TRUSTED_K13_PARAMETERS \
NOCTIUM_NATIVE_TOKEN_COLORS_PROOF_PARAMETERS_SHA256=TRUSTED_K13_DIGEST \
  cargo +1.100.0 test --locked --manifest-path runtime/Cargo.toml \
  --no-default-features --features zkir-321 --test native_token_colors -- --ignored
```

## Read a token balance

Use a 32-byte color and a Boolean tag. `true` selects the unshielded balance and
`false` selects the shielded balance for the same color.

```lean
tokenBalance(color, isUnshielded) as amount
tokenBalanceLt(color, isUnshielded, limit) as below
tokenBalanceGt(color, isUnshielded, limit) as above
```

These operations read the balance at the start of the call. A missing token has
balance zero. Exact reads return `UInt 128`. Both strict comparisons accept a
`UInt 128` limit at the source boundary. The pinned Impact VM requires the
actual balance and limit to fit in `UInt 64` when the comparison runs.

Color, tag, comparison limit and any `when` guard are public or explicitly
disclosed. A skipped exact read binds zero. A skipped comparison binds
`false`. The comparison binds its Boolean result to the native transcript.
Use the exact read when the application needs the amount.

The [Lean fixture](../../tests/NativeTokenBalance.lean) and
[Compact reference fixture](../../tests/compact/TokenBalance.compact) use the
same inputs and guards.

For unshielded balance helpers, set the token tag to `true`. Derive inclusive
comparisons from the opposite strict result. With an activity guard, use
`select(enabled, boolXor(below, true), false)` for at least and apply the same
expression to `above` for at most. The false branch preserves the inactive
result. [Lean fixture](../../tests/UnshieldedBalanceHelpers.lean)

The [localnet receipt](native-token-balance-localnet-receipt.json) records a
finalized ordinary call for an absent unshielded token. The call wrote zero
over the previous recorded value of 17. Shielded and nonzero cases use
simulated starting balances with the pinned native checker.
## Compare the block time

`blockTimeBefore(deadline) as before` and `blockTimeAfter(deadline) as after`
compare the ledger block time against a `UInt 64` deadline in Unix seconds.
Both are false at equality. A guarded inactive comparison supplies false
without reading the clock. A private deadline or activity condition needs
an explicit disclosure because the native transcript exposes the comparison
operands and activity. [Midnight kernel reference](https://docs.midnight.network/compact/reference/ledger-adt#blocktimelessthan)

`blockTimeAtOrAfter(deadline) as reached` and
`blockTimeAtOrBefore(deadline) as within` include equality. Each uses one native
strict comparison and complements the result only when the read is active. The
[inclusive localnet receipt](native-block-time-inclusive-receipt.json) records
one active call at cutoff zero.

The compiler emits native Impact operations to fetch the block time and
bind the Boolean result to the ZKIR statement. The native VM re-evaluates
the comparison against its execution context. If the clock crosses the
deadline and changes a bound result, the transcript fails. The caller
must prepare a new proof for the changed result.

Use `PreparedProof::from_config_in_block` with a prospective ledger
`BlockContext` in the Rust SDK. The native localnet client takes this
context from its checked node snapshot. The low-level
`prepare_with_context` also accepts an explicit query context.
An active comparison fails preparation when no clock is supplied.
The [source fixture](../../tests/NativeBlockTime.lean),
[Compact oracle](../../tests/compact/block-time.mjs) and
[native checker fixture](../../runtime/tests/native_block_time.rs)
check the strict boundaries. A hosted SDK path that does not provide a
block context still requires integration.

Ledger 9.1.0.1 finalized the inactive call and active calls at cutoff zero
and UInt64 maximum. Each exact contract state was unchanged. The receipt
records the oracle results and the observed inclusion times for blocks
49784, 49790 and 49796. Native checking covers exact equality and replay
across the deadline. These funded proofs use explicit prospective block
context. The `checkTime` circuit uses K8 and 126 rows.
[Finalized receipt](native-block-time-localnet-receipt.json)

## Settle tagged token inputs and outputs

```lean
incUnshieldedInputs(color, received, isUnshielded)
incUnshieldedOutputs(color, sent, isUnshielded)
claimUnshieldedCoinSpend(color, authorized, isUnshielded, isContract, recipient)
```

Each operation records a separate native effect. The ledger verifies these
effects against the transaction's other calls and settlement data.
Use `true` for the unshielded token tag and `false` for the shielded tag.
The spend's recipient tag distinguishes a contract address from a user
address with the same bytes. Each operand and any guard is public or
explicitly disclosed.

A first entry accepts a `UInt 128` amount. An addition to an existing entry
requires both operands and their sum to fit `UInt 64` in the pinned VM.
The [Lean fixture](../../tests/NativeTaggedSettlement.lean) and
[Compact reference fixture](../../tests/compact/TaggedSettlement.compact)
exercise these bounds and the effects' tagged keys.

The [funded localnet receipt](native-tagged-settlement-localnet-receipt.json)
records a proof which checks that both starting balances are zero, even after
the source records receipt effects. The finalized state contains 17
unshielded-tag units and 23 shielded-tag units of the same color. The native
assembler predicted both balances. The finalized bytes matched the SDK's
ledger replay byte for byte.

To send unshielded tokens, record the output and the recipient's spend claim.
Use `readSelf` to get the ledger-provided contract address. Credit the input
when the recipient has the contract tag and matches that address. The Lean,
Compact and native checker fixtures cover the self-send, a second contract and
a user address whose bytes match the sender. [Lean fixture](../../tests/NativeUnshieldedSend.lean)
[Compact fixture](../../tests/compact/UnshieldedSend.compact)
[Native checker](../../runtime/tests/native_unshielded_send.rs)

## Root record-key Maps on the development ledger

`RecordMapCollections.update` uses flat Bool and UInt16 record keys in a
scalar-valued Map and a flat-record-valued Map. Ledger 9.1.0.1 finalized the
deployment at height 66012 and the four calls at heights 66015, 66018, 66021,
and 66024. The checked return sizes were 1, 2, 2, and 0 in both Maps. The inactive
call preserved the exact state bytes. Reset restored the exact constructor bytes.
[Lean fixture](../../tests/RecordMapCollections.lean) · [Finalized evidence](record-map-collections-localnet-receipt.json)

Compile the fixture with the ZKIR 3.2.1 target and `--emit ledger`. Assemble an
authenticated `update` bundle as described in [Public entrypoint bundles](portable-artifacts.md).
The focused Rust test needs the bundle directory, its manifest SHA-256, and
the public parameter cache used for the run.

```sh
NOCTIUM_RECORD_MAP_COLLECTIONS_BUNDLE=PATH_TO_BUNDLE \
NOCTIUM_RECORD_MAP_COLLECTIONS_MANIFEST=MANIFEST_SHA256 \
NOCTIUM_RECORD_MAP_COLLECTIONS_PARAMETER_CACHE=PATH_TO_TRUSTED_PARAMETER_CACHE \
NOCTIUM_RECORD_MAP_COLLECTIONS_NODE=http://127.0.0.1:19944 \
  cargo +1.100.0 test --locked --manifest-path runtime/Cargo.toml --lib \
  --no-default-features --features zkir-321,localnet \
  record_map_collections_finalize_distinct_keys_noop_and_reset -- --ignored --nocapture
```

## Nested typed record-key Maps on the development ledger

`NestedRecordMap` stores a UInt16 value under a flat Bool and UInt16 record key
within each Bytes32 owner bucket. The pinned Ledger 9.1.0.1 development chain
finalized the empty deployment at height 66409 and all seven calls through
height 66430. The strict lookup read 11, and the removal changed the selected
key’s membership from true to false. The finalized data matched native
execution after every call and retained two owner buckets.
[Lean fixture](../../tests/NestedRecordMap.lean) · [Finalized evidence](nested-record-map-localnet-receipt.json)

Use `--emit ledger` on the ZKIR 3.2.1 target. Assemble authenticated bundles in
subdirectories named `initializeOwner`, `upsert`, `lookup`, and `removeMemo`.
The manifest pins are a JSON object keyed by entrypoint name.

```sh
NOCTIUM_NESTED_RECORD_MAP_NODE=http://127.0.0.1:19944 \
NOCTIUM_NESTED_RECORD_MAP_BUNDLES=PATH_TO_BUNDLES \
NOCTIUM_NESTED_RECORD_MAP_MANIFESTS=JSON_OF_MANIFEST_DIGESTS \
NOCTIUM_NESTED_RECORD_MAP_PARAMETER_CACHE=PATH_TO_PUBLIC_PARAMETER_CACHE \
  cargo +1.100.0 test --locked --manifest-path runtime/Cargo.toml --lib \
  --no-default-features --features zkir-321,localnet \
  nested_record_map_finalizes_and_preserves_outer_and_inner_siblings -- --ignored --nocapture
```
