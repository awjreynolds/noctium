# Confidential-token integration

`examples/openzeppelin/ConfidentialToken.lean` adapts the registration, credit, sweep, transfer, burn, memo maintenance and query paths from OpenZeppelin's confidential fungible token at
revision `f85f1a23685c6bbedfc8c2589ae3aa128aff7c46`. Noctium compiles the source
directly to native ZKIR and ledger operations. This milestone covers sixteen
entrypoints from the sixteen-entrypoint reference workload.

`registerWithKey` proves the account ID is SHA-256 of the private account secret
and proves ownership of the nonidentity registered encryption key. It initializes
spendable and pending balances with the curve-identity encryption of zero.
`mint` adds encrypted value to pending funds, prepends an ECDH memo, advances the
recipient's credit counter and changes public supply in the same transaction.
`sweep` authenticates the wallet and merges pending funds into spendable funds.
`transfer` proves the sender's plaintext balance, debits spendable funds, and
credits the recipient's pending funds with a memo and counter update.
`burn` authenticates the sender, subtracts encrypted spendable funds and public
supply atomically, and preserves pending funds, memos and credit counters.
`_move` uses the same conserving debit/credit path and permits self-moves.
`transfer` retains its self-transfer rejection. `clearMemos` authenticates both
wallet secrets and checks the current credit epoch before resetting only the
caller's memo List. A stale epoch rejects clearing after a concurrent credit.
The views expose supply, registration, spendable/pending ciphertexts and account
ID computation. Missing ciphertext entries return curve-identity encrypted zero.
Ciphertext results use named typed point components; nominal composite ABI
layouts remain separate work. `approve` refunds the prior owner ciphertext,
proves the refunded spendable balance, then replaces the escrow with paired
owner/spender encryptions and an owner memo. `transferFrom` consumes the
spender-authenticated escrow and credits recipient pending funds. `burnFrom`
consumes escrow and subtracts public supply. Both refresh the owner memo and
advance the permanent owner/spender spend counter. `allowance` returns those encrypted
components, with identity/zero defaults for an absent owner or spender.

| State | Representation |
| --- | --- |
| encryptionKeys | Account ID to two Native key coordinates |
| balances, pending | Account ID to four Native ciphertext coordinates |
| memos | Account ID to a List of three-Native ECDH memo records |
| creditEpochs | Account ID to a native u64 Counter |
| escrow | Owner and spender IDs to two ciphertexts and an owner memo |
| escrowSpendEpochs | Owner and spender IDs to a permanent u64 Counter |
| name, symbol, decimals | Sealed constructor metadata |
| initialized | Public initialization precondition |
| totalSupply | Public UInt128 supply |

The source takes candidate IDs, points and ciphertext coordinates as circuit
inputs. It checks account IDs against private secrets, keys against registered
keys, and every candidate ciphertext against actual ordered ledger reads before
writing. A candidate input is not trusted state. The account ID is returned as
a typed Bytes32 result bound to the native output commitment.

A witness helper now returns a logical Bytes32 value directly, with
[focused source/host/native evidence](bytes32-witness-output.md). Approval's
grouped ciphertext result still uses a public account-ID candidate constrained
against the private secret. A separate focused fixture also returns Bytes32
with a UInt8 count in a checked record. General nominal result layouts remain
separate ABI work. The helper analyzer enforces a maximum expanded depth
of 256. Typed point candidates avoid unused parameters within this bound.

Private account and encryption secrets come from wallet-scoped native witness
reads. A typed callback supplies a UInt248 plaintext claim indexed by the sender's
ciphertext. The circuit checks the claim through ElGamal decryption. The host also
supplies a private seed for encryption and memos. The credit epoch is cast to a
Native/Field before hashing, matching the reference's explicit Field cast.
Derived random scalars must be nonzero. Production seed freshness and secrecy
remain wallet responsibilities.
The deterministic seeds in the native fixture are public test data.

The focused reference check compares Noctium's account ID and domain-prefixed ElGamal scalar with results from Compact Runtime 0.21.0 on OpenZeppelin's public `elgamal-ek-A` fixture. The same check compares the ECDH memo's two ephemeral coordinates and masked amount with OpenZeppelin's fixed ciphertext at the pinned revision. The Noctium case runs the generated ZKIR through Midnight's native checker. [Noctium fixture](../../runtime/tests/derived_crypto.rs) · [OpenZeppelin ElGamal test](https://github.com/OpenZeppelin/compact-contracts/blob/f85f1a23685c6bbedfc8c2589ae3aa128aff7c46/contracts/src/crypto/test/ElGamal.test.ts) · [OpenZeppelin memo vector](https://github.com/OpenZeppelin/compact-contracts/blob/f85f1a23685c6bbedfc8c2589ae3aa128aff7c46/contracts/src/crypto/test/EcdhMask.test.ts)

The native lifecycle case registers two wallets, mints to the first wallet's
pending pool, sweeps, transfers to the second wallet's pending pool, then burns
two from the sender. Alice ends with five spendable, Bob with five pending and
zero spendable, and public supply is ten. It checks
decrypted balances with independent group arithmetic, public supply, memo Lists
and credit counters, then rejects a valid re-randomized old-ciphertext candidate which preserves
plaintext but differs from the ledger record. The same selected-3.2.1 native
sequence checks all five views, then self-moves one from Alice spendable to
Alice pending. Supply stays ten and Alice's credit epoch advances to two.
Clearing with epoch one rejects. Clearing with epoch two empties only Alice's
memo List and preserves the epoch and other ledger state. Self-transfer and
wrong-key clearing also reject. The expanded focused native case passes in 0.56 seconds.

The same native test now checks the mint epoch guard before the valid mint. It
runs the typed witness and native Impact check twice from the same registered
recipient pre-state, keeping recipient, public key, private amount, seed and
previous pending ciphertext fixed. Epoch zero rejects as stale, then epoch one
passes and retains the supply, pending credit, epoch and memo assertions.
Reproduce the focused test with:

```sh
cargo +1.100.0 test --manifest-path runtime/Cargo.toml --locked --offline \
  --no-default-features --features zkir-321 --test confidential_token \
  confidential_token_registration_pending_sweep_and_transfer_use_native_relations -- --exact
```

`TokenMinter.claimMint` binds the ordered `Bytes32` recipient and `UInt 128`
amount to the actual `ConfidentialToken.mint` call. The caller discloses the
commitment. The callee discloses the recipient for its ledger map operations
and writes the disclosed updated total supply. The proof records the exact
argument order and the checked supply update.

The focused native test uses fresh caller and callee artifacts. It checks the
mint supply, ciphertext, memo and epoch, then checks one caller counter
advance. Changing either committed argument leaves the caller independently
checkable and prevents the pair from assembling into one intent.
[Caller source](../../examples/openzeppelin/ConfidentialTokenComposition.lean) · [Mint proof](../../proofs/ConfidentialTokenMintSupply.lean) · [Native check](../../runtime/tests/confidential_token.rs)

```sh
mkdir -p build/experiments .lake/build/lib/lean/examples/openzeppelin
artifacts=$(mktemp -d "$PWD/build/experiments/committed-mint.XXXXXX")
trap 'rm -r "$artifacts"' EXIT
target=profiles/midnight-ledger-9-zkir-3.2.1-target.json
lake build noctium
lake env lean -o .lake/build/lib/lean/examples/openzeppelin/ConfidentialToken.olean \
  examples/openzeppelin/ConfidentialToken.lean
.lake/build/bin/noctium compile examples/openzeppelin/ConfidentialToken.lean \
  --target "$target" --emit ledger --emit witness --output "$artifacts/callee"
.lake/build/bin/noctium compile examples/openzeppelin/ConfidentialTokenComposition.lean \
  --target "$target" --emit ledger --emit witness --output "$artifacts/caller"
NOCTIUM_MINT_BINDING_ARTIFACTS="$artifacts" \
  cargo +1.100.0 test --manifest-path runtime/Cargo.toml --locked --offline \
  --no-default-features --features zkir-321 --test confidential_token \
  confidential_token_mint_binds_recipient_and_amount_across_calls -- --ignored --exact
```

### Funded cross-contract mint on localnet

The native Rust test deploys both contracts, registers a synthetic recipient key
and proves the caller and mint together in one DUST-funded transaction. The
finalized receipt includes both contracts' states. It confirms one caller
issuance, a supply increase from zero to 12, credit epoch one, and the expected
pending ciphertext and memo. The test compares both complete tagged post-states
with native execution from the preceding finalized state.

The 2026-11-22 run used Ledger 9.1.0.1 and ZKIR 3.2.1 on the development genesis
`823383ec0302be8417cfcbcc62f21df08f4047bca37aaea89e3f54b550ebae1d`.
Finalized block `86e48eaaddf1cdfede2c10808d56e5874dc3b82b3a5cbeaf910561ae14633a66`
includes the composed mint. The caller was
`5cc249283f623f3f4966ccfaa93c406f5c26c8cd7abd5a50d9234bcf2e3ef42e`
and the token was
`7fa59ac1f5dd9bfa9e8bcf5f87dcdb6c0d5132da034e4afc732daa9845ea3be9`.

For a fresh run, use the compiler commands above, generate each entrypoint's
keys with the pinned native ZKIR tool, and assemble `caller-bundle`,
`register-bundle` and `mint-bundle`. Set `NOCTIUM_CONFIDENTIAL_MINT_BUNDLES` to
their parent directory and `NOCTIUM_CONFIDENTIAL_MINT_SRS` to the parameter
cache. For `CALLER`, `REGISTER` and `MINT`, set
`NOCTIUM_CONFIDENTIAL_MINT_<ROLE>_SHA256` to the manifest digest and
`NOCTIUM_CONFIDENTIAL_MINT_<ROLE>_SRS_SHA256` to the SRS digest. The three
circuits use K9, K13 and K15 in that order. The development fee proof uses
the K10 SRS and DUST keys. [Native key generation](native-toolchain.md) ·
[Bundle assembly](portable-artifacts.md#build-and-use)

```sh
NOCTIUM_CONFIDENTIAL_MINT_NODE=http://127.0.0.1:19944 \
  cargo +1.100.0 test --manifest-path runtime/Cargo.toml --locked --offline \
  --no-default-features --features localnet,zkir-321 --test confidential_token \
  confidential_token_funded_mint_finalizes_registered_key_and_checked_pair \
  -- --ignored --exact --nocapture
```

The delegated-spend nonce preimage fits existing source operations:
`persistentHashVector32([seed, domain, owner, spender, toBytes32(epochNative)])`.
The pinned mixed record hashes four Bytes32 values followed by one canonical
Field, also 32 little-endian bytes. Alignment contributes no hash tags, so both
encodings produce the same 160-byte preimage. The delegated circuits now use this exact preimage. Readable witness
expressions share the existing typed `toBytes32` serialization route. [Native nested-map leaf deletion](native-map-remove.md) now supplies the
ledger primitive used for exact refund/replacement behavior.

The lifecycle then approves two for Bob and replaces the approval with three.
Replacement first refunds the prior two, so Alice ends with one spendable, one
pending and three escrowed. Bob keeps five pending and supply stays ten.
Independent group arithmetic checks both encrypted escrow copies and the owner
memo. Pending balances, credit counters and memo Lists stay unchanged. A valid
rerandomized old owner ciphertext rejects when used as the refund candidate.

Bob then transfers two from Alice's escrow into his pending pool and burns the
remaining one. Both escrow ciphertexts decrypt from three to one to zero, and
the owner memo carries each new remaining amount. Spend epochs advance from
one to two. Bob's pending balance reaches seven and his credit epoch reaches
two. Alice keeps one spendable and one pending, public supply ends at nine.
The delegated transfer consumes distinct spend/credit seed replies. Overspending
rejects with checked unsigned subtraction before native execution.

The [source constructor](constructors.md) takes public name, symbol and UInt8
decimals. It initializes sealed metadata and sets the initialization flag.
Maps and counters start empty and supply starts at zero. The lifecycle uses
`construct_state`, then checks Noctium Token/NOC/6 metadata again at the end.
Opaque strings use native Compress alignment with their exact UTF-8 bytes.

All sixteen reference circuit entrypoints and the constructor metadata path
are present. Nominal result layouts and composition remain open. The completed
localnet scenario now exercises every entrypoint with native proofs and receipts. Constructor execution is off chain,
without a constructor proof on the ledger. Mint is the ungated public-supply
benchmark operation, not a production issuance policy. Native acceptance here
is checker evidence. No new keys, proofs or deployment were created for this
source milestone.

## Native host and staged installation

`runtime/examples/confidential_token_localnet.rs` drives the sixteen-operation
contract through native Rust witness callbacks, proving, DUST funding, signing,
submission and finalized receipt checks. Each accepted private journal commit
provides the opaque state token for the next operation. Input candidates come
from the preceding verified receipt state.

```sh
cargo +1.100.0 run --manifest-path runtime/Cargo.toml \
  --no-default-features --features zkir-321,localnet \
  --example confidential_token_localnet -- HOST_CONFIG.json
```

The host config selects `endpoint`, `policy`, `bundleIndex`,
`bundleIndexSha256`, `parameterCache`, `parameterSource`, `journalDirectory`,
`approveLocalDevelopment` and `waitSeconds` (1–300). The bundle index contains
one object per entrypoint, with `name`, `directory` and `manifestSha256`.
Assemble each source-generated circuit, plan and optional witness sidecars with
matching native keys, compiler metadata, profile, ledger parameters and native
toolchain manifest using `noctium-bundle assemble`. Pin the index digest and
every manifest digest externally. Populate the explicit parameter cache with
the verified public SRS and native DUST material before running the host.

The localnet rejected installing all sixteen keys in one deployment because its
transaction weight exceeded the normal extrinsic limit. The host deploys eight
keys, then installs the remaining eight through a signed native maintenance
update. It rotates the temporary authority from key A to caller-selected key B
with a second signed update, then B locks maintenance with an empty committee
and threshold one. The SDK rejects a stale A rotation attempt before submission
and retains the current state token. Calls stay blocked until the complete
authenticated verifier map and locked authority match the intended contract.
Pure circuits retain an empty guaranteed transcript, as required by native
ledger sequencing.

`WitnessContractTarget::from_staged_state_config` and
`start_installation_client` expose verifier staging. The new
`start_authority_rotation_client` exposes the signed A-to-B replacement.
Recovery uses
`restore_deployment` and `recover_client` with trusted durable journal records,
then reobserves finality and acknowledges the private CAS before issuing a new
state token. The example accepts paired `deploymentAttempt` and `resumeAttempt`
identifiers for recovery. Its scripted scenario starts from the beginning, so
these fields do not resume midway through the token scenario.

This example accepts only the isolated development genesis in the
[localnet guide](../../scripts/localnet/README.md). Wallet and bootstrap signing
secrets are public fixtures. The plaintext callback decrypts the actual witness
request and searches fixture amounts up to 64. Each seed request receives fresh
host entropy. These callbacks demonstrate the host boundary and require a real
wallet implementation for production use. On 2026-11-18, the complete scenario
finished with 17 accepted calls across all sixteen entrypoints.

[Historical receipt evidence](../../tests/confidential-token-localnet-evidence.json)
records the earlier deployment, locked verifier installation and each accepted
call. The final call finalized at block 23680. Supply is nine. Alice holds one
spendable and one pending, Bob holds seven pending and zero spendable, and both
escrow copies and the owner escrow memo decrypt to zero. Bob's credit epoch and
the permanent escrow spend epoch both equal two. The process exited
successfully after checking these values from the verified final receipt state.
This chain scenario approves three once. Approval refund and replacement retain
their separate native checker evidence described above.

[Authority-rotation receipt evidence](../../tests/native-authority-rotation-localnet-evidence.json)
records a fresh isolated run with the staged install, A-to-B rotation, final
lock, stale-A rejection and all seventeen post-lock calls. It covers this
single-key rotation flow and does not qualify general verifier-key or IR
maintenance equivalence.
