# OpenZeppelin contract POC

The [implementation milestone](https://github.com/awjreynolds/noctium/issues/68)
rebuilds OpenZeppelin's confidential token with public supply in Lean. The
reference revision is `f85f1a23685c6bbedfc8c2589ae3aa128aff7c46` of
`OpenZeppelin/compact-contracts`. Its composed integration contract supplies the
behavioral benchmark. Its supply operations are deliberately ungated for tests.

Noctium compiles Lean directly to native ZKIR and ledger artifacts. The comparison
uses results, public state, decrypted balance results and native acceptance.
Different instruction sequences and constraint counts are acceptable.

## Implementation order

| Needed capability | Immediate use | Current boundary |
| --- | --- | --- |
| Dynamic map-value and membership reads | Balances, registered keys and allowances | Scalar value reads use native two-part index paths. Membership binds a Bool from the native VM, including after writes. Focused 3.2.1 cases pass and reject forged reads. Missing value keys fail; membership returns false. |
| Multi-entrypoint calls on current state | Registration, transfer and supply calls on one deployed contract | Bundle collection, retained deployment and source/proof/client handoff are implemented. Scalar-only operations also prepare calls without a witness-control sidecar. A focused add/subtract test covers distinct k9/k8 parameters and client startup after one real proof. Integrated multi-operation ledger execution remains open in issue 67. |
| Ledger-backed getter returns | totalSupply, balanceOf and isRegistered | Scalar, Bytes32 and Jubjub entrypoint results now resolve after ledger effects and bind to Midnight’s native communication output commitment. Rust and the C runtime expose named, typed results. Composite returns and the cross-contract claim protocol remain in [issue 50](https://github.com/awjreynolds/noctium/issues/50). |
| Guarded native execution | Missing accounts, balance checks and conditional updates | Scalar reads/writes/require and nested effect-block branches support guarded activity and safe inactive values. Selected-3.2.1 native checks pass; separate write fixtures have real proof/attachment evidence with native Noop/gas agreement. General helper/witness branches and aggregate reads remain open in issue 43. |
| Composite ledger values and byte keys | Account identifiers, encrypted balances and escrow records | Ledger 3.2.1 examples cover Bytes32 keys, nested scalar maps, and guarded record reads and writes with per-field disclosure. Record cells and memo Lists preserve Native, Bytes32 and JubjubPoint types in one aligned payload. Native Counter reads, adjustments, reset and strict less-than comparison use the ledger Bytes8 codec. [Ledger record and List example](native-lists.md). |
| Jubjub and cryptographic source operations | ElGamal balances, key registration, memos and account identifiers | Typed curve operations, byte-derived keys/randomness, affine point hashing, ElGamal binding and ECDH memo recovery have source/native examples. Bytes32 equality checks both field chunks. Typed scalar and point callbacks now use the existing private host protocol. Curve helper calculations now run through the same private host protocol. Curve ledger schemas and further helper byte operations remain open in [issue 70](https://github.com/awjreynolds/noctium/issues/70). |
| Lean port integration | Register, mint, transfer, approve, transferFrom and burn | All sixteen source entrypoints have a completed native-proof localnet scenario with seventeen finalized calls. Nominal return layouts and composition remain open. See the [receipt evidence](../../tests/confidential-token-localnet-evidence.json). |

The complete 47-instruction, 15-type native inventory remains the wider target.
The token workload does not exercise every native instruction.

The account-ID slice has a source-derived selected-3.2.1 native test in
`runtime/tests/persistent_hash.rs`. It checks independent SHA-256 vectors for
32 zero bytes and `00..1f`, exact byte-aligned ledger keys, replacement of an
existing key and preservation of a second key. A wrong expected key and an
altered private transcript fail. The source fixture rejects a hash key without
explicit disclosure. Hashing preserves private-origin labels.

`tests/Issue70HashPreimages.lean` exercises ordered two-value and four-value
preimages, right-padded UTF-8 tags, a nested Native-field hash, and explicit
disclosure at both state-key sinks. Vector hashing has a 1-to-32 element source
limit. Each Bytes32 value uses its pinned FAB alignment, while a Native value
uses one canonical field encoded as 32 little-endian bytes. This source path
covers the token's domain-separated account-key and credit-key preimages. It
does not implement curve operations or typed CALL returns. Modern `encode`
converts each typed digest to two field chunks for ledger-key alignment. A
computed digest does not act as 32 byte leaves.

The selected-3.2.1 native test `runtime/tests/hash_preimages.rs` matches independent
SHA-256 vectors for two secrets, preserves all four resulting ledger keys, and
rejects reversed tag order and a changed private count. The source rejects
undisclosed vector and Native hashes, malformed lengths and changed alignment.
The fixture releases test digests to exercise ledger binding. Token encryption
key derivation must keep its secret hash private and disclose only the public
key. This slice generates no keys, proofs or deployment.

`tests/Issue70Jubjub.lean` uses private Jubjub scalars for the encryption secret,
randomness and plaintext, with public typed recipient and delta inputs. It checks
scalar and recipient-key nonzero conditions, computes `c1 = rG` and
`c2 = (m + delta)G + r·pk`, then checks decryption returns `(m + delta)G`.
Typed scalar inputs retain their original Native leaf and must equal the
modern-Encode representation of their reduced scalar. Typed point coordinates
must roundtrip exactly through the checked native point constructor. The four
coordinates enter the ledger as one existing checked Native-field record. The
record itself carries no point-validity claim. This initial curve fixture does not exercise provider/control witness schemas.
Typed callback transport now has separate evidence in `tests/CurveWitness.lean`.

The selected-3.2.1 native test `runtime/tests/jubjub.rs` passes exact ciphertext
coordinates for two accounts and a full-range public scalar `q - 1`. It rejects
wrong keys, identity keys, zero randomness, changed plaintext, and a private
scalar changed to `q + 7` while retaining the public statement. Typed input
decoding rejects malformed, off-curve and non-subgroup points and noncanonical
scalars. Source producer checks reject removed scalar and coordinate equality
bridges. The source compiler and Rust evaluator also expose `degradeToNative`:
the first 31 digest bytes interpreted little-endian, matching the pinned native
`degrade_to_transient` builtin. Hashing and degradation retain private origins.
`upgradeFromNative` uses the same 31-byte boundary in the other direction. It
keeps the low bytes of a Native field and appends one zero byte. `toBytes32`
preserves the full canonical field encoding.
The claim-specific and generic scalar preservation theorems cover their
selected source fragments. Curve operations still need separate preservation evidence.

### Hash domain conversion evidence

The generated Compact 0.36.1 pure circuits and native ZKIR 3.2.1 checker
agree on both conversion boundaries. A short or overlong digest and a
field value at the modulus fail input checks. Native arguments use canonical
decimal fields and typed Bytes32 values, and the plan declares both
conversion results as public. [Lean source](../../tests/HashDomainConversions.lean) · [Compact oracle](../../tests/compact/hash-domain-conversions.mjs) · [Native checker and proof](../../runtime/tests/hash_domain_conversions.rs)

The native K9 proof verified against the two disclosed conversion results.
Changing either result rejected the proof. Changing only the discarded
digest byte preserved its public statement. The check uses the declared
native proof statement and the same communication randomness in each case.

Compile the source using the ZKIR 3.2.1 target and `--emit ledger`, then
generate keys for `inspect` and assemble its public bundle. Compiler
revision `e82c5d46f6a4e9052142fd8d39deda60450aace1` reproduced the plan
and ZKIR bytes. The checked circuit used 391 rows. The authenticated bundle
digest was `d973ae638da5de85b667a8b1c49d6de1c2795bb655145b6905ba73e7549ec1bd`.
Its K9 parameters digest was `b9009f1098bcefffec3c461ab3a5e3a17f7e5599f0f08c70fcdc55a89227bcbd`.
[Bundle assembly](portable-artifacts.md)

```sh
NOCTIUM_HASH_DOMAIN_CONVERSIONS_DIR=PATH_TO_COMPILER_OUTPUT \
NOCTIUM_HASH_DOMAIN_CONVERSIONS_BUNDLE=PATH_TO_VERIFIED_BUNDLE \
NOCTIUM_HASH_DOMAIN_CONVERSIONS_MANIFEST_SHA256=VERIFIED_MANIFEST_DIGEST \
NOCTIUM_HASH_DOMAIN_CONVERSIONS_PROOF_PARAMETERS=PATH_TO_TRUSTED_K9_PARAMETERS \
NOCTIUM_HASH_DOMAIN_CONVERSIONS_PROOF_PARAMETERS_SHA256=TRUSTED_K9_DIGEST \
  cargo +1.100.0 test --locked --manifest-path runtime/Cargo.toml \
  --no-default-features --features zkir-321 --test hash_domain_conversions -- --ignored
```

[`tests/Issue70DerivedCrypto.lean`](../../tests/Issue70DerivedCrypto.lean)
combines account hashing, domain-separated key and randomness derivation,
ElGamal encryption/decryption checks and ECDH memo recovery. The memo uses a
separate randomness tag from the balance ciphertext. Only ciphertext fields
are explicitly disclosed. Account comparison retains all 256 hash bits.

`persistentHashNativeVector` hashes 1 to 32 canonical Native fields in order,
each as 32 little-endian bytes. `persistentHashPoint(p)` hashes affine
`LE32(x) || LE32(y)`, using two FAB Field atoms. This follows the pinned
[ledger point alignment](https://github.com/midnightntwrk/midnight-ledger/blob/a2b30128ca4b660b73a068e29b56b48ede8c9a74/transient-crypto/src/curve.rs)
and the native persistent-hash encoding. Compressed point bytes produce a
different digest. These representations are not interchangeable.

The selected-3.2.1 native case in `runtime/tests/derived_crypto.rs` matches raw
SHA-256 reference preimages, checks two accounts including zero amount, preserves
the first encrypted record, and recovers the memo. Wrong secrets, a changed
account high byte and an altered private plaintext reject. Private point hashes
remain subject to disclosure checks. This extends an existing `persistent_hash`
opcode rather than adding an opcode name. Typed curve providers now have separate callback evidence. The complete token
remains separate work. Seeds in the fixture are public test data.
Fresh, secret production seeds remain a wallet obligation. No new keys, proofs
or deployments were generated.

[`tests/NativeByteConversions.lean`](../../tests/NativeByteConversions.lean)
adds `toBytes32(value)` and `fromBytes32(Type, bytes)` for Native, JubjubScalar
and JubjubPoint. Fields serialize as canonical little-endian bytes and decode
with explicit modular reduction. Points use canonical compressed bytes, with
subgroup validation. This compressed representation differs from the affine
point preimage used by `persistentHashPoint`.

Raw inputs and computed byte values use the same bounded native-chunk bridge.
Discarded malformed point decodes still reject. Inactive guarded decodes use
the canonical identity encoding, not zero-filled bytes. Compilation and one
focused selected-3.2.1 native smoke passed. Other byte lengths, other curves
and helper/control conversion routes remain outside this slice.

[`tests/NativeByteIndexing.lean`](../../tests/NativeByteIndexing.lean) adds
`byteAt(value, index)` for raw and computed Bytes32 values. Indices are public
compile-time constants from 0 through 31, in byte order. The result is UInt 8.
Hash digests, typed serialization and selected byte strings use native `nth`
followed by one-limb `encode`. Raw byte inputs keep their existing leaf path.
Indexing retains private origins and needs explicit disclosure at public sinks.

The focused selected-3.2.1 example compares first/last SHA-256 bytes, serialized
field bytes and both selector branches against independent byte values. General
byte lengths, slicing, concatenation and dynamic byte indexing remain separate
capabilities. This slice generates no keys, proofs or deployment.

[`tests/CurveHelpers.lean`](../../tests/CurveHelpers.lean) moves ElGamal
calculation into readable witness-backed source. Private callbacks supply the
key, randomness and 128-bit plaintext. The circuit checks ownership, nonzero
key/randomness and decryption before releasing four ciphertext coordinates.
Checked multiple-output records carry these fields into ledger writes. One
focused source/host/native check accepts the expected ciphertext and rejects a
wrong key. This does not yet integrate encrypted balances, memos or token state.

[`tests/HashWitness.lean`](../../tests/HashWitness.lean) joins the existing
account/key derivation, ElGamal and ECDH memo operations to private wallet reads
and a Bytes32 seed callback. The source checks all 256 account bits, keeps key
and seed hashes private, and discloses seven ciphertext/memo fields. Private seed
staging uses the existing tentative journal. One focused source/host/native case
matches independent preimages and output fields and rejects an altered account
high byte. Complete token ledger state and lifecycle integration remain open.

[`tests/NestedEscrow.lean`](../../tests/NestedEscrow.lean) exposes the existing
recursive record backend through two-key source declarations. An owner map
contains a spender map whose values are 11-field aligned Native cells. The
focused native sequence checks insertion, replacement and preservation of other
owner/spender paths, plus a malformed-record rejection. This qualifies storage
shape and path binding, not encryption validity. Counter and Native-field memo
List operations now have separate source/native examples below.

[`tests/NativeCounter.lean`](../../tests/NativeCounter.lean) adds native Counter
reads, immediate increment/decrement and reset for standalone and nested paths.
Storage uses the ledger's eight-byte u64 cell encoding, distinct from Field-aligned
UInt64 values. Updates use native Addi/Subi and retain overflow/underflow rejection.
A focused native sequence checks current-state reads, reset, inactive guards and
codec rejection. `counterLessThan` checks strict UInt64 comparison on standalone
and nested Counters. The paired source and native fixture also checks UInt16
expression amounts for increments and decrements.
See [Counter encoding and scope](native-counter.md).

The first source component is
[`examples/openzeppelin/PublicSupply.lean`](../../examples/openzeppelin/PublicSupply.lean).
It rebuilds the public-supply extension's two accounting blocks with 128-bit
overflow/underflow rejection and explicit public disclosure. It is an ungated
component that still needs atomic pairing with encrypted token effects.
One focused selected-3.2.1 native test checks supply `0 → 5 → 3`, unchanged
initial state, overflow rejection and underflow rejection. It generates no keys,
proof or deployment.

## Reference behavior to retain

The pinned reference exports 16 entrypoints. Its source requires the following
paths, beyond the current scalar map example:

| Entrypoints | Required behavior and implementation owner |
| --- | --- |
| `totalSupply`, `mint`, `burn`, `burnFrom` | Pair supply changes with encrypted token changes atomically. Retain 128-bit supply arithmetic and public mint/burn deltas. [Native state and crypto](https://github.com/awjreynolds/noctium/issues/70). |
| `balanceOf`, `pendingOf`, `allowance`, `isRegistered` | Membership and guarded lookup. Missing entries return valid curve-identity encrypted zeros. Escrow uses nested owner/spender maps and a record containing two ciphertexts and an owner memo. [Ledger ADTs](https://github.com/awjreynolds/noctium/issues/69), [guards](https://github.com/awjreynolds/noctium/issues/43). |
| `computeAccountId`, `registerWithKey` | Exact persistent-hash account identity, domain-separated encryption key ownership, registration uniqueness and encrypted-zero initialization. [Typed crypto](https://github.com/awjreynolds/noctium/issues/70). |
| `transfer`, `_move`, `sweep` | Separate spendable and pending balances. Credit the pending pool, deliver a memo, preserve credit epochs, and sweep through the authenticated encryption key. [Ledger ADTs](https://github.com/awjreynolds/noctium/issues/69), [crypto](https://github.com/awjreynolds/noctium/issues/70). |
| `approve`, `transferFrom`, `burnFrom` | Refund prior escrow, preserve encrypted allowance and owner-readable remaining balance, and bind spend randomness to owner, spender and epoch. [Ledger ADTs](https://github.com/awjreynolds/noctium/issues/69), [crypto](https://github.com/awjreynolds/noctium/issues/70). |
| `clearMemos` | Authenticate the encryption key, check the expected memo epoch and reset the memo list without resetting lifetime credit counters. [Ledger ADTs](https://github.com/awjreynolds/noctium/issues/69). |
| Caller-returning operations | Return the authenticated caller identity, which composing policies use for caller checks. Typed native inputs/returns remain part of [composition](https://github.com/awjreynolds/noctium/issues/50). |

The constructor also retains sealed name, symbol and decimals plus initialization
state. The witness interfaces supply an account secret, an encryption secret,
a plaintext claim indexed by ciphertext, and a fresh invocation randomness seed.
The circuit checks key ownership and plaintext claims. Seed freshness is a wallet
responsibility. Deterministic fixture seeds do not establish production privacy.

These requirements come from the pinned
[token](https://github.com/OpenZeppelin/compact-contracts/blob/f85f1a23685c6bbedfc8c2589ae3aa128aff7c46/contracts/src/token/ConfidentialFungibleToken.compact),
[composed harness](https://github.com/OpenZeppelin/compact-contracts/blob/f85f1a23685c6bbedfc8c2589ae3aa128aff7c46/contracts/test/integration/_mocks/ComposedConfidentialFungibleTokenPublicSupply.compact),
and [ElGamal helpers](https://github.com/OpenZeppelin/compact-contracts/blob/f85f1a23685c6bbedfc8c2589ae3aa128aff7c46/contracts/src/crypto/ElGamal.compact).
They describe port requirements, not implemented capabilities.

Native memo Lists now have a [source/native storage example](native-lists.md).
They preserve prepend order and nested owner/spender paths. Empty head and pop
reject, and pop includes a ledger-enforced nonempty check. Token memo encryption
and transaction policy integration remain separate.

Primitive getters now have [committed results](committed-returns.md), including
post-update reads. Their clear values stay in the application result channel.
The native call records the output commitment. Cross-contract composition still
needs its claim/argument protocol.

The [confidential-token source milestone](confidential-token.md) now runs
registration, pending credit, sweep, transfer, burn, self-moves, epoch-checked memo
clearing, encrypted escrow approval/replacement, delegated transfer/burn and views through native source-witness
execution. It preserves the pending/spendable split and checks a valid forged
candidate against actual ledger state. This covers all sixteen reference circuit entrypoints,
with source-constructor initialization and sealed metadata. A native Rust host
completed seventeen accepted localnet calls across all sixteen entrypoints.
[Public receipts](../../tests/confidential-token-localnet-evidence.json) record
exact state hashes and the final checked balances. Nominal ABI and composition
remain open.

## Minimum checks

Until feature implementation is complete, compile each changed feature group.
Run one focused native example and one
targeted rejection case where its semantics need one. Reuse existing evidence.
Run one integrated localnet demonstration at the completed-port milestone.
Additional proofs, repeated export audits, broad regression campaigns and
duplicate deployments stay in the assurance backlog.

Historical formal qualification remains attached to its recorded source commit.
New POC features do not inherit those proof claims automatically.
This also applies to conditional writes, membership reads and their SDK proof
integration. Their native checks and proof tests are separate evidence.
The map-read extension needs corresponding changes in `GenericStateOps.lean`,
`GenericStateEffectStep.lean` and `GenericStateConverseEffectStep.lean` before
the generic-state proof suite covers the extended compiler. That work belongs
to the [assurance backlog](https://github.com/awjreynolds/noctium/issues/21).
