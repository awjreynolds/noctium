# Typed source witnesses

The exact source revision and qualification scope are recorded in [typed-witness qualification](typed-witness-qualification.md), including bounded native evidence for profiles 3.2.0 and 3.2.1.

Noctium compiles finite Lean helper programs into a native circuit and an ordered private execution plan. Rust executes the plan. A C++ application drives the same interpreter through the C ABI. Neither path requires Node.

Witness providers supply untrusted values through explicit operation and capability declarations. A returned value grants no circuit truth, disclosure permission or ledger authority. Circuit constraints still check the resulting private inputs.

For straight-line scalar contracts, start with [the private state counter](../../examples/PrivateStateCounter.lean).
`noctium_private_state` declares wallet-owned typed cells. `noctium_witness` declares
an untrusted callback. A `noctium_witness_circuit ... where` body reads private
cells, states acceptance conditions with `prove`, and stages updates through the
same Rust execution plan described below. `prove` creates circuit constraints,
not Lean theorems. A private read or calculation needs no `disclose`. A public
result derived from either needs explicit release.

This source form supports Native, Bool, bounded UInt and Bytes32 values, with Unit
callback results. Typed callbacks and private cells also support `JubjubScalar`
and `JubjubPoint`. The `.observations.json` records authored proof conditions
separately from generated validity checks for source review. Composite curve
schemas and structured source branches remain separate work.

Use `assertUnit(condition, "message")` to attach a static message to a readable
assertion. The message appears in the failed result from the local portable
`Session` witness runner, which helps distinguish assertion sites. The one-argument
form keeps its generic failure. These messages stay in the portable control plan;
they do not enter ZKIR or change the circuit relation. Native checking still
rejects a false assertion through the circuit constraints.

On the ZKIR 3.2.1 profile, a provider can return a private `Secp256k1Point`
to a readable circuit. `keccak256(point)` executes inside the Rust witness
session. The native checker binds the same digest to the entrypoint return.
A reply tagged with a different curve leaves the request pending for a
corrected reply. [Typed point example](../../tests/TypedPointKeccak.lean) · [Native check](../../runtime/tests/witness_control.rs)

One circuit can read private cells of different supported scalar types. To opt
in, register `private_state.read.v1` with `argumentSchema` set to `{"key":"Key"}`
and `resultSchema` set to `"SourceCellType"`. Use the authenticated witness
plan to register each read's name, capability and exact key. Each request
reports its declared type, such as `Bool` or `UIntRange<256>`, and the runtime
validates the response against it. A host that supplies a concrete result
schema still restricts reads to that type. Declare a record cell with
`cell receipt : Payload receiptWire`. The reading circuit lists the same codec
in `using`. It receives a typed record from the host, projects checked fields,
and requires explicit disclosure at public sinks. The mixed-cell fixture reads
the record beside a counter, a flag and a Jubjub key pair. It stages a replacement
receipt and reads it back within the same invocation. The native checker rejects
an altered receipt or inconsistent scalar and point.
[Mixed-cell example](../../tests/PrivateStateMixed.lean)

Declarations describe access requests. The host still grants storage permissions.
Generated keys use `noctium/<qualified-schema>/<field>`. Grant a schema with
the slash-terminated prefix `noctium/<qualified-schema>/`, or selected exact keys.
The commit capability must cover every staged key.

The counter reads the public ledger count and checks the requested increment.
Entrypoint bindings describe those public transcript inputs separately as
`ledgerInputs`. Supply only the original circuit arguments to source execution.
Native execution obtains ledger read values from its admitted contract state,
not from witness callbacks or caller-supplied source arguments. Multi-operation
proof and accepted-state qualification remains tracked in
[current-state integration](https://github.com/awjreynolds/noctium/issues/67).

[`tests/WitnessSource.lean`](../../tests/WitnessSource.lean) contains the source examples. They cover scalar calls, nominal composite arguments and results, repeated helpers, Unit and empty nominal results, private reads, staged writes and rejected disclosure. The scalar example stages `cache/last = 1`, reads the staged value, calls a helper twice, checks the replies against a public value and stages the final result.

[`tests/WitnessDisclosure.lean`](../../tests/WitnessDisclosure.lean) checks direct and helper-mediated leaks. Disclosing constants inside a branch does not disclose its private witness guard. The host plan requires explicit disclosure of the guard itself.

Use `default(Payload receiptWire)` in a readable witness circuit whose
`using` clause lists `receiptWire`. Noctium builds the typed zero leaves
from the checked codec layout and reconstructs the logical return value.
The fixture covers a record, a vector of records, an absent Maybe with
a record payload, and an Either with both fields defaulted.
[Composite defaults fixture](../../tests/CompositeDefaults.lean)

Use `some(record)` to retain the checked payload and set `is_some`. Use
`none(Payload receiptWire)` for an absent value with the payload's typed
defaults. A public return containing a private payload requires explicit
disclosure. [Composite Maybe fixture](../../tests/CompositeMaybe.lean)

`Helpers.Wire.maybe` builds a named Maybe codec from the payload codec.
Use the resulting codec for a `Payload` argument. The host and circuit
check the tag and every field against the declared types. A supplied
false tag retains the supplied payload, matching the Compact call ABI.
The fixture returns the exact record and writes its tag to a Bool cell.
[Lean fixture](../../tests/CompositeMaybeInput.lean) · [Compact fixture](../../tests/compact/composite-maybe-input.mjs)

`either(isLeft, leftValue, rightValue)` evaluates the three arguments once
in order. A true tag retains the left payload and supplies the right
payload's typed default. A false tag retains the right payload and
supplies the left payload's typed default. The return layout orders
`is_left`, `left`, and `right`. Public returns still require disclosure
for private inputs that flow into them.
[Composite Either fixture](../../tests/CompositeEither.lean)

`Helpers.Wire.either` builds a named Either codec from the two arm codecs.
Caller-supplied values retain the tag and both checked arms, matching the
Compact call ABI. The fixture returns the same ordered record and writes
its tag to a Bool cell. [Lean fixture](../../tests/CompositeEitherInput.lean) · [Compact fixture](../../tests/compact/composite-either-input.mjs)

The CI artifact check runs both ignored native input tests against fresh
ledger and witness output. It covers three accepted Maybe values, two rejected
Maybe inputs, both accepted Either tags, and three rejected Either inputs.
The optional Compact comparison uses compiler 0.36.1 at source commit
`7fa3a117c5e7efe9d2c51da04263e5f0b3509144` and
`@midnight-ntwrk/compact-runtime` 0.21.0. Set the two variables
to absolute paths for those installed tools. The commands use a temporary
Maybe output directory and clean the Either runner's fixed generated directory
after the run.

```sh
set -eu
either_generated=build/experiments/either-input/compact/generated
if [ -e "$either_generated" ]; then
  printf 'Refusing to overwrite existing Compact output: %s\n' "$either_generated" >&2
  exit 1
fi
scratch=$(mktemp -d)
trap 'rm -rf -- "$scratch" "$either_generated"' EXIT
: "${COMPACTC_0361:?set the absolute path to Compact 0.36.1}"
: "${COMPACT_RUNTIME_0210:?set the absolute path to compact-runtime 0.21.0}"
"$COMPACTC_0361" --version | grep -E '^0\.36\.1 \(7fa3a117c'
test "$(node -p 'require(process.argv[1]).version' "$COMPACT_RUNTIME_0210/package.json")" = '0.21.0'
"$COMPACTC_0361" --skip-zk tests/compact/CompositeMaybeInput.compact "$scratch/maybe"
mkdir -p "$scratch/maybe/node_modules/@midnight-ntwrk"
ln -s "$COMPACT_RUNTIME_0210" "$scratch/maybe/node_modules/@midnight-ntwrk/compact-runtime"
NOCTIUM_COMPACT_RUNTIME_DIR="$COMPACT_RUNTIME_0210" \
  node tests/compact/composite-maybe-input.mjs "$scratch/maybe"
node tests/compact/composite-either-input.mjs "$COMPACTC_0361" "$COMPACT_RUNTIME_0210"
```

## Nested Maybe returns

The paired `Maybe<Maybe<UInt8>>` case uses `some` and `none` at both
levels. The outer `none` carries a canonical absent inner Maybe. A
present outer with an absent inner keeps the outer tag. A present
inner value of zero stays distinct from either absent case.

| Outer input | Inner input | UInt8 input | Outer tag | Inner tag | Payload |
| --- | --- | ---: | --- | --- | ---: |
| false | true | 255 | false | false | 0 |
| true | false | 255 | true | false | 0 |
| true | true | 0 | true | true | 0 |
| true | true | 255 | true | true | 255 |

The native return binds these three fields in order and reconstructs a
typed `result`. Replacing the prepared payload of 255 with 254 changes
the call commitment and fails the emitted ZKIR relation check. The test
uses Ledger 9.1.0.1 / ZKIR 3.2.1 and compares generated Compact 0.36.1
(`7fa3a117c`) contract behavior under Runtime 0.21.0. Compact compiles
`inspect` as a pure entrypoint and emits no proving relation for this case.
[Lean fixture](../../tests/NestedMaybeUInt.lean) ·
[Compact reference](../../tests/compact/nested-maybe-uint.mjs) ·
[Native check](../../runtime/tests/composite_maybe.rs)

```sh
set -eu
mkdir -p build/experiments
scratch=$(mktemp -d "$PWD/build/experiments/nested-maybe-uint.XXXXXX")
trap 'rm -rf "$scratch"' EXIT
lake build Noctium.Cli Noctium.Compiler Noctium.Frontend
node tests/compact/nested-maybe-uint.mjs \
  "$COMPACTC_0361" "$COMPACT_RUNTIME_0210" > "$scratch/compact.json"
lake env lean --run NoctiumMain.lean compile tests/NestedMaybeUInt.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --emit witness --output "$scratch/native"
NOCTIUM_NESTED_MAYBE_UINT_DIR="$scratch/native" \
NOCTIUM_NESTED_MAYBE_UINT_COMPACT="$scratch/compact.json" \
  cargo +1.100.0 test --locked --manifest-path runtime/Cargo.toml \
  --no-default-features --features zkir-321 --test composite_maybe \
  nested_maybe_uint_preserves_tags_defaults_and_result_binding -- --ignored --exact
```

## Pass a qualified shielded coin

Use `Noctium.Midnight.QualifiedShieldedCoinInfo.codec` with a `Payload`
parameter. The record carries `nonce` and `color` as `Bytes 32`, a `UInt 128`
`value`, and a `UInt 64` commitment-tree `mt_index`. The fixture checks the
named public input and return through the native relation. Coin membership
and assignment of the index belong to the ledger receive flow.
[Lean fixture](../../tests/QualifiedShieldedCoinInfo.lean) · [Compact fixture](../../tests/compact/shielded-coin-info.mjs) · [Ledger receive flow](compact-shielded-coin-map.md)

## Pass a record to a witness

Declare a witness parameter with the codec that defines its layout.
The circuit lists the same codec in its `using` clause.

```lean
noctium_witness inspect(payload : Payload limitsWire, amount : UInt8) : Bool
```

A call to `witness inspect(payload, amount)` sends one typed record
followed by the amount. The host protocol preserves the record identity
and checked fields. The circuit still constrains the reply where the
contract requires a condition. The matched fixture covers a UInt8,
a Bool and four bytes, including rejection of a wrong-typed callback reply.
[Lean fixture](../../tests/CompositeWitnessArguments.lean) · [Compact fixture](../../tests/compact/composite-witness-arguments.mjs) · [Native check](../../runtime/tests/composite_witness_arguments.rs)

## Compile source

Declare `Helpers.WitnessSignature` values on `Helpers.Program.witnesses`. Each signature names its versioned operation, capability, typed parameters and result. Call a signature with `Term.witnessCall site name arguments`. Site names remain unique within each helper declaration.

Register a circuit with:

```lean
noctium_witness_circuit scalarRelation from scalarProgram entry "scalar"
```

The registered circuit also works inside the existing `noctium_contract` declaration. The source program stays available to the compiler for fresh type and disclosure checks.

```sh
lake exe noctium compile tests/WitnessSource.lean --output /tmp/noctium-witnesses
```

The selected ledger entrypoint emits:

| File | Purpose |
| --- | --- |
| `TypedWitness.ScalarWitness.claim.zkir` | Actual native CALL relation, including Impact operations and `Output []`. |
| `TypedWitness.ScalarWitness.claim.impact.json` | Ordered ledger plan and source circuit schema. |
| `TypedWitness.ScalarWitness.claim.witness.json` | Public signatures, schemas, source identity and exact private-input bindings. |
| `TypedWitness.ScalarWitness.claim.witness.control.json` | Typed private execution plan bound to the CALL relation. |

Standalone circuit bindings use a separate target identity. Their public-return convention does not replace the ledger CALL relation. Host-only plans use `mode: "host"` and have no native binding. Native guarded control remains gated by its own backend work.

The companion binding file has one trailing LF. Its embedded copy in the control plan preserves those exact bytes. Hash the retained raw file, rather than a parsed or reformatted JSON object.

## Public artifacts and private values

Public bindings record original input names and schemas, declaration paths, call sites, invocation ordinals and fresh circuit leaf names. Two executions of the same helper receive separate bindings. Unit and empty nominal results still receive invocation records.

The binding contains the actual emitted relation tree. Runtime checks require a complete correspondence between original inputs, witness result leaves and declared circuit inputs. Aggregate leaves use native field encodings. A flattened Boolean leaf becomes decimal `"0"` or `"1"`; a scalar `Bool` input keeps its Boolean JSON encoding.

[`tests/CurveWitness.lean`](../../tests/CurveWitness.lean) exercises typed curve
callback arguments and results. A scalar uses a canonical decimal object. A point
uses a subgroup-checked affine-coordinate object. Each remains one logical input
in the private host protocol. The native relation expands a point into two field
inputs and retains exact coordinate roundtrip constraints. Scalars retain their
reduce/encode equality bridge. Runtime binding checks require these bridges and
reject a typed curve input relabeled as Native.

The focused selected-3.2.1 check drives both callbacks, rejects a malformed point
reply, retries the pending request, and passes the completed private input map to
the native checker. This extends callback transport and equality constraints.
Additional helper cryptography, composite curve schemas and curve-valued contract
returns remain separate implementation work. Historical
witness proof claims do not extend automatically to this slice. No new keys,
proofs or deployments were generated.

[`tests/CurveHelpers.lean`](../../tests/CurveHelpers.lean) computes ElGamal
ciphertexts inside a witness-backed contract. Typed helper expressions support
scalar conversion, generator multiplication, point multiplication, addition,
negation, coordinate extraction and checked coordinate reconstruction. The Rust
control interpreter calls the same pinned curve implementation used by the
existing circuit evaluator. The runtime executes in process without Node. Every operation propagates its arguments' private origins.

The example obtains a secret key, randomness and bounded 128-bit plaintext from
private providers. Circuit constraints check key ownership, nonzero reduced keys
and randomness, and decryption. Four explicit releases publish the ciphertext
coordinates. Multiple trailing scalar outputs use an existing checked record
result. Single scalar outputs retain their format. These are source circuit
outputs, not typed native CALL returns, which remain separate work.

One selected-3.2.1 source-to-host-to-native example checks the resulting ciphertext
and rejects a wrong secret key. Test randomness is deterministic. Production
randomness remains a wallet obligation. The old scalar diagnostic trace evaluator
rejects curve expressions explicitly. The native control runtime executes them.
This slice generates no keys, proofs or deployments and extends no historical
witness preservation theorem.

[`tests/HashWitness.lean`](../../tests/HashWitness.lean) keeps account and
encryption secrets in Bytes32 private cells. A private seed callback supplies the
invocation randomness, and the source stages the seed in the wallet journal.
Bytes32 is one logical host value with exactly 32 octets. Native binding expands
it into 32 range-checked field inputs. The checked aggregate bytes codec remains
a separate type representation.

Readable witness helpers support Bytes32 literals, persistent hashing of one
Bytes32 value or a bounded vector, Native field hashing, affine point hashing and
explicit degradation to the low 31 bytes as a Native field. Hashing and degradation
retain private origins. Bytes32 equality checks all 256 bits. Public circuit and
native CALL byte returns, general byte lengths and additional byte operations
remain separate work.

The example checks the account ID, derives the encryption key and separate balance
and memo randomness, verifies ElGamal decryption and recovers an ECDH memo. Seven
explicitly disclosed Native outputs publish ciphertext and memo fields. The
public account comparison intentionally makes the match observable through
acceptance. The staged seed stays on the private channel and remains tentative
until the existing journal lifecycle commits it.

One selected-3.2.1 source/host/native example checks independent hash preimages,
ciphertext and memo values, reads two private byte cells, stages one update and
rejects a changed account high byte. Deterministic test seeds establish no
production freshness property. The scalar diagnostic trace still rejects byte
and curve expressions explicitly. No new keys, proofs or deployments were run.

Selected-entrypoint bundles retain optional `witnessBinding` and `witnessControl` roles together. The verifier rejects a missing member, unreferenced role, different entrypoint, changed relation, changed schema or incomplete input map. Existing bundles without witness roles keep their canonical format. An externally trusted manifest digest authenticates retained bytes. A self-hash alone supplies no source authority.

Invocation inputs, evaluated provider arguments, provider results and staged private writes travel through private channels. They do not enter the public artifact files. Host status and scheduling remain visible to the invocation controller. They are excluded from a contract-public privacy claim.

## Private state

A typed private read declares `operation := "private_state.read.v1"`, an explicit source `privateKey` and no dynamic arguments. Runtime checks the declared key, namespace, capability and key prefix. The request metadata excludes the private key value. The private argument channel carries the key and current invocation overlay.

Runtime already owns staged writes. A reply for an owned staged key must match its exact schema and newest canonical value. A wrong reply leaves the pending request and staged journal available for a valid retry. Reads of committed host storage still depend on the host storage service.

Source `stage` accepts scalar and composite values checked against the declared
cell type. For example, `stage Wallet.receipt := record(Payload receiptWire,
{amount := uint(3), okay := false})` stages a whole typed receipt. The next read
in the invocation must return the exact canonical value. Writes stay tentative
in the private journal until the authorized commit. The circuit evaluates the
staged expression. The host owns staging and compare-and-exchange.

A source-bound execution accepts journal writes only from its compiled stage statements. The public manual-stage API remains available for legacy host-policy execution. It does not add writes to a source-qualified invocation.

## Owned native handoff

Prepare the native target before running source callbacks. The target context authenticates the bundle and proving parameters, retains the initial native contract state and creates the deployment nonce once. Its address and entrypoint stay fixed throughout private execution.

Rust applications use the opaque owners in [`witness_execution`](../../runtime/src/witness_execution.rs). Prepare a real `proof::WitnessTarget`, then pass it to `WitnessExecution::from_target`. The host has the frozen address before choosing its private-state namespace. `WitnessExecution::begin` combines those steps when a namespace is already available.

Drive `advance`, `private_request` and `resume_typed` until source execution completes. `prepare_proof` preserves the invocation on a rejected preparation, then transfers ownership to `WitnessProof`. After verified proving, `WitnessProvedCall` starts the separate deployment client and the source-bound CALL client through the existing driver. These types expose no mutable Runtime or replacement private-input map. The pinned proving-parameter digest also follows the invocation through proof preparation and verification.

[`runtime/tests/witness_execution_public.rs`](../../runtime/tests/witness_execution_public.rs) compiles against public crate APIs alone. Its integration test requires authenticated retained artifacts and public proving parameters, supplied through the environment. It covers source callbacks, corrected retries, invocation mismatch, changed SRS, local proving and the consuming client handoff.

## Generate a Rust witness module

```sh
lake exe noctium compile examples/PrivateStateCounter.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --emit witness --bindings rust --output build/private-counter
```

Include `bindings/rust/NoctiumExamples.PrivateStateCounter.advance.rs` as a module in a crate using `noctium-runtime` and `serde_json`. Keep the module with its artifact directory so Rust resolves the embedded control file. The generated `Inputs { arg_expected: 1 }` holds original source arguments. `Inputs::from_target` starts a frozen deployment target. `Inputs::begin_contract_operation` uses an admitted current-state token. Both check the exact control bytes in the authenticated bundle before calling the SDK. The packager verifies the binding embedded in those bytes.

Provider helpers such as `reply_NoctiumExamples_dnextValue` take the current request, attempt ID and Rust result value. They check the declared provider, operation, capability and result schema. The SDK still validates the pending request, attempt, argument and result values. The host supplies its own capabilities and storage services.

The module uses Rust booleans, fixed byte arrays, Unit and unsigned integers through 128 bits. Wider integers and fields use decimal strings. Jubjub values use decimal strings or a coordinate pair. Nominal aggregates and foreign values use schema-checked JSON. The host still owns private values and decides how to store them.

## Native C/C++ handoff

The additive C entrypoints live in [`noctium_native.h`](../../runtime/include/noctium_native.h) and [`noctium_control.h`](../../runtime/include/noctium_control.h):

1. `noctium_native_witness_target_begin` creates the bounded target context from authenticated artifacts, state-only configuration and explicit entropy.
2. `noctium_control_begin_from_native_target` loads the retained plan and freezes the context identity, address and entrypoint before any provider call or stage.
3. Advance the Control session and answer typed requests. Replies carry protocol version, process-unique decimal request ID, attempt ID, operation, capability and schema. Invalid replies retain suspension. Explicit provider failure aborts the invocation.
4. `noctium_native_begin_from_witness` obtains the complete canonical input map from the completed Control session. It accepts no caller-supplied replacement input map or arbitrary journal. Artifact, context, target and input checks precede consumption.
5. Verify and attach the proof through the existing native proof API. The completed proof session retains the actual source Runtime.
6. Deploy through the existing kind-0 client path using a separate deployment namespace. Deployment leaves source CALL writes untouched. `noctium_client_start_from_witness` consumes the source Runtime for the proved CALL and follows the existing funding, approval, submission, finality and private CAS lifecycle.

A rejected handoff preserves a completed invocation for corrected retry. After successful consumption, cancellation belongs to the native proof or client owner. It discards that owned invocation. It does not restore the old Control session or interrupt arbitrary native CPU work.

Chain acceptance and private CAS are separate outcomes. A finalized call does not disappear when private storage reports a revision conflict. Recovery retains typed schemas and the exact source journal through the existing trusted-store protocol.

The single-operation context covers deployment and its first call. The
multi-entrypoint C ABI selects a retained operation and uses an opaque state
token from a finalized, privately committed client. The linked C++ host
executed two typed callbacks against one Ledger 9 deployment, recovering the
first call after restart before the second callback read its committed value.
[Multi-entrypoint ABI and receipt](native-client-abi.md#run-typed-witnesses-against-the-current-state)

The Rust contract-set POC also supports corrected pre-proof retries at an
authenticated current-state checkpoint. `WitnessExecution::begin_contract_operation`
borrows a target and `&mut Option<CurrentStateContext>` and only takes the token
after source-session construction succeeds. `cancel_contract_operation` clears
the tentative session and returns that token. Successful preparation consumes
ownership. This path has one focused lifecycle test, with full multi-operation
ledger integration and process recovery still in issue 67.

## Assurance scope

The source model in [`Noctium/Witness/Semantics.lean`](../../Noctium/Witness/Semantics.lean) separates private source stages from the erased constraint computation. Its execution gate records a witness tape and replays frozen results rather than rerunning providers after erasing writes. Formal claims must identify their checked theorem, admitted source fragment and host assumptions.

`recordInvocation_replayInvocation_matches` connects the actual recording and replay entrypoints. For source runs admitted by the host-boundary trace, and successful compiler/input/tape validation, replay returns the same result or terminal error, ordered tape and cursor. Replay preserves its initial private store and leaves its journal empty. `validateCompleteInputMap_preserves_bindings` separately ties accepted canonical values to the exact original and fresh input names in circuit schema order. These facts do not prove general Helpers-to-circuit preservation.

The failure theorem uses a one-shot model of accepted execution. Its source-only diagnostic trace must stay empty. This excludes a rejected stage-value cast, a denied private write grant, a staged-read reply that contradicts the owned write, and a malformed typed callback. An accepted terminal provider failure stays in the recorded tape and replays with the same error and cursor. The native protocol separately retains a pending request after a malformed or mismatched reply, so a corrected reply retries that request. The theorem does not model those rejected callback attempts as accepted tape events. Diagnostic traces do not enter callback requests, public observations, artifacts or the native ABI.

Native checker, prover, C++ and ledger tests complement those source facts. They do not establish general Helpers lowering correctness, a verified Rust implementation or circuit-proved private storage. Full compiler assurance, native guarded execution and web/mobile packaging remain separate delivery goals.

[`runtime/tests/witness_checker.rs`](../../runtime/tests/witness_checker.rs) changes private witness leaves after host preparation, then invokes the upstream checker on the emitted CALL relation. The tests cover dishonest scalar replies, nominal result fields and noncanonical Boolean and bounded integer encodings. This separates native constraint rejection from provider validation and host assertions.

## Guarded native binding update

[Binding schema2](guarded-witnesses.md) adds closed call guards, conditional provider execution and canonical skipped native slots. Straight-line schema1 bindings retain their existing format. The scoped native case does not extend the earlier source semantic theorems to schema2. General guarded ledger/helper effects and complete compiler preservation remain separate work.
