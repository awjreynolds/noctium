# Compact feature-equivalence baseline

Research checked on 2026-11-16. The public support matrix was checked again on 2026-11-23. Noctium compiles Lean to ZKIR and native Midnight ledger artifacts. The host-neutral witness runtime is a separate implementation track.

The [Noctium feature register](../compatibility/compact-feature-matrix.json) tracks 221 inventory entries across language families, pinned ledger ADT methods, standard-library types, functions and events, and artifact/runtime obligations. Each entry records its current evidence. Equivalence requires evidence for overloads, rejection cases, composition and runtime boundaries.

## Baseline decision and provenance

Compact toolchain 0.36.1, language 0.28.0, is the stable feature reference. The official release was published on 2026-11-11 and uses reference runtime 0.21.0. Midnight's 2026-11-17 client patch lists the same compiler for Preview, Preprod and Mainnet. Noctium's local qualification follows the exact pins recorded in each receipt. [Stable release](https://github.com/LFDT-Minokawa/compact/releases/tag/compactc-v0.36.1) · [Network matrix](https://docs.midnight.network/relnotes/support-matrix)

| Component | Pinned value | Meaning |
| --- | --- | --- |
| Compact feature reference | Toolchain 0.36.1, language 0.28.0 | Latest stable compiler release observed |
| Compiler source | `LFDT-Minokawa/compact`, `7fa3a117c5e7efe9d2c51da04263e5f0b3509144` | Commit resolved from `compactc-v0.36.1` |
| Compact runtime | 0.21.0 | Reference behavior only, forbidden Noctium dependency |
| Emitted circuit format | ZKIR 3.1 | Producer format, distinct from executable version |
| Bundled key generator | ZKIR 3.2.1, `7a51b3385bbf4bce3604df87a7c70867c9ab43c0` | Latest patch fixes a Jubjub key-generation failure |
| Public-network matrix | Toolchain 0.36.1, Compact.js 3.0.2, Midnight.js 5.0.1, on-chain runtime 4.0.2, proof server 9.0.2 | Official 2026-11-17 Ledger 9 client patch |
| Ledger source | 9.1.0.1, `a2b30128ca4b660b73a068e29b56b48ede8c9a74` | Ledger contract/maintenance interface inspected |
| Existing Noctium observation | `da3ffa3b61b0948768ca370b2abc391575e1dbae` | Local source inspected during research |
| Original Noctium local proof of concept | ZKIR 3.2.0, on-chain runtime profile 4.0.1 | Historical evidence tied to the inspected revision |

Sources: [Compact tag](https://api.github.com/repos/LFDT-Minokawa/compact/git/ref/tags/compactc-v0.36.1), [pinned lockfile](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/flake.lock), [patch comparison and ZKIR 3.1 regression output](https://github.com/LFDT-Minokawa/compact/compare/compactc-v0.36.0...compactc-v0.36.1), [ledger tag](https://api.github.com/repos/midnightntwrk/midnight-ledger/git/ref/tags/ledger-9.1.0.1), [local profile](../../profiles/midnight-ledger-9.json), [existing native evidence](../development/native-localnet.md).

The `midnightntwrk/compact` repository distributes releases and points to LFDT-Minokawa for source. Its 0.36.0 tag resolves to `5e4946cca6abd8039e242ebcfc06be01391c35d6`, whereas the actual 0.36.0 compiler source tag resolves to `b5d9e4dfc532fe47011c4f6296e254f4853eb469`. A release-repository commit is not compiler-source provenance. [Distribution README](https://github.com/midnightntwrk/compact/blob/5e4946cca6abd8039e242ebcfc06be01391c35d6/README.md), [source tag](https://api.github.com/repos/LFDT-Minokawa/compact/git/ref/tags/compactc-v0.36.0).

The 0.36.1 patch changes Boolean deserialization lowering and upgrades the key generator. The reviewed reference, standard-library declarations, native primitive declarations and event declarations retain their 0.36.0 blobs. The ADT reference changes its compiler label to 0.36.1. No new source feature was added by this patch. Exact blob IDs appear in the JSON source register. [Pinned comparison](https://github.com/LFDT-Minokawa/compact/compare/compactc-v0.36.0...compactc-v0.36.1).

## What equivalence means

The requested target is equivalent contract capability and observable semantics through Noctium's Lean surface. Compact syntax, its generated JavaScript class shape and its compiler implementation are reference material, not implementation dependencies. A feature requires a supported Lean representation, semantic rules, native lowering, artifact/runtime support and the appropriate acceptance evidence. A low-level ZKIR opcode alone does not satisfy the feature.

Keep three tracks separate:

- Language and standard-library semantics: values, bounded computation, witness/disclosure rules, ledger operations, cryptographic functions, events and contract calls.
- Native integration: canonical encodings, transcript/proof bindings, keys, deployment, portable host execution and lifecycle behavior exposed by ledger interfaces.
- External SDK products: wallet UI, indexer infrastructure, package-manager commands, editors and explorer interfaces. Equivalent adapter capabilities matter where Noctium uses them. Reimplementing those products is not a language-parity requirement.

Arbitrary Lean theorem proving, unrestricted recursion, dependent values of unbounded runtime size and compilation of all Lean programs are separate goals. Lean as implementation/proof language does not make such constructs part of the bounded Compact comparison. Conversely, the small private-claim example does not define the intended language boundary. [Pinned language reference](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/doc/compact-reference.mdx).

No production, build, runtime or mandatory test path should invoke Compact or import its runtime. Conformance evidence should use a pinned specification, independently checked expected values and official native ZKIR/ledger checks. Any externally generated Compact oracle fixtures would need explicit provenance and isolation, with no Compact dependency introduced into Noctium's required toolchain. Identical verifier-key bytes across two different compilers are not a feature-equivalence requirement. Agreement with the keys deployed for each contract is a requirement.

## Language and private execution inventory

| IDs | Surface and required distinctions | Noctium observation |
| --- | --- | --- |
| `C-LANG-BOOL`, `C-LANG-FIELD`, `C-LANG-UINT` | Boolean, native field, bounded/sized Uint, arithmetic, canonical inputs and bounds | Native/Bool literals, add, multiply and equality exist. Uint and general subtraction/conversions are absent |
| `C-LANG-BYTES`, `C-LANG-VECTOR`, `C-LANG-TUPLE` | Fixed bytes, fixed homogeneous vectors, heterogeneous tuples, unit, indexing, slicing, spreads and destructuring | Missing from the supported frontend and IR |
| `C-LANG-STRUCT`, `C-LANG-ENUM`, `C-LANG-ALIAS`, `C-LANG-OPAQUE` | Structs, enums, structural/nominal aliases, supported host opaque values | Missing |
| `C-LANG-SUBTYPE`, `C-LANG-CAST`, `C-LANG-DEFAULT` | Least upper bounds, allowed/rejected conversions, range checks and defaults | Missing as general facilities |
| `C-LANG-SELECT`, `C-LANG-CONTROL`, `C-LANG-ASSERT` | Conditional expressions, guarded effects, short-circuit logic, statement order, return and unit-valued assert | Eager selection and Boolean assertions exist. General control-flow equivalence is absent |
| `C-LANG-LOOP`, `C-LANG-MAPFOLD` | Compile-time bounded loops, anonymous circuits, map and fold | Missing. Ledger Map is a different feature |
| `C-LANG-FUNCTION`, `C-LANG-PURITY`, `C-LANG-GENERICS` | Helper calls, static recursion restrictions, effect/purity analysis, type/natural generics | No general function/generic surface |
| `C-LANG-MODULE`, `C-LANG-SCOPE`, `C-LANG-PRAGMA` | Namespaces, imports/exports, includes, scopes, version targeting | Lean namespaces exist, but corresponding Noctium language contracts are not established |
| `C-PRIVATE-*` | Typed witness calls, private-state initialization/evolution, public-input boundary, direct/indirect disclosure | Explicit scalar private inputs exist. General witness callbacks and disclosure analysis are absent |
| `C-STATE-CONSTRUCTOR`, `C-STATE-SEALED`, `C-STATE-NESTED` | Constructor rules, immutable-after-construction fields, nested ledger ADTs | Runtime configuration initializes scalar cells and empty maps. General language support is absent |

Source coverage: [language reference](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/doc/compact-reference.mdx), [grammar](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/doc/compact-grammar.mdx), [disclosure analysis](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/doc/explicit-disclosure.mdx). Local observations: [frontend](../../Noctium/Frontend.lean), [IR](../../Noctium/IR.lean), [semantics](../../Noctium/Semantics.lean), [runtime](../../scripts/zkir/native-runtime.mjs).

Boundary cases matter. Compact Uint addition/multiplication widen result bounds, subtraction rejects negative results, and native field arithmetic wraps modulo the field order. Nominal numeric aliases recast results into their own bounds. The reference limits unsigned integers to 248 bits and fixed vectors/bytes to 2^24 elements. Loops use constant/natural-parameter ranges or fixed-size input collections. Unbounded local arrays and unrestricted while loops are not implied by ledger collections. [Numeric, loop and implementation-limit rules](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/doc/compact-reference.mdx).

### Uint result bounds: source/prose discrepancy

For ordinary, non-nominal operands `Uint<0..m>` and `Uint<0..n>`, the pinned reference says addition produces exclusive bound `m+n` and multiplication produces exclusive bound `m*n`. The pinned compiler implements tighter bounds:

| Operation | Internal inclusive result maximum | Equivalent exclusive result bound |
| --- | --- | --- |
| Addition | `(m-1)+(n-1)` | `m+n-1` |
| Multiplication | `(m-1)*(n-1)` | `(m-1)*(n-1)+1` |
| Subtraction | `m-1` | `m`, with a runtime nonnegative-result assertion |

This discrepancy changes which programs type-check, including returns, typed const bindings, ledger writes and argument passing. Use the pinned compiler behavior for implementation parity. Do not silently replace these equations with the looser prose rules. This conclusion comes from source inspection, without executing Compact. Native conformance evidence is still required.

The trace is explicit. `expand-modules-and-types.ss` converts `Uint<bits>` to maximum `2^bits-1`, and range `Uint<0..n>` to maximum `n-1`. `langs.ss` labels the normalized argument as the maximum value. In `infer-types.ss`, `condense` removes structural aliases and records nominal identities without adjusting integer bounds. `arithmetic-binop` adds or multiplies these maxima, checks the result against `max-unsigned`, and constructs the resulting unsigned type. `format-type` adds one when printing a range, and `subtype?` compares the inclusive maxima. The safe casts introduced for operands do not change the inferred result bound. [Normalization, lines 1306 onward](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/compiler/analysis-passes/expand-modules-and-types.ss#L1306), [normalized type definition, line 627](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/compiler/langs.ss#L627), [formatter, subtyping and arithmetic inference](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/compiler/analysis-passes/infer-types.ss#L648).

Numeric literals have a minimal prefix range, not singleton-refined types: literal `v` receives inclusive maximum `v`. Thus literal `0` has range `Uint<0..1>`. Explicitly typed variables use their declared type even when initialized from a smaller literal. Parameter-based cases below avoid confusing range inference with later constant folding. The frontend `expand-const` pass splits declarations, rather than folding arithmetic. The pass pipeline runs integer inference before circuit simplification. [Literal typing](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/compiler/analysis-passes/infer-types.ss#L1195), [const expansion](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/compiler/frontend-passes/expand-const.ss), [analysis pass order](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/compiler/analysis-passes.ss), [compiler pipeline](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/compiler/passes.ss).

Nominal aliases form a separate case. Both operands must have the same nominal identity and underlying type. The compiler returns the original nominal type and inserts a checked downcast when the computed maximum exceeds the original maximum. Structural aliases follow the ordinary equations. A preceding `max-unsigned` failure still rejects a nominal operation before the downcast path. [Nominal arithmetic path, lines 743 onward](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/compiler/analysis-passes/infer-types.ss#L743).

These `C-LANG-UINT` case IDs are source-derived expectations, not executed results:

| Case ID | Operands and expression | Required result |
| --- | --- | --- |
| `UINT-ADD-EXCLUSIVE` | Parameters `x,y: Uint<8>`, expression `x+y` | Inferred maximum 510, range `Uint<0..511>`. Return/assignment to this range accepts. Range `Uint<0..510>` rejects. Values 255+255 produce 510 |
| `UINT-MUL-EXCLUSIVE` | Parameters `x,y: Uint<8>`, expression `x*y` | Inferred maximum 65025, range `Uint<0..65026>`. This result type accepts. Range `Uint<0..65025>` rejects |
| `UINT-ZERO-LITERAL` | Parameter `x: Uint<8>`, expression `x+0` | Result remains `Uint<8>`. Repeat with parameter `z: Uint<0..1>` in place of 0 |
| `UINT-DECLARED-ZERO` | Parameter `x: Uint<8>`, binding `z: Uint<8> = 0`, expression `x+z` | Inference uses declared maximum 255 for z. Returning the sum as `Uint<8>` rejects without a cast |
| `UINT-MAX-MUL-BIT` | Parameters `x: Uint<248>`, `b: Uint<1>`, expression `x*b` | Maximum `2^248-1`, accepted as `Uint<248>`. This differs from applying the prose's exclusive-bound multiplication |
| `UINT-MAX-ADD-ZERO` | Parameters `x: Uint<248>`, `z: Uint<0..1>`, expression `x+z` | Maximum `2^248-1`, accepted as `Uint<248>` |
| `UINT-MAX-ADD-BIT` | Parameters `x: Uint<248>`, `b: Uint<1>`, expression `x+b` | Maximum `2^248`, rejected at arithmetic inference, even before a narrower result annotation |
| `UINT-SUB-UNDERFLOW` | Parameters `x,y: Uint<8>`, expression `x-y` | Inferred type remains `Uint<8>`. 0-1 fails, 255-0 succeeds |
| `UINT-STRUCTURAL-ALIAS` | Structural alias for `Uint<8>`, two parameters | Same sum/product maxima and assignment decisions as the ordinary cases |
| `UINT-NOMINAL-ALIAS` | Nominal alias for `Uint<8>`, two parameters | Result retains nominal identity. Sum 255+1 fails its downcast. Sum 1+1 succeeds. Different nominal identities reject statically |

Each accepting assignment case should also be exercised as a circuit return, typed const, ledger write and function argument. Negative cases need stable failure categories. Runtime cases need native checker rejection as well as evaluator behavior. The JSON records the equations, source trace and these case IDs under `C-LANG-UINT`, with related notes on alias and subtyping entries.

Noctium's eager `select` evaluates both arms. This is useful source-subset evidence, but guarded Compact branches also affect witness invocation, assertions and ledger effects. An implementation must define and test those rules before claiming conditional-expression parity. The existing runtime deliberately rejects an unknown reference even in an unselected expression arm. [Native runtime](../../scripts/zkir/native-runtime.mjs), [existing rejection evidence](../development/native-localnet.md).

## Complete ledger ADT heading inventory

Each operation below has its own `C-ADT-<TYPE>-<METHOD>` record. Host-only operations use the `host-ledger-view` layer. All operations come from the pinned [0.36.1 ADT reference](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/doc/ledger-adt.mdx).

| ADT | Circuit-facing operations | Host-only operations |
| --- | --- | --- |
| Kernel | balance, balanceGreaterThan, balanceLessThan, blockTimeGreaterThan, blockTimeLessThan, caller, checkpoint, claimContractCall, claimUnshieldedCoinSpend, claimZswapCoinReceive, claimZswapCoinSpend, claimZswapNullifier, incUnshieldedInputs, incUnshieldedOutputs, mintShielded, mintUnshielded, self | None listed |
| Implicit Cell | read, resetToDefault, write, writeCoin | None listed |
| Counter | decrement, increment, lessThan, read, resetToDefault | None listed |
| Set | insert, insertCoin, isEmpty, member, remove, resetToDefault, size | iterator |
| Map | insert, insertCoin, insertDefault, isEmpty, lookup, member, remove, resetToDefault, size | iterator |
| List | head, isEmpty, length, popFront, pushFront, pushFrontCoin, resetToDefault | iterator |
| MerkleTree | checkRoot, insert, insertHash, insertHashIndex, insertIndex, insertIndexDefault, isFull, resetToDefault | findPathForLeaf, firstFree, pathForLeaf, root |
| HistoricMerkleTree | checkRoot, insert, insertHash, insertHashIndex, insertIndex, insertIndexDefault, isFull, resetHistory, resetToDefault | findPathForLeaf, firstFree, history, pathForLeaf, root |

Cell is implicit for ordinary ledger field types. Set, Map and List are unbounded ledger collections, despite bounded circuit computation. Merkle trees have declared depth 2 through 32. Coin-specific mutations require qualified shielded coin values and transaction-local Merkle index resolution. Map values support nested ADTs. These distinctions need dedicated acceptance cases, not a shared generic map test. [ADT reference](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/doc/ledger-adt.mdx).

Noctium supports Native/Bool cell reads/writes, map insertion and an absent-key requirement. The IR contains `readMap`, but the native lowerer explicitly rejects map value reads. The frontend does not expose general map lookup. Empty-map initialization and a spent-nullifier map are not full Compact Map support. [IR](../../Noctium/IR.lean), [native lowerer](../../Noctium/Backend/Impact.lean), [frontend](../../Noctium/Frontend.lean).

Kernel `caller` has an upstream limitation: a top-level off-chain invocation records no caller before the final unshielded inputs are known. The pinned docs restrict practical use to known contract callers. `balance` observes the start-of-execution balance. `checkpoint` introduces partial-failure boundaries. These semantics need to survive a portable runtime, and must not be replaced with superficially similar host APIs. [Kernel rules](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/doc/ledger-adt.mdx).

## Standard library, cryptography and contracts

The JSON uses `C-STDLIB-<NAME>` for each named API heading, including every standard event. Source declarations and native overloads take precedence where generated prose is stale. [Library API](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/doc/api/CompactStandardLibrary/exports.md), [library implementation](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/compiler/standard-library.compact), [ZKIR v3 helpers](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/compiler/zkir-v3-library.compact).

- Generic data: Maybe/Either, some/none/left/right, MerkleTreeDigest/PathEntry/Path and both path-root helpers.
- Hashes and commitments: transientHash, transientCommit, persistentHash, persistentCommit, degradeToTransient, upgradeFromTransient, keccak256 and sha512. Persistent operations use the documented SHA-256 compression semantics. Exact type alignment, domain separation and padding need vectors. The existing two-input Poseidon primitive does not prove equivalence to these generic APIs.
- Curves and fields: JubjubPoint/JubjubScalar, Secp256k1Point/Base/Scalar, Secp256r1Point/Base/Scalar and Curve25519Point/Base/Scalar. Include coordinate access, Jubjub construction, ecAdd/ecMul/ecMulGenerator overloads, Jubjub ecNeg, foreign-field neg/inv, hashToCurve, casts and canonical identity encodings.
- Signatures: Jubjub Schnorr, secp256k1 ECDSA, secp256k1 Ethereum address derivation, secp256r1 ECDSA and Ed25519. Each has distinct key/message/signature representations and invalid-input cases. The source explicitly includes P256 and Curve25519, even where shorter rendered documentation omits them.
- Token helpers: ContractAddress, UserAddress, PublicAddress, ZswapCoinPublicKey, ShieldedCoinInfo, QualifiedShieldedCoinInfo and ShieldedSendResult. Include nativeToken/tokenType, mint/receive/send shielded and unshielded tokens, immediate shielded sends, mergeCoin/mergeCoinImmediate, evolveNonce, shieldedBurnAddress, ownPublicKey, createZswapInput/output, balance comparisons and time comparisons.
- Serialization: serialize/deserialize, canonical size and byte encoding, aliases and malformed input. The API prose says event-only, but the compiler implementation supports ordinary serializable values and the 0.36.1 regression uses `deserialize<Boolean,1>`. Reject unsupported point, contract, ADT and opaque forms according to the implementation. This mismatch needs a conformance case, not a narrowed feature claim.

Cryptographic declarations: [native operations](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/compiler/midnight-natives.ss), [foreign operations](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/compiler/zkir-v3-natives.ss). Serialization evidence: [lowering](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/compiler/analysis-passes/expand-serialize.ss), [patch regression](https://github.com/LFDT-Minokawa/compact/compare/compactc-v0.36.0...compactc-v0.36.1).

Standard events are ShieldedSpend, ShieldedReceive, ShieldedMint, ShieldedBurn, UnshieldedSpend, UnshieldedReceive, UnshieldedMint, UnshieldedBurn, Paused, Unpaused and Misc. Test schema, tag, payload bytes, ordering, disclosure and constructor rejection. The compiler emits versioned log items. An arbitrary user-defined event type is not part of the reviewed source surface. [Event declarations](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/compiler/midnight-events.ss), [event version and size contract](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/compiler/events.ss).

Contract interfaces and calls require provable, non-generic signatures, disclosed arguments and address, module/signature checks, verifier-key agreement, the callee entry-point hash and communication commitment. Re-entry and exported interface implementations calling witnesses are restricted. Older prose still mentions purity in runtime conformance, but 0.36.0 explicitly removed this field and rejects pure interface circuits. Preserve the release correction in acceptance cases. [Reference](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/doc/compact-reference.mdx), [0.36 changes](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/doc/release-notes/toolchain-0.36.0.md).

Upgrade/authority support belongs to the native ledger integration track. The inspected ledger binding exposes ReplaceAuthority, VerifierKeyInsert/Remove, IrInsert/Remove and signed MaintenanceUpdate with a counter. This is evidence of an available ledger API, not an implemented Noctium upgrade path or a Compact language statement. [Pinned ledger binding](https://github.com/midnightntwrk/midnight-ledger/blob/a2b30128ca4b660b73a068e29b56b48ede8c9a74/ledger-wasm/src/contract.rs).

## Existing evidence and its limits

The existing localnet receipt qualifies one selected workload. Lean source produced native ZKIR and a symbolic Impact plan, independent tooling produced keys, and the isolated ledger finalized deployment and one private claim with exact expected public state. Five altered witnesses failed the official checker. Replay failed during local execution against fetched spent state, without submitting a second transaction. This distinction prevents claiming ledger-side replay rejection from evidence which tests a host-side guard. No tests were rerun for this research. [Receipt narrative](../development/native-localnet.md), [machine receipts](../development/native-localnet-receipts.json).

The initial inspection at `da3ffa3` found two source value types and a small expression/state effect set, with a Node ESM evaluator. Subsequent work adds [native Rust execution and C/C++ providers](../development/native-runtime-abi.md), [public bundle integrity checks](../development/portable-artifacts.md), and a [bounded UInt slice with finalized local ledger evidence](../development/unsigned-localnet.md). General providers/private-state journals, composite encodings, general state constructors, cross-calls, tokens, events and most ADT methods remain absent. The profile still labels itself `source-baseline-unqualified`, which must not silently become a claim of public-network or whole-language qualification. [IR](../../Noctium/IR.lean), [original reference runtime](../../scripts/zkir/native-runtime.mjs), [profile validation](../../Noctium/Target.lean).

Compiler product parity requires more than a circuit file: exported value/type metadata, provable entrypoints, verifier/prover material, manifest sizes/hashes, source mapping, input validation, state views and portable execution context. Noctium need not duplicate Compact's JavaScript product names, but a documented native ABI must cover equivalent behavior. The Compact runtime must remain absent from the resulting dependency closure. [Compiler product reference](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/doc/compact-reference.mdx).

## Acceptance evidence and bounded first packages

The matrix names six evidence kinds: `SEM` for positive/negative source and evaluator semantics, `ZK` for native checker/prover/verifier acceptance and adversarial inputs, `LEDGER` for finalized state/effect outcomes, `ABI` for canonical representations and metadata, `HOST` for the same artifact exercised by two host languages, and `PROVENANCE` for source/tool hashes and dependency closure. A feature stays unverified until every applicable kind has linked results. Unit tests or a broad category label alone do not prove parity.

Start with these bounded packages. They are prerequisites and first slices, not a delivery schedule for all 221 inventory entries.

1. Freeze the comparison contract. Record 0.36.1 source, native ZKIR 3.2.1 source/binaries and native ledger pins. Reconcile the existing 3.2.0/4.0.1 local proof profile with the documented matrix without overwriting its evidence. Produce a semantic source register, stable failure categories and an explicit list of upstream undefined/unsupported cases. Exit evidence: provenance validation and the 0.36.1 Boolean/Jubjub regressions represented as test requirements. No broad code changes are a prerequisite to this package.

2. Establish a portable scalar ABI and two runners for the existing subset. Prerequisite: an agreed schema/versioning and private-state/witness protocol from the portable-runtime track. Use Native/Bool, argument/result validation, eager-selection behavior, ordered reads/writes and rejection fixtures already represented in Noctium. Exit evidence: identical canonical values, outputs, errors and effect plans in two host languages, plus a dependency-closure check excluding Compact. This is runtime substrate, not whole-Compact witness support.

3. Implement bounded integers and their conversions as one language slice. Prerequisites: scalar ABI and agreed source semantics. Cover Uint widths/ranges, arithmetic result bounds, underflow, narrowing, field conversions and boundary diagnostics. Exit evidence: independent value vectors, bad-witness rejection, official native proof verification and one ledger state round trip using Uint. Do not attach arrays, foreign curves or modules to this initial package.

4. Close scalar Cell/Map behavior before adding every collection. Prerequisites: typed key/value encodings and transcript binding rules. Add supported map lookup/member/remove/default/reset/size cases only after specifying each operation's transcript/state layout, including absence failures. Separate constructor/sealed-field behavior from runtime configuration. Exit evidence: scalar positive/negative operations against an isolated ledger, exact state bytes and stale-read rejection. Nested Map values are a later package with its own prerequisite.

5. Expand the inventory into executable semantic cases. Prerequisites: packages 1 and 2, while further language work proceeds. Split every overloaded primitive and ADT family into boundary, malformed-input, effect-order and composition cases. Audit compiler exports/native declarations against this heading-derived register. Decide the next implementation slice from those gaps and measured native backend support. No estimate of total feature-equivalence effort is justified before this expansion.

The following bounded package boundaries support issue creation after the initial baseline is accepted. They are gated candidates, not a promise of an exhaustive roadmap or an implementation order beyond the stated prerequisites.

| Package | Feature IDs and bounded output | Prerequisites and exit evidence |
| --- | --- | --- |
| `CP-01` Typed IR foundation | `C-LANG-UINT`, `C-LANG-CAST`, `C-LANG-SUBTYPE`, `C-LANG-DEFAULT`: bounded scalar representation and rules, building on existing typed expressions | Frozen semantic register and scalar ABI. SEM/ZK boundary vectors and one ledger round trip |
| `CP-02` Composite values | `C-LANG-BYTES`, `C-LANG-VECTOR`, `C-LANG-TUPLE`, `C-LANG-STRUCT`, `C-LANG-ENUM`, `C-LANG-ALIAS`: value layout and construction/access | CP-01, canonical ABI. SEM/ABI tests, matching native proof inputs and outputs |
| `CP-03` Ledger ADTs | `C-ADT-CELL-*`, `C-ADT-MAP-*` first. Separate follow-on slices for Counter, Set, List, MerkleTree and HistoricMerkleTree | Typed value layout and scalar transcript binding. Each ADT gets its own acceptance/rejection/state-byte ledger corpus. Nested ADTs wait for scalar Map completion |
| `CP-04` Cryptographic slices | `C-STDLIB-TRANSIENTHASH`, `C-STDLIB-PERSISTENTHASH`, commitments and byte hashes first. Separate curve/signature packages under their named `C-STDLIB-*` IDs | CP-02, ZKIR 3.2.1 qualification and independent expected vectors. Every overload needs SEM/ZK/ABI cases including malformed points/signatures |
| `CP-05` Contract composition | `C-CONTRACT-INTERFACE`, `C-CONTRACT-CALL`, `C-ADT-KERNEL-CLAIMCONTRACTCALL`, `C-ADT-KERNEL-CALLER` | Effect/purity rules, canonical signatures, multi-contract runtime context and artifact key agreement. Two-contract positive test plus wrong-entrypoint/key/re-entry/witness rejection |
| `CP-06` Events | `C-EVENT-EMIT`, event `C-STDLIB-*` IDs, `C-STDLIB-SERIALIZE`, `C-STDLIB-DESERIALIZE` | CP-02 and guarded effects/disclosure. Start with one event schema, then each standard schema. Exact ABI bytes, order, constructor rejection and ledger observation |
| `CP-07` Assets | Shielded/unshielded token helper `C-STDLIB-*` IDs and kernel mint/claim/input/output IDs | Addresses and composite types, commitments, witness protocol, transaction coin assembly. Separate unshielded and shielded slices, each proving conservation, authorization, change/self-receive and rejected malformed spends |
| `CP-08` Portable runtime ABI | `C-ARTIFACT-HOST`, `C-PRIVATE-WITNESS`, `C-PRIVATE-STATE`, `C-PRIVATE-INPUT` | Agreed versioned protocol. Two languages running identical scalar fixtures first, then each newly added type/effect. HOST/ABI evidence and zero Compact imports |
| `CP-09` Artifact manifest | `C-ARTIFACT-MANIFEST`, `C-ARTIFACT-ZKIR`, `C-ARTIFACT-LEDGER`, `C-DIAGNOSTIC` | Target pins and portable ABI. Version/hash/size/schema validation, provenance, structured errors and exact deployed-key agreement. CP-05 adds interface metadata when its rules are known |

The static-analysis/disclosure and control-flow rules are cross-cutting prerequisites. Do not mark those features complete merely because a dependent happy-path package passes. `C-SDK-MAINTENANCE` requires a separate ledger lifecycle package after artifact key identity is stable.

## Open facts requiring follow-up

The following gaps constrain planning without invalidating the current inventory:

- The network matrix has not adopted 0.36.1. The release declares ledger 9 compatibility, but exact network acceptance of all affected key-generation paths needs a pinned qualification run.
- The 221 entries do not exhaust grammar alternatives, native overloads, compiler options, malformed encodings, alias compatibility or interactions. Source-heading coverage is measurable. Semantic completeness is not yet established.
- Source/docs disagree on Uint result bounds and serialization extent, and contain stale cross-contract purity prose. The pinned implementation resolves the identified rules. Uint cases above remain source-derived expectations until native conformance tests execute. A systematic contradiction audit remains necessary.
- Native ZKIR/ledger support for every foreign primitive, event, ADT and cross-call has not been qualified from Noctium. Library exposure alone does not establish the compiler-to-ledger path.
- The first host-neutral scalar schema and linked language runners are implemented. General providers and private-state commit/failure rules remain separate work. This file does not preempt the [portable runtime contract](../designs/portable-runtime.md).
- Existing local receipts prove a development-ledger subset. Public-network deployment, production assurance, full transaction-atomicity coverage and whole-language equivalence are unverified.
