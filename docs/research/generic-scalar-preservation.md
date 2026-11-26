# Generic scalar translation validation

This proof package concerns the straight-line Native, Bool and UInt scalar relation backend at the recorded source pin. Issue #64 records the qualified source and audit evidence. The newer byte, curve and nested expression constructors still require an updated normalization model and proof. The range-pass preservation theorem builds independently against the current scalar instruction decoder. [Proof assurance ticket](https://github.com/awjreynolds/noctium/issues/21) · [Range preservation](../../Noctium/Verification/RangeDedup.lean)

## Current standalone proof

`ScalarTranslation.lowerCircuit_satisfiable_iff` connects successful source execution to a satisfying witness for the exact accepted and strictly decoded ZKIR. The witness preserves the source input bindings. The theorem requires scalar circuit admission, canonical source inputs and field/hash model agreement. The current arithmetic proof modules feed `ScalarExpressionLowering.lowerExpr_complete`, which covers the expressions admitted by that scalar model. The published qualification below records the earlier source and evidence pins. [Current scalar translation proofs](../../Noctium/Verification/ScalarTranslation.lean)

## Reused implementation

- `Noctium/IR.lean` defines the typed scalar expression and circuit syntax and its actual entry checks.
- `Noctium/Semantics.lean` defines the executable source semantics. UInt operations reject unsupported bounds, narrowing overflow and subtraction underflow. Selection evaluates both arms. A let evaluates its value even when the body does not use the binding.
- `Noctium/Backend/NativeMeaning.lean` provides the existing normalization consumed by the mandatory validator. Normalized values retain ordered assertions and every range requirement, including requirements from unused computations.
- `Noctium/Backend/NativeExpected.lean` independently derives the expected input, assertion, bound, return and Impact schedules.
- `Noctium/Backend/NativeProducer.lean` validates the actual emitted JSON, SSA definitions, opcode preconditions, bound refinements and schedules.
- `Noctium/Backend/Zkir.lean` performs the existing lowering and CSE. `lowerCircuit_validated` proves successful lowering passed the actual mandatory validator against `expectedCircuit (Passes.pruneCircuit circuit)`.
- `Noctium/Verification/NativeRelation.lean` specifies field-level instruction satisfaction for an arbitrary assignment. `NativeRelationJson.lean` decodes the actual scalar instruction representation.

No second compiler or alternate lowering appears in the proof model. `ScalarNormalization.interpret` gives meaning to the symbolic terms already carried by the validator. Its unsupported opcode fallback is unreachable for normalized source expressions and accepted producer instructions.

## Proved normalization boundary

`ScalarNormalization.normalize_success` proves, for every actual scalar expression constructor, successful source evaluation gives a successful actual normalization with the same field value and all retained bounds and assertions satisfied.

`ScalarNormalization.normalize_sound` proves the reverse direction. Its premises are actual `Expr.validate` acceptance, the actual normalization result, canonical typed input/environment agreement, the qualified field/hash implementation agreement and satisfaction of the normalized bounds and assertions. Its conclusion derives successful actual `Expr.eval` execution. Source acceptance and normalization preservation are not premises.

`ScalarNormalization.normalize_exact` packages the equivalence between normalized requirement satisfaction and existence of successful source evaluation.

The proof covers Native modular arithmetic, UInt addition and multiplication without wrap, underflow rejection, narrowing, all scalar casts, Boolean/native conversion, equality, eager select, qualified hashes, let shadowing, unused partial values, assertion sequencing and disclosure erasure.

## Proved circuit boundary

`ScalarNormalization.expectedCircuit_parts` inverts the actual expected-statement constructor. `ScalarNormalization.expectedCircuit_sound` derives successful actual `Circuit.run`, exact named outputs, exact return scalar values and the expected always-active Impact schedule from expected bound and assertion satisfaction.

`CanonicalInputs` supplies only the source input preflight and numeric input agreement: unique environment names, declared inputs, complete typed canonical values and agreement with the corresponding `%input_` values. Native and UInt host numbers are below the field modulus. A UInt host number also lies below its declared maximum, and that maximum lies below `ScalarPolicy.maxUint`. Bool host values use the Bool type. These are explicit typed host-input admission premises, not source constraint or output acceptance. `ScalarValidation.validate_sound` independently derives every native input bound without this host-range premise. `CanonicalInputs.typedEnvironment` establishes the internal alias/range environment from those premises. The theorem does not assume an alias invariant or source constraint acceptance.

The relation schedule contains one singleton Impact group for each public input, in declaration order, and a final group containing all returns when the circuit has outputs. Output alone supplies no authenticated public instance. This standalone circuit result does not prove generic ledger VM interpretation, state effects or accepted contract-call transcript binding.

## Native instruction boundary

The theorem consumes `NativeRelation.CircuitSatisfies`, the explicit field-level native relation premise. Applying the result to an external proof verifier additionally requires agreement between that implementation and these primitive constraints. The pinned checker/prover tests supply scoped implementation evidence; this package does not prove the external verifier, cryptographic soundness or ledger implementation.

Native Assert means nonzero. The producer separately establishes the Boolean precondition before using an assertion as a typed source assertion or a comparison refinement.

`constrain_bits` restricts a canonical scalar to values below `2^bits`. LessThan determines its result only when both operands satisfy the primitive's width precondition. Outside those ranges the model leaves the result unrestricted. A validator proof must derive the preconditions from prior native constraints and fact bounds. Circuit satisfaction does not assume range soundness.

The validator compares nested symbolic terms. Its former derived nested BEq was opaque to the kernel. A total structural comparison now follows the same constructor, string and list order, with kernel-checked equality equivalence and `LawfulBEq`. No algebraic identities enter acceptance.

## Proved generic soundness boundary

`ScalarTranslation.lowerCircuit_sound` composes the actual lowerer gate, independent statement constructor, JSON decoder, validator fold, normalized semantics and original unpruned circuit semantics. The native witness is arbitrary. Its premises include actual successful lowering, actual successful relation decoding, `CircuitSatisfies`, qualified field/hash agreement and exact canonical source input agreement. Source acceptance, normalization preservation and compiler correctness are absent from its premises.

The conclusion derives successful original `Circuit.run`, exact named output values, exact ordered public and private input streams, the full public Impact schedule and host return values. For nonempty source returns, the theorem derives equality between those returns and the final public Impact group. It separately exposes the input bounds established by the actual native validator constraints.

`ScalarValidation.validate_sound` proves the actual mandatory validator fold's fact, comparison, input, assertion and observation invariants. Native assertion nonzero plus an established Boolean bound yields one. LessThan operand preconditions follow from previous fact bounds and native constraints. Exact final counters close the input, assertion and Impact schedules. The actual final-Output shape check closes the host return schedule.

`ScalarNormalization.expectedCircuit_complete` separately proves successful source execution satisfies every requirement of the actual expected statement.

## Proved actual-lowerer completeness

`ScalarTranslation.lowerCircuit_complete` starts with canonical typed host inputs, actual successful `Zkir.lowerCircuit`, actual successful JSON decoding and successful original `Circuit.run`. Decoder acceptance is a syntactic admission boundary. The theorem constructs a native assignment satisfying every instruction, exact public/private input streams, exact public-input singleton Impact groups, the final nonempty return Impact group and exact host returns. Every `%input_` field retains its supplied value.

The theorem does not assume normalization preservation, a cache invariant, source assertion satisfaction beyond the successful source execution, arbitrary validator completeness or any compiler correctness conclusion. Arbitrary validator acceptance alone does not establish completeness, since validator acceptance permits additional constraints which preserve soundness and restrict satisfying assignments.

`ScalarExpressionLowering.lowerExpr_complete` proves the scalar expression constructors in the pinned source against the actual lowering computation. Its subsidiary proofs cover fresh names, cached/fresh primitive branches, eager arms, let alias restoration, assertion sequencing, casts and qualified hashes. `ScalarCircuitLowering` extends the actual typed-input, constraint, output-loop and footer prefixes, constructs all decoded instruction satisfaction, then derives observations through the independent validator. The witness exists before validator soundness identifies those observations.

`ScalarImmediate.fieldImmediate_exact` proves exact emitted-constant parsing. `ScalarInstructionEncoding` proves actual emitted instruction encodings. `ScalarRangeLowering` proves actual UInt constraint-emission witness extension. `ScalarAllocation` proves actual allocation/count monotonicity. `ScalarAdmission` derives identifier and resource facts from actual entry checks, including the final allocation budget used for every recursive subtree. `ScalarStateExtensions`, `ScalarCache` and `ScalarWitness` establish alias, cache and old-assignment frames from the actual empty initial state.

CSE formerly stored pretty-printed tuple keys. Its cache now uses the actual opcode, ordered operand list and optional Nat hash domain as a flat structural key. This removes an unrelated printer-injectivity obligation. Exact byte parity passed across 38 freshly emitted scalar, helper, private-claim and host-control artifact files. A direct IR fixture also preserved bytes across nested shadowing/CSE, escaped and Unicode operand names, opcode/arity differences and distinct hash domains. Its eight independent raw-witness cases passed the pinned 3.2.1 checker. Native compilation used k=7 and 108 rows. The native proof server produced and self-verified a 3,852-byte proof (SHA256 `bf03b67318b56c866bcae312917c0cfe91d9f408204cd5b23ecefaea9583eb76`), after the dedicated server cache received the official k=7 parameters. No ledger transaction was submitted.

Claim-specific exact byte parsing and artifact certificates were qualified in issue #56. Generic raw-byte implementation agreement and artifact binding remain outside this scalar library package. Guarded source lowering stays disabled until its separate qualification. Composite and foreign representations, general state lowering, frontend helper elaboration, other native primitives and whole-compiler claims remain outside this scalar theorem package.

## Verification evidence

`tests/ScalarNormalization.lean` checks structural comparison parity against the former derived comparison over constants, inputs, unary/binary terms, selects and nested hash lists with unequal arities. Independent source examples cover shadowing/CSE, discarded underflow, eager narrowing rejection, casts, assertion error order and hash evaluation. The test also audits the normalization theorem axiom closures.

`tests/ScalarRangeRelation.lean` checks the range-op JSON representation, malformed widths, field relation preconditions and out-of-range LessThan freedom. `tests/ScalarValidation.lean` exercises the generic arbitrary-witness theorem and rejects missing Boolean constraints, omitted Impact, absent comparison preconditions and wrong tightened bounds. Existing NativeProducer, Zkir and BoundedScalars tests exercise the lowering and mandatory gate. `tests/ScalarCseParity.lean` covers structural cache key distinctions, rejects an add-to-mul emitted-program mutant and emits the direct byte-parity relation. `tests/scalars/cse-cases.json` supplies the eight raw-witness cases for the existing scalar checker harness.

Export/replay of the normalization and expected-circuit roots admits only `propext`, `Quot.sound` and `Classical.choice`. Finite compiler/checker/prover tests supplement these kernel proofs. `tests/ScalarTranslation.lean` specializes actual lowering completeness to the shadowing/CSE result 25 and derives arbitrary-witness unsatisfiability for an accepted program containing discarded underflow. Assertion and select tests check eager evaluation and first-error order. Both public theorem axiom closures contain only the three permitted standard axioms.

## Exact proof-role audit

`ScalarExportAudit` requires both generic soundness and native-witness completeness roles. It obtains their required kernel types from fixed declarations in an independently reviewed model export. Candidate proof names never select their expected statements. The checker requires each role in the candidate export, merges exact trusted declarations, replays the data in a fresh kernel environment, compares types with `Kernel.isDefEq` and traverses actual bodies through `Verification.Audit.axiomsIn`.

`scripts/proofs/audit-scalar-proof.py` requires an explicit trusted model SHA256, retains input bytes before checking and strips custom Lean import paths. Candidate modules and initializers are not imported. The result explicitly leaves compiler-build authentication, whole-compiler verification, general ledger state preservation and deployed identity unchecked.

The regression driver `check-scalar-proof-audit.py` tests swapped, missing and weakened roles, a transitive forbidden axiom and a wrong model pin. Its locally generated baseline is a test fixture, not independent model review. The final package requires the externally reviewed model pin. A model or candidate missing the completeness role is rejected. Soundness alone never receives a complete audit result. The final two-role export measures 71,177,434 bytes, so this isolated checker uses a 96 MiB cap with early oversized-file rejection. Bounded regular-file retention also rejects FIFO input before parsing.

## Published qualification

[The receipt](../../tests/generic-scalar-preservation-evidence.json) qualifies source commit `6ed98d2991b14146176da7028588404464d0ba5a`, tree `c829b42d03645eb02d7036fcdbde7cb7bc63a03d`. The parent independently rebuilt the source and all Lean tests from public baseline `7198416` plus the reviewed scalar package. Every one of the resulting commit's 358 tracked blobs and file modes matched that built snapshot. Unpublished disclosure and runtime packages were excluded.

A separate export from that fresh build reproduced the reviewed 71,177,434-byte model, SHA-256 `6e9b4da95bc6bdf305b5a8e32be7585e62ed74efc6942287ff8c38d7828c98d9`. The parent supplied this independent pin to a separate fresh-kernel audit of both candidate roles. Both roles passed exact statement and three-axiom checks. The worker's local mutation suite also rejected all seven swapped/missing/weakened/axiom/pin/size/FIFO cases. Its locally generated baseline is labelled as local, separately from the parent's independently rebuilt model.

Reproduce the reviewed model from the pinned source and Lean toolchain:

```sh
git worktree add --detach /absolute/path/to/scalar-proof-source 6ed98d2991b14146176da7028588404464d0ba5a
cd /absolute/path/to/scalar-proof-source
lake build Noctium.Verification.ScalarTranslation Noctium.Verification.ScalarExportAudit
lake env leanexport Noctium.Verification.ScalarTranslation -- \
  Noctium.Verification.ScalarTranslation.lowerCircuit_sound \
  Noctium.Verification.ScalarTranslation.lowerCircuit_complete \
  propext Classical.choice Quot.sound > /absolute/path/to/model.ndjson
shasum -a 256 /absolute/path/to/model.ndjson
python3 scripts/proofs/check-scalar-proof-audit.py \
  --trusted-model-export /absolute/path/to/model.ndjson \
  --trusted-model-sha256 6e9b4da95bc6bdf305b5a8e32be7585e62ed74efc6942287ff8c38d7828c98d9 \
  --output-dir /absolute/path/to/new-audit-output
```

Review the model source and check the independent digest before using that digest as authority. The model export is regenerated from source rather than committed as a 71 MB repository asset. Replaying these generic library proofs leaves compiler executable authentication, frontend preservation, raw-byte implementation agreement, broader native operations and general ledger preservation unchecked. Existing claim-specific byte/deployment receipts keep their original source identities.
