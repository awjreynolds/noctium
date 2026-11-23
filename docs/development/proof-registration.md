# Source proof registration and audit policy

`Noctium/Verification.lean` defines typed functional and privacy obligations for an actual source contract and a finite entrypoint index. Authors use ordinary Lean definitions, theorem terms, tactics and libraries. The registration command checks the resulting proposition and proof dependencies, rather than approving particular tactic spellings.

This is PA-01, the source-proof foundation. It does not certify native lowering, emitted bytes, keys, deployment or host execution. Every audit result sets `compiledContractVerified` to false. Those required bridges remain in the [proof audit chain](../research/lean-proof-audit-chain.md).

## Typed obligations

`Specification` contains initialization, an invariant, a broad precondition, an enabled/progress domain and a postcondition. `Subject` binds that specification to an actual `Contract` value and a checked `Fin` index into its entrypoints.

`Correctness subject` requires all four fields:

- Initialization establishes the invariant.
- Every accepted execution under the invariant and precondition satisfies the postcondition and preserves the invariant.
- Every invariant/precondition/enabled invocation admits successful execution.
- At least one initialized invocation satisfies the precondition and enabled domain.

The separate enabled predicate matters. An authorization requirement belongs in the accepted-execution postcondition. Putting eligibility in the only precondition would merely assume eligibility rather than deriving it from success. The progress domain expresses when a valid witness ought to succeed. The existence field prevents an entirely impossible progress domain. It does not replace human review of specification strength or intended business policy.

An `AuditPolicy` binds the subject and privacy specification. `FunctionalObligation policy` and `PrivacyObligation policy` are distinct propositions. A theorem of `True`, a proof about another contract/specification, or a functional proof supplied as a privacy proof fails the expected-type check.

```lean
#noctium_register_functional myCorrectness for reviewedPolicy
#noctium_register_privacy myPrivacy for reviewedPolicy
```

These commands create provisional authoring metadata. They do not establish the review authority of `reviewedPolicy`. The separate data-export audit must apply an independently trusted model pin.

Run `#noctium_source_proof_coverage MyContract` after registration to list the contract's entrypoints and the checked roles for each one. The report uses kernel definitional equality to match the contract and pair the full functional and privacy policies. It reports missing roles, ambiguous candidates, and policy mismatches. Repeated identical registrations count once. Native and deployment verification remain false in this report.

The final policy and proof declarations must be closed instances without uninstantiated universe parameters. Generic lemmas remain unrestricted; a small ordinary Lean theorem instantiates them for the concrete audited subject and policy. The transport does not silently choose universe arguments or discharge missing theorem hypotheses.

## Privacy scope

The source observer is fixed to `Outcome`: named public outputs and final public `LedgerState`, with errors included only in the selected outcome scope. Public equivalence derives from actual declared public inputs in declaration order, the same public state and the same `EvalContext`. An author cannot substitute a constant observer or add private-input equality to public equivalence.

The domain is the exact functional invariant and precondition, not the enabled domain. `successfulOnly` compares successful runs within that domain. `allOutcomes` compares all source outcomes within that domain. Neither label automatically covers invalid/ineligible inputs excluded by the precondition. The audit report exposes the precondition and enabled bodies separately.

`ReleasePolicy.none` permits no extra release. `ReleasePolicy.declared f` compares equality of an explicit `Invocation → List Value` release function, avoiding an arbitrary always-false relation. Its body is audit-visible. A function returning every private input would authorize everything, so a custom function is explicitly reported as unlinked to source authorization. PA-01 does not approve such a release policy by type checking it. The pinned policy requires independent review, and source/native release correspondence remains open.

A second regression accepts private UInt inputs bounded by 1, evaluates unsigned subtraction inside a retained equality constraint, and returns a constant public Boolean without `disclose`. Value-flow analysis accepts the contract. Functional correctness and successful-only no-release privacy both hold under a broad canonical-input precondition. Progress requires the separate enabled condition `b ≤ a`. All-outcomes privacy fails: inputs `(0, 1)` return underflow, and `(1, 0)` succeed. Both invocations satisfy the same broad precondition and have identical public inputs/state. The kernel proves this counterexample, so successful-only privacy never implies failure-channel privacy.

The model excludes intermediate effect traces, proof bytes, provider callbacks, storage/network effects and timing. A source functional proof does not imply this scoped privacy property. `tests/Verification.lean` proves a concrete counterexample: a contract intentionally discloses its private Boolean, satisfies its functional specification, and fails canonical no-release privacy.

## Independent model pin and fresh replay

The trusted model export includes the actual policy/subject/specification, both obligation definitions and their dependencies, plus `propext`, `Classical.choice` and `Quot.sound`. An auditor obtains its expected SHA-256 from an independently reviewed and controlled build. A producer's self-reported digest is not a trust anchor.

The producer exports public proof data using the pinned official tools:

```sh
lake env leanexport Your.Proof.Module -- \
  Noctium.Verification.FunctionalObligation \
  Noctium.Verification.PrivacyObligation Your.policy \
  propext Classical.choice Quot.sound > model.ndjson
lake env leanexport Your.Proof.Module -- \
  Your.functional Your.privacy > proofs.ndjson
```

Module loading and theorem elaboration belong in the producer's controlled build environment. The auditor accepts exports as data:

```sh
lake build Noctium.Verification.ExportAudit
python3 scripts/proofs/audit-source-proof.py \
  --model-export model.ndjson --proof-export proofs.ndjson \
  --trusted-model-sha256 "$REVIEWED_MODEL_SHA256" \
  --policy Your.policy --functional-proof Your.functional \
  --privacy-proof Your.privacy
```

Omitting `--privacy-proof` yields `source-functional-only` and `sourcePrivacyChecked: false`. Supplying both valid obligations yields `source-functional-and-scoped-privacy-checked`. Neither status is a compiled-contract certificate or a blanket confidentiality statement.

The driver retains file bytes, checks the external model digest and passes private temporary copies to the trusted Lean checker. It removes candidate `LEAN_PATH`/`LEAN_SRC_PATH` settings. The checker parses the official export format, rejects different same-name model declarations, merges the trusted model, and replays declarations into a fresh kernel environment. It never imports candidate modules or executes their initializers. Quotient primitives receive the kernel's canonical post-check.

After replay, the kernel compares each actual proof type with the trusted expected obligation. The checker walks checked declaration types and bodies directly, including imports. It does not trust imported `collectAxioms` metadata. Every reachable axiom outside the three approved foundational identities rejects. Their declarations are protected by the independently pinned model. This rejects user axioms, sorry/admit and the per-computation axioms generated by native evaluation. Replay alone would accept those derivations relative to their axioms.

Successful results include a version 1 `proofRoles` array in functional-then-privacy order. Each record exposes its role, obligation, policy, proof and sorted axioms from the checked kernel registration. The existing top-level `axioms` union stays unchanged. Current accepted fixtures reach the same three foundational axioms, so the records report per-proof observations rather than a copy of the allowlist.

The report includes inspected specification/release bodies, root declarations and dependencies. Pretty printing serves human review. If the fresh kernel environment lacks numeral or other syntax metadata, the report uses a labelled kernel-expression display instead of rejecting a valid proof or importing candidate syntax handlers. Machine identity comes from the pinned export bytes and matching checked declarations, not display text. Export inputs are capped at 64 MiB each, and the trusted checker process has a 180-second timeout.

## Reproduce the acceptance and rejection cases

```sh
lake env lean tests/Verification.lean
python3 scripts/proofs/check-registration.py
```

The intentional sorry/admit and user-axiom declarations appear only in rejection fixtures. They do not enter the accepted proof closure. The tests exercise valid source functional/privacy proofs, missing privacy, the proved functional-but-not-private counterexample, wrong contract/specification/role, irrelevant `True`, user axioms, sorry/admit, native-computation axioms, wrong model digest and a valid changed specification under unchanged module/declaration names. The latter rejects both as an altered model and as a model collision in the proof closure.

The same script creates a separate model pin and proof export for the UInt failure-channel fixture, preserving the original fixture model roots and digest. It checks successful-only/no-release scope through the audit driver, rejects substituting that proof for all-outcomes privacy, and replays the functional proof, successful-only privacy proof and all-outcomes counterexample with the official checker. This UInt export also exercises numeral display in the fresh kernel environment.

## Remaining trust boundary

The repository, audit driver, pinned Lean/export parser/kernel executables and controlled tool search path are trusted. Full immutable source/import/build-product provenance, sandboxed producer builds, independent-kernel qualification and authenticated distribution of reviewed policy pins belong to PA-02 and later release assurance. `specificationReviewVerified` stays false. A correct proof relative to an approved pin does not show the pin reflects business intent.

Source/native preservation, exact byte certificates, authenticated key/deployment identity and privacy of native transcripts/proof bytes remain mandatory open gates. Model hash/oracle assumptions remain explicit in contract specifications. Runtime secrets and invocation data must stay outside public proof-production inputs and audit bundles.
