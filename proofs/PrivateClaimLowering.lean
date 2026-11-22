import proofs.PrivateClaim
import Noctium.Backend.Zkir
import Noctium.Verification.NativeRelation
import Noctium.Verification.NativeRelationJson

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace Noctium.PrivateClaimLowering
open PrivateClaimProofs Verification.NativeRelation

private def ref := Operand.reference
private def imm (value : Nat) := Operand.immediate (scalar value)

/-- Literal typed target program, separately specified from the source and its
lowerer. A separate JSON certificate checks the emitted relation against this. -/
def program : Program := {
  outputArity := 1
  communicationsCommitment := Bool.false
  instructions := [
    .input .«public» "%input_root", .impact (imm 1) [ref "%input_root"],
    .input .«public» "%input_campaign", .impact (imm 1) [ref "%input_campaign"],
    .input .«public» "%input_suppliedNullifier", .impact (imm 1) [ref "%input_suppliedNullifier"],
    .input .«private» "%input_secret", .input .«private» "%input_sibling0",
    .input .«private» "%input_sibling1", .input .«private» "%input_direction0",
    .boolean (ref "%input_direction0"), .input .«private» "%input_direction1",
    .boolean (ref "%input_direction1"),
    .hash [imm 1, ref "%input_secret", ref "%input_campaign"] "%v0",
    .select (ref "%input_direction0") (ref "%input_sibling0") (ref "%v0") "%v1",
    .select (ref "%input_direction0") (ref "%v0") (ref "%input_sibling0") "%v2",
    .hash [imm 2, ref "%v1", ref "%v2"] "%v3",
    .select (ref "%input_direction1") (ref "%input_sibling1") (ref "%v3") "%v4",
    .select (ref "%input_direction1") (ref "%v3") (ref "%input_sibling1") "%v5",
    .hash [imm 2, ref "%v4", ref "%v5"] "%v6",
    .testEq (ref "%v6") (ref "%input_root") "%v7", .assert (ref "%v7"),
    .hash [imm 3, ref "%input_secret", ref "%input_campaign"] "%v8",
    .testEq (ref "%v8") (ref "%input_suppliedNullifier") "%v9", .assert (ref "%v9"),
    .impact (imm 1) [ref "%input_suppliedNullifier"], .output [ref "%input_suppliedNullifier"]]
}

structure Inputs where
  root : Scalar
  campaign : Scalar
  nullifier : Scalar
  secret : Scalar
  sibling0 : Scalar
  sibling1 : Scalar
  direction0 : Scalar
  direction1 : Scalar

def Inputs.streams (input : Inputs) : InputStreams := {
  publicValues := [input.root, input.campaign, input.nullifier]
  privateValues := [input.secret, input.sibling0, input.sibling1, input.direction0, input.direction1]
}

def Inputs.source (input : Inputs) : InputValues := {
  root := input.root.val, campaign := input.campaign.val, nullifier := input.nullifier.val
  secret := input.secret.val, sibling0 := input.sibling0.val, sibling1 := input.sibling1.val
  direction0 := decide (input.direction0 = one), direction1 := decide (input.direction1 = one)
}

theorem source_canonical (ctx : EvalContext) (input : Inputs) (modulus : ctx.modulus = Field.modulus) :
    CanonicalInputs ctx input.source := by
  constructor
  · rw [modulus]; decide
  · simpa only [Inputs.source, modulus] using input.root.isLt
  · simpa only [Inputs.source, modulus] using input.campaign.isLt
  · simpa only [Inputs.source, modulus] using input.nullifier.isLt
  · simpa only [Inputs.source, modulus] using input.secret.isLt
  · simpa only [Inputs.source, modulus] using input.sibling0.isLt
  · simpa only [Inputs.source, modulus] using input.sibling1.isLt

structure InputBindings (input : Inputs) (assignment : Assignment) : Prop where
  root : assignment "%input_root" = input.root
  campaign : assignment "%input_campaign" = input.campaign
  nullifier : assignment "%input_suppliedNullifier" = input.nullifier
  secret : assignment "%input_secret" = input.secret
  sibling0 : assignment "%input_sibling0" = input.sibling0
  sibling1 : assignment "%input_sibling1" = input.sibling1
  direction0 : assignment "%input_direction0" = input.direction0
  direction1 : assignment "%input_direction1" = input.direction1

theorem stream_bindings (hash : Hash) (input : Inputs) (assignment : Assignment)
    (groups : List (List Scalar)) (returns : List Scalar)
    (sat : Satisfies hash program input.streams assignment groups returns) : InputBindings input assignment := by
  have hp := sat.publicInputs
  have hs := sat.privateInputs
  change [assignment "%input_root", assignment "%input_campaign", assignment "%input_suppliedNullifier"] =
    [input.root, input.campaign, input.nullifier] at hp
  change [assignment "%input_secret", assignment "%input_sibling0", assignment "%input_sibling1",
    assignment "%input_direction0", assignment "%input_direction1"] =
    [input.secret, input.sibling0, input.sibling1, input.direction0, input.direction1] at hs
  simp only [List.cons.injEq, and_true] at hp hs
  exact ⟨hp.1, hp.2.1, hp.2.2, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2⟩

structure Checks (hash : Hash) (w : Assignment) : Prop where
  direction0 : w "%input_direction0" = zero ∨ w "%input_direction0" = one
  direction1 : w "%input_direction1" = zero ∨ w "%input_direction1" = one
  leaf : w "%v0" = hash [scalar 1, w "%input_secret", w "%input_campaign"]
  left0 : w "%v1" = if w "%input_direction0" = one then w "%input_sibling0" else w "%v0"
  right0 : w "%v2" = if w "%input_direction0" = one then w "%v0" else w "%input_sibling0"
  node : w "%v3" = hash [scalar 2, w "%v1", w "%v2"]
  left1 : w "%v4" = if w "%input_direction1" = one then w "%input_sibling1" else w "%v3"
  right1 : w "%v5" = if w "%input_direction1" = one then w "%v3" else w "%input_sibling1"
  root : w "%v6" = hash [scalar 2, w "%v4", w "%v5"]
  rootEq : w "%v7" = bit (decide (w "%v6" = w "%input_root"))
  rootAssert : w "%v7" ≠ zero
  nullifier : w "%v8" = hash [scalar 3, w "%input_secret", w "%input_campaign"]
  nullifierEq : w "%v9" = bit (decide (w "%v8" = w "%input_suppliedNullifier"))
  nullifierAssert : w "%v9" ≠ zero

theorem satisfying_checks (hash : Hash) (input : Inputs) (w : Assignment)
    (groups : List (List Scalar)) (returns : List Scalar)
    (sat : Satisfies hash program input.streams w groups returns) : Checks hash w := by
  constructor
  · exact sat.instructions (.boolean (ref "%input_direction0")) (by simp [program])
  · exact sat.instructions (.boolean (ref "%input_direction1")) (by simp [program])
  · exact sat.instructions (.hash [imm 1, ref "%input_secret", ref "%input_campaign"] "%v0") (by simp [program])
  · exact (sat.instructions (.select (ref "%input_direction0") (ref "%input_sibling0") (ref "%v0") "%v1") (by simp [program])).2
  · exact (sat.instructions (.select (ref "%input_direction0") (ref "%v0") (ref "%input_sibling0") "%v2") (by simp [program])).2
  · exact sat.instructions (.hash [imm 2, ref "%v1", ref "%v2"] "%v3") (by simp [program])
  · exact (sat.instructions (.select (ref "%input_direction1") (ref "%input_sibling1") (ref "%v3") "%v4") (by simp [program])).2
  · exact (sat.instructions (.select (ref "%input_direction1") (ref "%v3") (ref "%input_sibling1") "%v5") (by simp [program])).2
  · exact sat.instructions (.hash [imm 2, ref "%v4", ref "%v5"] "%v6") (by simp [program])
  · exact sat.instructions (.testEq (ref "%v6") (ref "%input_root") "%v7") (by simp [program])
  · exact sat.instructions (.assert (ref "%v7")) (by simp [program])
  · exact sat.instructions (.hash [imm 3, ref "%input_secret", ref "%input_campaign"] "%v8") (by simp [program])
  · exact sat.instructions (.testEq (ref "%v8") (ref "%input_suppliedNullifier") "%v9") (by simp [program])
  · exact sat.instructions (.assert (ref "%v9")) (by simp [program])

theorem source_hash_trace (ctx : EvalContext) (hash : Hash) (agreement : HashAgreement ctx hash)
    (input : Inputs) (w : Assignment) (groups : List (List Scalar)) (returns : List Scalar)
    (sat : Satisfies hash program input.streams w groups returns) :
    HashTrace ctx input.source (w "%v0").val (w "%v3").val := by
  have bindings := stream_bindings hash input w groups returns sat
  have checks := satisfying_checks hash input w groups returns sat
  have leaf : w "%v0" = hash [scalar 1, input.secret, input.campaign] := by
    simpa only [bindings.secret, bindings.campaign] using checks.leaf
  have nullifier : w "%v8" = hash [scalar 3, input.secret, input.campaign] := by
    simpa only [bindings.secret, bindings.campaign] using checks.nullifier
  have rootEq : w "%v6" = input.root :=
    (test_eq_assert_sound _ _ _ checks.rootEq checks.rootAssert).trans bindings.root
  have nullifierEq : w "%v8" = input.nullifier :=
    (test_eq_assert_sound _ _ _ checks.nullifierEq checks.nullifierAssert).trans bindings.nullifier
  have left0 : w "%v1" = if input.direction0 = one then input.sibling0 else w "%v0" := by
    simpa only [bindings.direction0, bindings.sibling0] using checks.left0
  have right0 : w "%v2" = if input.direction0 = one then w "%v0" else input.sibling0 := by
    simpa only [bindings.direction0, bindings.sibling0] using checks.right0
  have left1 : w "%v4" = if input.direction1 = one then input.sibling1 else w "%v3" := by
    simpa only [bindings.direction1, bindings.sibling1] using checks.left1
  have right1 : w "%v5" = if input.direction1 = one then w "%v3" else input.sibling1 := by
    simpa only [bindings.direction1, bindings.sibling1] using checks.right1
  constructor
  · simpa only [agreement.modulus] using (w "%v0").isLt
  · simpa only [agreement.modulus] using (w "%v3").isLt
  · have call := agreement.calls (scalar 1) input.secret input.campaign
    rw [← leaf] at call
    exact call
  · have call := agreement.calls (scalar 2) (w "%v1") (w "%v2")
    rw [← checks.node] at call
    rw [left0, right0] at call
    simpa [Inputs.source, apply_ite, scalar_no_wrap 2 (by decide)] using call
  · have call := agreement.calls (scalar 2) (w "%v4") (w "%v5")
    rw [← checks.root, rootEq] at call
    rw [left1, right1] at call
    simpa [Inputs.source, apply_ite, scalar_no_wrap 2 (by decide)] using call
  · have call := agreement.calls (scalar 3) input.secret input.campaign
    rw [← nullifier, nullifierEq] at call
    exact call

/-- Security direction: every satisfying assignment, including an adversarial
internal witness, yields source acceptance and the externally bound result. -/
theorem native_satisfaction_sound (ctx : EvalContext) (hash : Hash) (agreement : HashAgreement ctx hash)
    (input : Inputs) (assignment : Assignment) (groups : List (List Scalar)) (returns : List Scalar)
    (sat : Satisfies hash program input.streams assignment groups returns) :
    claimEntry.circuit.run ctx (inputEnvironment input.source) =
      .ok [("nullifier", .native input.nullifier.val)] ∧
    returns = [input.nullifier] ∧
    groups = [[input.root], [input.campaign], [input.nullifier], [input.nullifier]] ∧
    (input.direction0 = zero ∨ input.direction0 = one) ∧
    (input.direction1 = zero ∨ input.direction1 = one) := by
  have bindings := stream_bindings hash input assignment groups returns sat
  have checks := satisfying_checks hash input assignment groups returns sat
  have trace := source_hash_trace ctx hash agreement input assignment groups returns sat
  refine ⟨hash_trace_circuit_accepts ctx input.source _ _ (source_canonical ctx input agreement.modulus) trace, ?_, ?_, ?_, ?_⟩
  · have out := sat.outputs
    change [assignment "%input_suppliedNullifier"] = returns at out
    exact out.symm.trans (congrArg (fun v => [v]) bindings.nullifier)
  · have publicBinding := sat.groups
    change [[assignment "%input_root"], [assignment "%input_campaign"],
      [assignment "%input_suppliedNullifier"], [assignment "%input_suppliedNullifier"]] = groups at publicBinding
    rw [bindings.root, bindings.campaign, bindings.nullifier] at publicBinding
    exact publicBinding.symm
  · simpa only [bindings.direction0] using checks.direction0
  · simpa only [bindings.direction1] using checks.direction1

/-- Composition uses the existing proved pruning transformation. -/
theorem native_satisfaction_pruned_sound (ctx : EvalContext) (hash : Hash) (agreement : HashAgreement ctx hash)
    (input : Inputs) (assignment : Assignment) (groups : List (List Scalar)) (returns : List Scalar)
    (sat : Satisfies hash program input.streams assignment groups returns) :
    (Passes.pruneCircuit claimEntry.circuit).run ctx (inputEnvironment input.source) =
      .ok [("nullifier", .native input.nullifier.val)] := by
  rw [Passes.pruneCircuit_run]
  exact (native_satisfaction_sound ctx hash agreement input assignment groups returns sat).1

structure Computation where
  leaf : Scalar
  left0 : Scalar
  right0 : Scalar
  node : Scalar
  left1 : Scalar
  right1 : Scalar
  root : Scalar
  rootCheck : Scalar
  nullifier : Scalar
  nullifierCheck : Scalar

def compute (hash : Hash) (input : Inputs) : Computation :=
  let leaf := hash [scalar 1, input.secret, input.campaign]
  let left0 := if input.direction0 = one then input.sibling0 else leaf
  let right0 := if input.direction0 = one then leaf else input.sibling0
  let node := hash [scalar 2, left0, right0]
  let left1 := if input.direction1 = one then input.sibling1 else node
  let right1 := if input.direction1 = one then node else input.sibling1
  let root := hash [scalar 2, left1, right1]
  let nullifier := hash [scalar 3, input.secret, input.campaign]
  {leaf, left0, right0, node, left1, right1, root, nullifier,
   rootCheck := bit (decide (root = input.root)),
   nullifierCheck := bit (decide (nullifier = input.nullifier))}

def computedSource (hash : Hash) (input : Inputs) : InputValues :=
  {input.source with root := (compute hash input).root.val, nullifier := (compute hash input).nullifier.val}

theorem computed_source_canonical (ctx : EvalContext) (hash : Hash) (input : Inputs)
    (modulus : ctx.modulus = Field.modulus) : CanonicalInputs ctx (computedSource hash input) := by
  have original := source_canonical ctx input modulus
  exact {original with
    root := by simpa only [computedSource, modulus] using (compute hash input).root.isLt
    nullifier := by simpa only [computedSource, modulus] using (compute hash input).nullifier.isLt}

theorem computed_trace (ctx : EvalContext) (hash : Hash) (agreement : HashAgreement ctx hash)
    (input : Inputs) : HashTrace ctx (computedSource hash input)
      (compute hash input).leaf.val (compute hash input).node.val := by
  constructor
  · simpa only [agreement.modulus] using (compute hash input).leaf.isLt
  · simpa only [agreement.modulus] using (compute hash input).node.isLt
  · exact agreement.calls (scalar 1) input.secret input.campaign
  · have call := agreement.calls (scalar 2) (compute hash input).left0 (compute hash input).right0
    simpa [compute, computedSource, Inputs.source, apply_ite, scalar_no_wrap 2 (by decide)] using call
  · have call := agreement.calls (scalar 2) (compute hash input).left1 (compute hash input).right1
    simpa [compute, computedSource, Inputs.source, apply_ite, scalar_no_wrap 2 (by decide)] using call
  · exact agreement.calls (scalar 3) input.secret input.campaign

/-- Source acceptance forces the independently calculated target path and
nullifier results. No target satisfaction premise occurs in this direction. -/
theorem source_acceptance_calculation (ctx : EvalContext) (hash : Hash) (agreement : HashAgreement ctx hash)
    (input : Inputs) (outputs : EvalEnv)
    (accepted : claimEntry.circuit.run ctx (inputEnvironment input.source) = .ok outputs) :
    (compute hash input).root = input.root ∧ (compute hash input).nullifier = input.nullifier := by
  have calculated := hash_trace_expressions ctx (computedSource hash input)
    (compute hash input).leaf.val (compute hash input).node.val
    (computed_source_canonical ctx hash input agreement.modulus) (computed_trace ctx hash agreement input)
  have source := successful_source_root_and_nullifier ctx input.source
    (source_canonical ctx input agreement.modulus) outputs accepted
  have rootEnvironment : rootExpression.eval ctx (inputEnvironment input.source) =
      rootExpression.eval ctx (inputEnvironment (computedSource hash input)) := by
    simp [rootExpression, firstNodeExpression, leafExpression, Expr.eval, inputEnvironment, computedSource,
      List.lookup]
  have nullifierEnvironment : nullifierExpression.eval ctx (inputEnvironment input.source) =
      nullifierExpression.eval ctx (inputEnvironment (computedSource hash input)) := by
    simp [nullifierExpression, Expr.eval, inputEnvironment, computedSource, List.lookup]
  rw [← rootEnvironment] at calculated
  rw [← nullifierEnvironment] at calculated
  exact ⟨Fin.ext (Except.ok.inj (calculated.1.symm.trans source.1)),
    Fin.ext (Except.ok.inj (calculated.2.symm.trans source.2))⟩

def computedWitness (hash : Hash) (input : Inputs) : Assignment := fun name =>
  match name with
  | "%input_root" => input.root
  | "%input_campaign" => input.campaign
  | "%input_suppliedNullifier" => input.nullifier
  | "%input_secret" => input.secret
  | "%input_sibling0" => input.sibling0
  | "%input_sibling1" => input.sibling1
  | "%input_direction0" => input.direction0
  | "%input_direction1" => input.direction1
  | "%v0" => (compute hash input).leaf
  | "%v1" => (compute hash input).left0
  | "%v2" => (compute hash input).right0
  | "%v3" => (compute hash input).node
  | "%v4" => (compute hash input).left1
  | "%v5" => (compute hash input).right1
  | "%v6" => (compute hash input).root
  | "%v7" => (compute hash input).rootCheck
  | "%v8" => (compute hash input).nullifier
  | "%v9" => (compute hash input).nullifierCheck
  | _ => zero

theorem computed_assignment_satisfies (hash : Hash) (input : Inputs)
    (direction0 : input.direction0 = zero ∨ input.direction0 = one)
    (direction1 : input.direction1 = zero ∨ input.direction1 = one)
    (root : (compute hash input).root = input.root)
    (nullifier : (compute hash input).nullifier = input.nullifier) :
    Satisfies hash program input.streams (computedWitness hash input)
      [[input.root], [input.campaign], [input.nullifier], [input.nullifier]] [input.nullifier] := by
  have scalarOne : scalar 1 = one := by decide
  have rootCheck : (compute hash input).rootCheck = one := by
    change bit (decide ((compute hash input).root = input.root)) = one
    rw [root]
    simp [bit]
  have nullifierCheck : (compute hash input).nullifierCheck = one := by
    change bit (decide ((compute hash input).nullifier = input.nullifier)) = one
    rw [nullifier]
    simp [bit]
  constructor
  · intro instruction membership
    simp only [program, List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals subst instruction
    all_goals simp only [Instruction.Holds, Operand.read, ref, imm, List.map_cons, List.map_nil,
      computedWitness, scalarOne]
    all_goals first | trivial | exact direction0 | exact direction1 | exact ⟨direction0, rfl⟩ | exact ⟨direction1, rfl⟩ | rfl | skip
    · rw [rootCheck]
      exact Ne.symm zero_ne_one
    · rw [nullifierCheck]
      exact Ne.symm zero_ne_one
  · rfl
  · rfl
  · rfl
  · rfl

/-- Usability direction: every successful source circuit execution with valid
native Boolean encodings admits a satisfying native assignment. -/
theorem source_acceptance_complete (ctx : EvalContext) (hash : Hash) (agreement : HashAgreement ctx hash)
    (input : Inputs) (direction0 : input.direction0 = zero ∨ input.direction0 = one)
    (direction1 : input.direction1 = zero ∨ input.direction1 = one) (outputs : EvalEnv)
    (accepted : claimEntry.circuit.run ctx (inputEnvironment input.source) = .ok outputs) :
    ∃ assignment, Satisfies hash program input.streams assignment
      [[input.root], [input.campaign], [input.nullifier], [input.nullifier]] [input.nullifier] := by
  obtain ⟨root, nullifier⟩ := source_acceptance_calculation ctx hash agreement input outputs accepted
  exact ⟨computedWitness hash input, computed_assignment_satisfies hash input direction0 direction1 root nullifier⟩

/-- Canonical source fields map directly into native field elements. -/
def Inputs.ofSource (ctx : EvalContext) (input : InputValues)
    (canonical : CanonicalInputs ctx input) (modulus : ctx.modulus = Field.modulus) : Inputs := {
  root := ⟨input.root, by simpa only [modulus] using canonical.root⟩
  campaign := ⟨input.campaign, by simpa only [modulus] using canonical.campaign⟩
  nullifier := ⟨input.nullifier, by simpa only [modulus] using canonical.nullifier⟩
  secret := ⟨input.secret, by simpa only [modulus] using canonical.secret⟩
  sibling0 := ⟨input.sibling0, by simpa only [modulus] using canonical.sibling0⟩
  sibling1 := ⟨input.sibling1, by simpa only [modulus] using canonical.sibling1⟩
  direction0 := bit input.direction0
  direction1 := bit input.direction1
}

theorem source_embedding (ctx : EvalContext) (input : InputValues)
    (canonical : CanonicalInputs ctx input) (modulus : ctx.modulus = Field.modulus) :
    (Inputs.ofSource ctx input canonical modulus).source = input := by
  cases input with
  | mk root campaign nullifier secret sibling0 sibling1 direction0 direction1 =>
    cases direction0 <;> cases direction1 <;>
      simp [Inputs.ofSource, Inputs.source, bit, zero, one]

theorem bit_is_boolean (value : _root_.Bool) : bit value = zero ∨ bit value = one := by
  cases value <;> simp [bit]

/-- Eligible source inputs have a native witness. This rules out an always-
rejecting target and covers arbitrary canonical source secrets/paths. -/
theorem eligible_source_complete (ctx : EvalContext) (hash : Hash) (agreement : HashAgreement ctx hash)
    (input : InputValues) (canonical : CanonicalInputs ctx input) (leaf node : Nat)
    (trace : HashTrace ctx input leaf node) :
    let nativeInputs := Inputs.ofSource ctx input canonical agreement.modulus
    ∃ assignment, Satisfies hash program nativeInputs.streams assignment
      [[nativeInputs.root], [nativeInputs.campaign], [nativeInputs.nullifier], [nativeInputs.nullifier]]
      [nativeInputs.nullifier] := by
  dsimp only
  apply source_acceptance_complete ctx hash agreement
    (Inputs.ofSource ctx input canonical agreement.modulus)
    (bit_is_boolean input.direction0) (bit_is_boolean input.direction1)
    [("nullifier", .native input.nullifier)]
  rw [source_embedding]
  exact hash_trace_circuit_accepts ctx input leaf node canonical trace

/-- Satisfaction of an independently decoded JSON tree. Exact tree/program
binding is a separate checked certificate, not a lowering assumption. -/
def ArtifactRelation (json : Lean.Json) (hash : Hash) (streams : InputStreams)
    (assignment : Assignment) (groups : List (List Scalar)) (returns : List Scalar) : Prop :=
  ∃ target, Verification.NativeRelationJson.decode json = .ok target ∧
    Satisfies hash target streams assignment groups returns

theorem decoded_artifact_sound (json : Lean.Json)
    (certificate : Verification.NativeRelationJson.decode json = .ok program)
    (ctx : EvalContext) (hash : Hash) (agreement : HashAgreement ctx hash)
    (input : Inputs) (assignment : Assignment) (groups : List (List Scalar)) (returns : List Scalar)
    (sat : ArtifactRelation json hash input.streams assignment groups returns) :
    claimEntry.circuit.run ctx (inputEnvironment input.source) =
      .ok [("nullifier", .native input.nullifier.val)] ∧
    returns = [input.nullifier] ∧
    groups = [[input.root], [input.campaign], [input.nullifier], [input.nullifier]] ∧
    (input.direction0 = zero ∨ input.direction0 = one) ∧
    (input.direction1 = zero ∨ input.direction1 = one) := by
  obtain ⟨target, decoded, satisfaction⟩ := sat
  have targetEq := Except.ok.inj (decoded.symm.trans certificate)
  subst target
  exact native_satisfaction_sound ctx hash agreement input assignment groups returns satisfaction

theorem decoded_eligible_complete (json : Lean.Json)
    (certificate : Verification.NativeRelationJson.decode json = .ok program)
    (ctx : EvalContext) (hash : Hash) (agreement : HashAgreement ctx hash)
    (input : InputValues) (canonical : CanonicalInputs ctx input) (leaf node : Nat)
    (trace : HashTrace ctx input leaf node) :
    let nativeInputs := Inputs.ofSource ctx input canonical agreement.modulus
    ∃ assignment, ArtifactRelation json hash nativeInputs.streams assignment
      [[nativeInputs.root], [nativeInputs.campaign], [nativeInputs.nullifier], [nativeInputs.nullifier]]
      [nativeInputs.nullifier] := by
  obtain ⟨assignment, satisfaction⟩ := eligible_source_complete ctx hash agreement input canonical leaf node trace
  exact ⟨assignment, program, certificate, satisfaction⟩

/-- Native constraints alone establish source acceptance. No alleged external
host return is assumed. This claim's actual return is authenticated by its final
Impact group, unlike an unbound standalone Output in general. -/
theorem native_constraints_sound (ctx : EvalContext) (hash : Hash) (agreement : HashAgreement ctx hash)
    (input : Inputs) (assignment : Assignment) (groups : List (List Scalar))
    (sat : CircuitSatisfies hash program input.streams assignment groups) :
    claimEntry.circuit.run ctx (inputEnvironment input.source) =
      .ok [("nullifier", .native input.nullifier.val)] ∧
    program.returns assignment = [input.nullifier] ∧
    program.returns assignment = groups.getLastD [] := by
  have sound := native_satisfaction_sound ctx hash agreement input assignment groups
    (program.returns assignment) sat.withObservedReturns
  refine ⟨sound.1, sound.2.1, ?_⟩
  rw [sound.2.1, sound.2.2.1]
  rfl

def DecodedCircuitRelation (json : Lean.Json) (hash : Hash) (streams : InputStreams)
    (assignment : Assignment) (groups : List (List Scalar)) : Prop :=
  ∃ target, Verification.NativeRelationJson.decode json = .ok target ∧
    CircuitSatisfies hash target streams assignment groups

theorem decoded_constraints_sound (json : Lean.Json)
    (certificate : Verification.NativeRelationJson.decode json = .ok program)
    (ctx : EvalContext) (hash : Hash) (agreement : HashAgreement ctx hash)
    (input : Inputs) (assignment : Assignment) (groups : List (List Scalar))
    (sat : DecodedCircuitRelation json hash input.streams assignment groups) :
    claimEntry.circuit.run ctx (inputEnvironment input.source) =
      .ok [("nullifier", .native input.nullifier.val)] ∧
    program.returns assignment = [input.nullifier] ∧
    program.returns assignment = groups.getLastD [] := by
  obtain ⟨target, decoded, satisfaction⟩ := sat
  have targetEq := Except.ok.inj (decoded.symm.trans certificate)
  subst target
  exact native_constraints_sound ctx hash agreement input assignment groups satisfaction

theorem decoded_eligible_constraints_complete (json : Lean.Json)
    (certificate : Verification.NativeRelationJson.decode json = .ok program)
    (ctx : EvalContext) (hash : Hash) (agreement : HashAgreement ctx hash)
    (input : InputValues) (canonical : CanonicalInputs ctx input) (leaf node : Nat)
    (trace : HashTrace ctx input leaf node) :
    let nativeInputs := Inputs.ofSource ctx input canonical agreement.modulus
    ∃ assignment, DecodedCircuitRelation json hash nativeInputs.streams assignment
      [[nativeInputs.root], [nativeInputs.campaign], [nativeInputs.nullifier], [nativeInputs.nullifier]] := by
  obtain ⟨assignment, satisfaction⟩ := eligible_source_complete ctx hash agreement input canonical leaf node trace
  exact ⟨assignment, program, certificate, satisfaction.circuit⟩

theorem native_constraints_pruned_sound (ctx : EvalContext) (hash : Hash) (agreement : HashAgreement ctx hash)
    (input : Inputs) (assignment : Assignment) (groups : List (List Scalar))
    (sat : CircuitSatisfies hash program input.streams assignment groups) :
    (Passes.pruneCircuit claimEntry.circuit).run ctx (inputEnvironment input.source) =
      .ok [("nullifier", .native input.nullifier.val)] := by
  rw [Passes.pruneCircuit_run]
  exact (native_constraints_sound ctx hash agreement input assignment groups sat).1

theorem source_circuit_identity : claimEntry.circuit = claimRelation := by rfl

/-- Abstract-model nonvacuity only, not a native Poseidon qualification vector. -/
def zeroHash : Hash := fun _ => zero

theorem zero_hash_agreement : HashAgreement fixtureContext zeroHash := by
  constructor
  · rfl
  · intro domain left right
    rfl

theorem fixture_native_nonvacuity :
    let input := Inputs.ofSource fixtureContext fixtureValues fixture_canonical rfl
    ∃ assignment, CircuitSatisfies zeroHash program input.streams assignment
      [[input.root], [input.campaign], [input.nullifier], [input.nullifier]] := by
  obtain ⟨assignment, satisfaction⟩ := eligible_source_complete fixtureContext zeroHash zero_hash_agreement
    fixtureValues fixture_canonical 0 0 fixture_hash_trace
  exact ⟨assignment, satisfaction.circuit⟩

#print axioms decoded_constraints_sound
#print axioms decoded_eligible_constraints_complete
#print axioms native_constraints_pruned_sound
#print axioms fixture_native_nonvacuity
#print axioms native_constraints_sound
#print axioms native_satisfaction_sound
#print axioms native_satisfaction_pruned_sound
#print axioms source_acceptance_complete
#print axioms decoded_artifact_sound
#print axioms decoded_eligible_complete
#print axioms eligible_source_complete

end Noctium.PrivateClaimLowering
