import Noctium.Verification.GenericStateOps
import Noctium.Verification.GenericStateVM

namespace Noctium.Verification.GenericStateAdmissionPrefix
open Backend

private theorem bind_ok {α β : Type} {first : Except ε α} {next : α → Except ε β}
    {result : β} : (first >>= next) = .ok result ↔
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private def publicInputScalarValues (inputs : List Input) : List Impact.Aligned :=
  inputs.flatMap fun input =>
    match input.visibility, input.ty with
    | .public, .native =>
      [.field (.ref input.name : Expr .native)]
    | .public, .bool =>
      [.field (.cast .native (.ref input.name : Expr .bool))]
    | .public, .uint maximum =>
      [.field (.cast .native (.ref input.name : Expr (.uint maximum)))]
    | _, _ => []

private theorem publicInputScalarOperations_pairs (inputs : List Input) :
    inputs.flatMap Impact.publicInputScalarOperations =
      (publicInputScalarValues inputs).flatMap (fun value =>
        [Impact.Op.push value, .popeq value]) := by
  induction inputs with
  | nil => rfl
  | cons input rest ih =>
    cases input with
    | mk name ty visibility span =>
      cases visibility <;> cases ty <;>
        simp [publicInputScalarValues, Impact.publicInputScalarOperations,
          List.flatMap_cons, ih]

/-- A successful, scalar-compatible public-input fold emits ordered
push/popeq pairs, with the exact accepted plan as its source. -/
theorem publicInputPlan_pairs (inputs : List Input) (plan : Impact.Plan)
    (accepted : Impact.publicInputPlan inputs {} = .ok plan)
    (compatible : ∀ input ∈ inputs, Impact.publicInputScalarCompatible input) :
    ∃ values : List Impact.Aligned,
      plan.operations = values.flatMap (fun value =>
        [Impact.Op.push value, .popeq value]) := by
  have scalarShape := Impact.publicInputPlan_scalar_operations inputs {} plan
    accepted compatible
  rw [publicInputScalarOperations_pairs] at scalarShape
  exact ⟨publicInputScalarValues inputs, by simpa using scalarShape⟩

/-- Successful production lowering retains the exact public-input fold as
the plan prefix before guarded source effects are appended. -/
theorem lower_input_prefix (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan) (lowered : Impact.lower state entry = .ok plan) :
    ∃ boundaries inputPlan,
      Impact.lowerWithEffectBoundaries state entry = .ok (plan, boundaries) ∧
      Impact.publicInputPlan entry.circuit.inputs {} = .ok inputPlan ∧
      Impact.appendEffectsGuardedWithBoundaries state entry.effects
        entry.effectGuards inputPlan = .ok (plan, boundaries) := by
  unfold Impact.lower at lowered
  cases result : Impact.lowerWithEffectBoundaries state entry with
  | error message =>
    rw [result] at lowered
    cases lowered
  | ok output =>
    cases output with
    | mk candidate boundaries =>
      rw [result] at lowered
      simp only [Functor.map, Except.map] at lowered
      have candidateEq : candidate = plan := Except.ok.inj lowered
      subst plan
      have prefixResult := Impact.lowerWithEffectBoundaries_inputPrefix state entry
        candidate boundaries result
      obtain ⟨inputPlan, inputAccepted, effectsAccepted⟩ := prefixResult
      exact ⟨boundaries, inputPlan, rfl, inputAccepted, effectsAccepted⟩

/-- The checked ledger lowerer yields the actual guarded effect trace after
the accepted public-input prefix. Intermediate plans reflect the source guard. -/
theorem lower_guarded_effect_trace (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan) (lowered : Impact.lower state entry = .ok plan) :
    ∃ boundaries inputPlan,
      Impact.lowerWithEffectBoundaries state entry = .ok (plan, boundaries) ∧
      Impact.publicInputPlan entry.circuit.inputs {} = .ok inputPlan ∧
      Impact.GuardedEffectTrace state entry.effectGuards entry.effects.zipIdx
        inputPlan plan boundaries := by
  obtain ⟨boundaries, inputPlan, accepted, inputAccepted, effects⟩ :=
    lower_input_prefix state entry plan lowered
  exact ⟨boundaries, inputPlan, accepted, inputAccepted,
    Impact.appendEffectsGuardedWithBoundaries_trace state entry.effects
      entry.effectGuards inputPlan plan boundaries effects⟩

private theorem eval_public_pair (ctx : EvalContext) (env : EvalEnv)
    (value : Impact.Aligned) (ops : List NativeState.Op)
    (accepted : [Impact.Op.push value, .popeq value].mapM
      (GenericStateOps.evalOp ctx env) = .ok ops) :
    ∃ cell, ops = [.push cell false, .popeq cell] := by
  cases evaluated : GenericStateOps.evalAligned ctx env value with
  | error message =>
    simp [List.mapM_cons, GenericStateOps.evalOp, evaluated,
      Except.bind, Except.map, Functor.map] at accepted
    change (Except.error message : Except String (List NativeState.Op)) =
      .ok ops at accepted
    cases accepted
  | ok cell =>
    simp [List.mapM_cons, GenericStateOps.evalOp, evaluated,
      Except.bind, Except.map, Functor.map] at accepted
    change (Except.ok [.push cell false, .popeq cell] :
      Except String (List NativeState.Op)) = .ok ops at accepted
    exact ⟨cell, (Except.ok.inj accepted).symm⟩

private theorem eval_public_pairs (ctx : EvalContext) (env : EvalEnv)
    (values : List Impact.Aligned) (ops : List NativeState.Op)
    (evaluated : (values.flatMap (fun value =>
      [Impact.Op.push value, .popeq value])).mapM
      (GenericStateOps.evalOp ctx env) = .ok ops) :
    ∃ cells : List NativeState.Cell,
      ops = cells.flatMap (fun cell =>
        [NativeState.Op.push cell false, .popeq cell]) := by
  induction values generalizing ops with
  | nil =>
    simp at evaluated
    cases evaluated
    exact ⟨[], rfl⟩
  | cons value rest ih =>
    simp only [List.flatMap_cons, List.mapM_append, bind_ok] at evaluated
    rcases evaluated with ⟨first, pairAccepted, remaining, restAccepted, result⟩
    obtain ⟨cell, pairShape⟩ := eval_public_pair ctx env value first pairAccepted
    obtain ⟨cells, restShape⟩ := ih remaining restAccepted
    cases result
    exact ⟨cell :: cells, by simp [pairShape, restShape]⟩

/-- The accepted production public-input prefix records each consumed public
value in the read tape and leaves the native root and stack intact. -/
theorem public_prefix_run (inputs : List Input) (plan : Impact.Plan)
    (ctx : EvalContext) (env : EvalEnv) (ops : List NativeState.Op)
    (stack : List NativeState.Node) (reads : List NativeState.Cell)
    (accepted : Impact.publicInputPlan inputs {} = .ok plan)
    (compatible : ∀ input ∈ inputs, Impact.publicInputScalarCompatible input)
    (evaluated : plan.operations.mapM
      (GenericStateOps.evalOp ctx env) = .ok ops) :
    ∃ cells : List NativeState.Cell,
      ops = cells.flatMap (fun cell =>
        [NativeState.Op.push cell false, .popeq cell]) ∧
      NativeState.run ops ⟨stack, reads⟩ =
        some ⟨stack, reads ++ cells⟩ := by
  obtain ⟨aligned, shape⟩ := publicInputPlan_pairs inputs plan accepted compatible
  rw [shape] at evaluated
  obtain ⟨cells, nativeShape⟩ := eval_public_pairs ctx env aligned ops evaluated
  refine ⟨cells, nativeShape, ?_⟩
  rw [nativeShape]
  exact GenericStateVM.run_input_pairs cells stack reads

/-- The public prefix selected by production lowering is the accepted prefix
plan consumed by the VM. -/
theorem lower_prefix_run (state : List StateDecl) (entry : Entrypoint)
    (plan prefixPlan : Impact.Plan) (ctx : EvalContext) (env : EvalEnv)
    (ops : List NativeState.Op) (stack : List NativeState.Node)
    (reads : List NativeState.Cell)
    (lowered : Impact.lower state entry = .ok plan)
    (prefixAccepted : Impact.publicInputPlan entry.circuit.inputs {} =
      .ok prefixPlan)
    (compatible : ∀ input ∈ entry.circuit.inputs,
      Impact.publicInputScalarCompatible input)
    (evaluated : prefixPlan.operations.mapM
      (GenericStateOps.evalOp ctx env) = .ok ops) :
    ∃ cells : List NativeState.Cell,
      ops = cells.flatMap (fun cell =>
        [NativeState.Op.push cell false, .popeq cell]) ∧
      NativeState.run ops ⟨stack, reads⟩ =
        some ⟨stack, reads ++ cells⟩ := by
  obtain ⟨_, sourcePrefix, _, sourceAccepted, _⟩ :=
    lower_input_prefix state entry plan lowered
  have samePrefix : sourcePrefix = prefixPlan :=
    Except.ok.inj (sourceAccepted.symm.trans prefixAccepted)
  subst prefixPlan
  exact public_prefix_run entry.circuit.inputs sourcePrefix ctx env ops stack reads
    sourceAccepted compatible evaluated

end Noctium.Verification.GenericStateAdmissionPrefix
