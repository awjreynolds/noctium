import Noctium.Verification.GenericStateOps

namespace Noctium.Verification.GenericStateScalarPrefix
open Backend

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

/-- A plan accepted by `lower` comes from a successful detailed production
lowering, with its effect boundaries intact. -/
private theorem lower_boundary_result (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan)
    (accepted : Impact.lower state entry = .ok plan) :
    ∃ boundaries,
      Impact.lowerWithEffectBoundaries state entry = .ok (plan, boundaries) := by
  unfold Impact.lower at accepted
  cases detailed : Impact.lowerWithEffectBoundaries state entry with
  | error message =>
    simp only [detailed, Except.map] at accepted
    cases accepted
  | ok pair =>
    cases pair with
    | mk detailedPlan boundaries =>
      simp only [detailed, Except.map] at accepted
      cases accepted
      exact ⟨boundaries, rfl⟩

/-- The accepted public scalar prefix is the exact prefix admitted by the
production fallible input fold. A successful evaluation of the actual plan
also admits every operation in that plan. -/
theorem lower_scalar_operations_admitted
    (state : List StateDecl) (entry : Entrypoint) (plan : Impact.Plan)
    (ctx : EvalContext) (env : EvalEnv) (native : List NativeState.Op)
    (compatible : ∀ input ∈ entry.circuit.inputs,
      Impact.publicInputScalarCompatible input)
    (lowered : Impact.lower state entry = .ok plan)
    (evaluated : GenericStateOps.evalPlan ctx env plan = .ok native) :
    ∃ boundaries inputPlan,
      Impact.lowerWithEffectBoundaries state entry = .ok (plan, boundaries) ∧
      Impact.publicInputPlan entry.circuit.inputs {} = .ok inputPlan ∧
      Impact.appendEffectsGuardedWithBoundaries state entry.effects
        entry.effectGuards inputPlan = .ok (plan, boundaries) ∧
      inputPlan.operations =
        entry.circuit.inputs.flatMap Impact.publicInputScalarOperations ∧
      (∀ operation ∈ inputPlan.operations,
        GenericStateOps.ScalarOperation operation) ∧
      (∀ operation ∈ plan.operations,
        GenericStateOps.ScalarOperation operation) := by
  obtain ⟨boundaries, detailedAccepted⟩ :=
    lower_boundary_result state entry plan lowered
  obtain ⟨inputPlan, inputsAccepted, effectsAccepted⟩ :=
    Impact.lowerWithEffectBoundaries_inputPrefix state entry plan boundaries
      detailedAccepted
  have operationsExact := Impact.publicInputPlan_scalar_operations
    entry.circuit.inputs {} inputPlan inputsAccepted compatible
  have prefixSupported := GenericStateOps.publicInputPlan_scalar_supported
    entry.circuit.inputs {} inputPlan inputsAccepted compatible (by simp)
  have planSupported := GenericStateOps.evalPlan_supported ctx env plan native evaluated
  exact ⟨boundaries, inputPlan, detailedAccepted, inputsAccepted,
    effectsAccepted, operationsExact, prefixSupported, planSupported⟩

def publicInputScalarExpressions : Input → List (Expr .native)
  | .mk name .native .«public» _ => [(.ref name : Expr .native)]
  | .mk name .bool .«public» _ =>
    [(.cast .native (.ref name : Expr .bool) : Expr .native)]
  | .mk name (.uint maximum) .«public» _ =>
    [(.cast .native (.ref name : Expr (.uint maximum)) : Expr .native)]
  | _ => []

private def scalarPairOperations (expression : Expr .native) : List Impact.Op :=
  let value := Impact.Aligned.field expression
  [.push value, .popeq value]

private def nativeScalarPair (value : Nat) : List NativeState.Op :=
  let cell := NativeState.field (NativeRelation.scalar value)
  [.push cell false, .popeq cell]

private theorem publicInputScalarOperations_eq_expressions (inputs : List Input) :
    inputs.flatMap Impact.publicInputScalarOperations =
      (inputs.flatMap publicInputScalarExpressions).flatMap scalarPairOperations := by
  have one (input : Input) :
      Impact.publicInputScalarOperations input =
        (publicInputScalarExpressions input).flatMap scalarPairOperations := by
    cases input with
    | mk name ty visibility span =>
      cases visibility <;> cases ty <;>
        simp [Impact.publicInputScalarOperations, publicInputScalarExpressions,
          scalarPairOperations]
  induction inputs with
  | nil => rfl
  | cons input rest ih =>
    simp only [List.flatMap_cons]
    rw [one input, ih]
    simp only [List.flatMap_append]

private theorem scalarPair_eval (ctx : EvalContext) (env : EvalEnv)
    (expression : Expr .native) (operations : List NativeState.Op)
    (accepted : (scalarPairOperations expression).mapM
      (GenericStateOps.evalOp ctx env) = .ok operations) :
    ∃ value, expression.eval ctx env = .ok value ∧
      operations = nativeScalarPair value := by
  cases evaluated : expression.eval ctx env with
  | error message =>
    simp [scalarPairOperations, GenericStateOps.evalOp,
      GenericStateOps.evalAligned, evaluated, bind, Except.bind] at accepted
  | ok value =>
    refine ⟨value, rfl, ?_⟩
    simp [scalarPairOperations, GenericStateOps.evalOp,
      GenericStateOps.evalAligned,
      evaluated, bind, Except.bind] at accepted
    cases accepted
    rfl

private theorem scalarPairs_eval (ctx : EvalContext) (env : EvalEnv)
    (expressions : List (Expr .native)) (operations : List NativeState.Op)
    (accepted : (expressions.flatMap scalarPairOperations).mapM
      (GenericStateOps.evalOp ctx env) = .ok operations) :
    ∃ values,
      expressions.mapM (fun expression => expression.eval ctx env) = .ok values ∧
      operations = values.flatMap nativeScalarPair := by
  induction expressions generalizing operations with
  | nil =>
    simp at accepted
    cases accepted
    exact ⟨[], rfl, rfl⟩
  | cons expression rest ih =>
    simp only [List.flatMap_cons, List.mapM_append, bind_ok] at accepted
    rcases accepted with ⟨head, headAccepted, tail, tailAccepted, result⟩
    obtain ⟨value, valueAccepted, headShape⟩ :=
      scalarPair_eval ctx env expression head headAccepted
    obtain ⟨values, valuesAccepted, tailShape⟩ :=
      ih tail tailAccepted
    cases result
    refine ⟨value :: values, ?_, ?_⟩
    · simp [valueAccepted, valuesAccepted, List.mapM_cons,
        bind, Except.bind, pure, Except.pure]
    · rw [headShape, tailShape]
      simp [nativeScalarPair]

/-- Successful evaluation of the accepted scalar input prefix yields one
field-aligned push/equality pair per public Native, Bool, or UInt input, in
source order. The stored cells use the same native scalar conversion as the
production `Impact` expressions. -/
theorem publicInputPlan_scalar_eval_order
    (inputs : List Input) (plan : Impact.Plan)
    (ctx : EvalContext) (env : EvalEnv) (operations : List NativeState.Op)
    (compatible : ∀ input ∈ inputs, Impact.publicInputScalarCompatible input)
    (accepted : Impact.publicInputPlan inputs {} = .ok plan)
    (evaluated : GenericStateOps.evalPlan ctx env plan = .ok operations) :
    ∃ values,
      (inputs.flatMap publicInputScalarExpressions).mapM
        (fun expression => expression.eval ctx env) = .ok values ∧
      operations = values.flatMap nativeScalarPair := by
  have ordered := Impact.publicInputPlan_scalar_operations
    inputs {} plan accepted compatible
  have exactExpressions := publicInputScalarOperations_eq_expressions inputs
  unfold GenericStateOps.evalPlan at evaluated
  rw [ordered, exactExpressions] at evaluated
  exact scalarPairs_eval ctx env (inputs.flatMap publicInputScalarExpressions)
    operations evaluated

end Noctium.Verification.GenericStateScalarPrefix
