import Noctium.Verification.ImpactPlanStatementAgreement
import Noctium.Verification.ScalarCellPlanScope

namespace Noctium.Verification.ScalarCellImpactByteEvaluation

open Backend ImpactReferenceEvaluation ScalarNormalization

private theorem all_none_eq_replicate {guards : List (Option (Expr .bool))}
    (allNone : guards.all Option.isNone = Bool.true) :
    guards = List.replicate guards.length none := by
  induction guards with
  | nil => rfl
  | cons guard rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at allNone
    have guardNone : guard = none := by
      cases guard with
      | none => rfl
      | some value =>
        have impossible : Option.isNone (some value) = Bool.true := allNone.1
        simp [Option.isNone] at impossible
    change guard :: rest = none :: List.replicate rest.length none
    rw [guardNone]
    congr 1
    exact ih allNone.2

/-- Accepted unguarded scalar-cell lowering gives the guard-aware evaluator
the same exact operation result as the generic scalar interpreter. -/
theorem guarded_evalPlan_eq_scalarCell
    (state : List StateDecl) (ep : Entrypoint) (plan : Impact.Plan)
    (ctx : EvalContext) (env : EvalEnv)
    (lowered : Impact.lower state ep = .ok plan)
    (unguarded : ep.effectGuards = [])
    (cellEffects : ScalarCellSourceReads.ScalarCellEffects state ep.effects) :
    GuardedPlanExecution.evalPlan ctx env plan = GenericStateOps.evalPlan ctx env plan := by
  have noGuardExpressions :=
    ScalarCellPlanScope.lower_scope state ep plan lowered unguarded cellEffects
  have valid := Impact.lower_validated state ep plan lowered
  obtain ⟨guardSchedule, _⟩ := plan.validate_activity_success ep valid
  have inactive : GuardedPlanActivity.operationGuards plan =
      List.replicate plan.operations.length none := by
    unfold GuardedPlanActivity.operationGuards
    split
    · simp
    · rename_i nonempty
      have exactSchedule : plan.activityGuards.length = plan.operations.length :=
        guardSchedule.resolve_left (by simpa using nonempty)
      rw [all_none_eq_replicate noGuardExpressions.1, exactSchedule]
  exact GuardedPlanExecution.evalPlan_eq_scalar_of_unguarded ctx env plan inactive

/-- Matching production bytes evaluate to the native operation list accepted
by the generic scalar interpreter for an unguarded scalar-cell plan. -/
theorem evaluations_fromBytes_agree
    (profile : TargetProfile) (contractName : Lean.Name) (state : List StateDecl)
    (ctor : Option Constructor) (ep : Entrypoint) (plan : Impact.Plan)
    (standaloneFile : _root_.Bool)
    (ctx : EvalContext) (modulus : ctx.modulus = Field.modulus)
    {env : EvalEnv} (typed : TypedScalarEnv (plan.typeEnvironment ep) env)
    (keyWidth : Nat → Option Nat)
    (admitted : ImpactPlanStatementAgreement.admitsScalarPlan keyWidth plan = Bool.true)
    (budget : Nat) (bytes : ArtifactBytes.Bytes)
    (lowered : Impact.lower state ep = .ok plan)
    (unguarded : ep.effectGuards = [])
    (cellEffects : ScalarCellSourceReads.ScalarCellEffects state ep.effects)
    (matched : ImpactPlanStatementAgreement.matchesBytes budget bytes
      (Compiler.nativePlanJson profile contractName state ctor ep plan standaloneFile) = Bool.true)
    {native : List NativeState.Op}
    (evaluated : GenericStateOps.evalPlan ctx env plan = .ok native) :
    ∃ minimum, ∀ fuel, minimum ≤ fuel → ∃ raw,
      ArtifactBytes.parse bytes = .ok raw ∧
      ImpactPlanAgreement.evaluatePlan fuel ctx env raw = some native := by
  obtain ⟨minimum, agrees⟩ :=
    ImpactPlanStatementAgreement.evaluations_fromBytes_agree
      profile contractName state ctor ep plan standaloneFile ctx modulus typed
      keyWidth admitted budget bytes lowered matched
  have sourceExact := guarded_evalPlan_eq_scalarCell
    state ep plan ctx env lowered unguarded cellEffects
  refine ⟨minimum, ?_⟩
  intro fuel enough
  obtain ⟨raw, parsed, operationsAgree, _activityAgree⟩ := agrees fuel enough
  have planAccepted : (GuardedPlanExecution.evalPlan ctx env plan).toOption = some native := by
    rw [sourceExact, evaluated]
    rfl
  exact ⟨raw, parsed, operationsAgree.trans planAccepted⟩

end Noctium.Verification.ScalarCellImpactByteEvaluation
