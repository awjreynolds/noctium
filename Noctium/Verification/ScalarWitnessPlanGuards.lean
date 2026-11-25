import Noctium.Verification.ScalarWitnessCircuitConstraints
import Noctium.Verification.ScalarExpressionLowering

namespace Noctium.Verification.ScalarWitnessConstruction

open Lean Backend NativeRelation NativeRelationJson ScalarNormalization ScalarLowering
open ScalarWitness ScalarInstructionEncoding ScalarAllocationOutputFrame
open ScalarExpressionLowering

private def planGuardBody (guard : Expr .bool) : StateM Zkir.LowerState Unit := do
  let text ← Zkir.lowerExpr guard
  Zkir.emit "assert" [("cond", toJson text)]

private theorem planGuardBody_frame (guard : Expr .bool)
    (admitted : ScalarExpression guard) :
    Zkir.PreservesOutputCapacityFrame (planGuardBody guard) := by
  unfold planGuardBody
  apply Zkir.bind_preservesOutputCapacityFrame _ _
    (lowerExpr_admitted_preservesOutputCapacityFrame guard admitted)
  intro text
  exact Zkir.emit_preservesOutputCapacityFrame "assert" [("cond", toJson text)]

private theorem lowerConstraints_cons (guard : Expr .bool)
    (guards : List (Expr .bool)) :
    Zkir.lowerConstraints (guard :: guards) =
      planGuardBody guard >>= fun _ => Zkir.lowerConstraints guards := by
  unfold Zkir.lowerConstraints
  rw [List.forIn_cons]
  simp only [planGuardBody, bind_assoc, pure_bind]

private theorem completes_plan_guard (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (normalAliases : Backend.Native.AliasEnvironment)
    (values : EvalEnv) (types : TypeEnv) (sourceAliases : AliasAgreement hash inputs normalAliases values)
    (lowerAliases : LowerAliasAgreement hash inputs witness normalAliases state.aliases values)
    (meaning : LowerStateMeaning hash witness state) (guard : Expr .bool)
    (admitted : ScalarExpression guard)
    (valid : guard.validate Capabilities.crypto types = .ok ())
    (success : guard.eval ctx values = .ok true)
    (budget : ((planGuardBody guard).run state).2.next ≤
      Native.maxInstructions * Native.maxVectorLength) :
    ∃ extension : PrefixExtension hash witness state
        ((planGuardBody guard).run state).2,
      LowerAliasAgreement hash inputs extension.witness normalAliases
        ((planGuardBody guard).run state |>.2).aliases values := by
  have guardFrame := Zkir.emit_preservesOutputCapacityFrame "assert"
    [("cond", toJson ((Zkir.lowerExpr guard).run state).1)]
    ((Zkir.lowerExpr guard).run state).2
  have expressionBudget : ((Zkir.lowerExpr guard).run state).2.next ≤
      Native.maxInstructions * Native.maxVectorLength :=
    Nat.le_trans guardFrame.next budget
  obtain ⟨result⟩ := lowerExpr_complete guard admitted ctx hash implementation inputs witness state
    normalAliases values types true valid success sourceAliases lowerAliases meaning expressionBudget
  have readOne : ∃ operand,
      decodeOperand (toJson result.text) = .ok operand ∧ operand.read result.finalWitness = one := by
    obtain ⟨operand, parsed, read⟩ := result.operandMeaning
    have valueMeaning : interpret hash inputs result.normalized.term = some one := by
      simpa [sourceScalar?, sourceNumber?, scalar_one] using result.represents.2.2
    exact ⟨operand, parsed, Option.some.inj (read.symm.trans valueMeaning)⟩
  have actualState : ((planGuardBody guard).run state).2 =
      ((Zkir.emit "assert" [("cond", toJson result.text)]).run result.finalState).2 := by
    change ((Zkir.emit "assert"
      [("cond", toJson ((Zkir.lowerExpr guard).run state).1)]).run
        ((Zkir.lowerExpr guard).run state).2).2 = _
    rw [result.run]
  have transportedLowerAliases : LowerAliasAgreement hash inputs result.finalWitness
      normalAliases result.finalState.aliases values := by
    rw [result.aliasesPreserved]
    exact LowerAliasAgreement.of_frame hash inputs witness result.finalWitness state.next
      normalAliases state.aliases values lowerAliases meaning.aliases result.frame
  refine ⟨{
    witness := result.finalWitness
    meaning := ?_
    aliases := ?_
    frame := result.frame
  }, ?_⟩
  · rw [actualState]
    exact emit_assert hash result.finalWitness result.finalState result.stateMeaning
      result.text result.textScope readOne
  · rw [actualState]
    exact result.aliasesPreserved
  · change LowerAliasAgreement hash inputs result.finalWitness normalAliases
      ((planGuardBody guard).run state).2.aliases values
    rw [actualState]
    change LowerAliasAgreement hash inputs result.finalWitness normalAliases
      ((Zkir.emit "assert" [("cond", toJson result.text)]).run result.finalState).2.aliases values
    change LowerAliasAgreement hash inputs result.finalWitness normalAliases
      result.finalState.aliases values
    exact transportedLowerAliases

private theorem lowerConstraints_nil (state : Zkir.LowerState) :
    (Zkir.lowerConstraints ([] : List (Expr .bool))).run state = ((), state) := by
  rfl

private theorem lowerConstraints_cons_state (guard : Expr .bool)
    (guards : List (Expr .bool)) (state : Zkir.LowerState) :
    (Zkir.lowerConstraints (guard :: guards)).run state =
      ((), ((Zkir.lowerConstraints guards).run ((planGuardBody guard).run state).2).2) := by
  rw [lowerConstraints_cons]
  rfl

private theorem completes_plan_guard_list (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : NativeRelation.Assignment)
    (normalAliases : Backend.Native.AliasEnvironment) (values : EvalEnv) (types : TypeEnv)
    (sourceAliases : AliasAgreement hash inputs normalAliases values)
    (guards : List (Expr .bool))
    (admitted : ∀ guard ∈ guards, ScalarExpression guard)
    (valid : ∀ guard ∈ guards, guard.validate Capabilities.crypto types = .ok ())
    (success : ∀ guard ∈ guards, guard.eval ctx values = .ok true) :
    ∀ (witness : NativeRelation.Assignment) (state : Zkir.LowerState),
      LowerStateMeaning hash witness state →
      LowerAliasAgreement hash inputs witness normalAliases state.aliases values →
      ((Zkir.lowerConstraints guards).run state).2.next ≤
        Native.maxInstructions * Native.maxVectorLength →
      ∃ extension : PrefixExtension hash witness state
          ((Zkir.lowerConstraints guards).run state).2,
        LowerAliasAgreement hash inputs extension.witness normalAliases
          ((Zkir.lowerConstraints guards).run state).2.aliases values := by
  induction guards with
  | nil =>
    intro witness state meaning lowerAliases budget
    refine ⟨{witness := witness, meaning := ?_, aliases := ?_, frame := ?_}, lowerAliases⟩
    · rw [lowerConstraints_nil]
      exact meaning
    · rw [lowerConstraints_nil]
    · intro name _
      rfl
  | cons guard guards ih =>
    intro witness state meaning lowerAliases budget
    let tailAdmitted : ∀ condition ∈ guards, ScalarExpression condition := by
      intro condition member
      exact admitted condition (List.mem_cons_of_mem guard member)
    let tailValid : ∀ condition ∈ guards,
        condition.validate Capabilities.crypto types = .ok () := by
      intro condition member
      exact valid condition (List.mem_cons_of_mem guard member)
    let tailSuccess : ∀ condition ∈ guards, condition.eval ctx values = .ok true := by
      intro condition member
      exact success condition (List.mem_cons_of_mem guard member)
    have guardAdmitted : ScalarExpression guard := admitted guard (by simp)
    have tailFrame : Zkir.PreservesOutputCapacityFrame (Zkir.lowerConstraints guards) :=
      Zkir.lowerConstraints_preservesOutputCapacityFrame guards (by
        intro condition member
        exact lowerExpr_admitted_preservesOutputCapacityFrame condition
          (tailAdmitted condition member))
    have tailBudget : ((Zkir.lowerConstraints guards).run
        ((planGuardBody guard).run state).2).2.next ≤
          Native.maxInstructions * Native.maxVectorLength := by
      simpa only [lowerConstraints_cons_state] using budget
    have guardBudget : ((planGuardBody guard).run state).2.next ≤
        Native.maxInstructions * Native.maxVectorLength := by
      exact Nat.le_trans (tailFrame ((planGuardBody guard).run state).2).next tailBudget
    have guardComplete := completes_plan_guard ctx hash implementation inputs witness state
      normalAliases values types sourceAliases lowerAliases meaning guard guardAdmitted
      (valid guard (by simp)) (success guard (by simp)) guardBudget
    obtain ⟨first, firstLowerAliases⟩ := guardComplete
    obtain ⟨rest, restLowerAliases⟩ := ih tailAdmitted tailValid tailSuccess first.witness
      ((planGuardBody guard).run state).2 first.meaning firstLowerAliases tailBudget
    refine ⟨{
        witness := rest.witness
        meaning := ?_
        aliases := ?_
        frame := ?_
      }, ?_⟩
    · rw [lowerConstraints_cons_state]
      exact rest.meaning
    · rw [lowerConstraints_cons_state]
      exact rest.aliases.trans first.aliases
    · intro name scope
      exact (rest.frame name (InScope.mono (planGuardBody_frame guard guardAdmitted state).next scope)).trans
        (first.frame name scope)
    · change LowerAliasAgreement hash inputs rest.witness normalAliases
        ((Zkir.lowerConstraints (guard :: guards)).run state).2.aliases values
      rw [lowerConstraints_cons_state]
      exact restLowerAliases

/-- The actual guard loop extends a valid witness through every true typed
plan guard. It preserves installed aliases and returns agreement for the
final witness, so later ledger stages can reuse it. -/
theorem completes_plan_guards (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (normalAliases : Backend.Native.AliasEnvironment)
    (values : EvalEnv) (types : TypeEnv) (plan : Impact.Plan)
    (sourceAliases : AliasAgreement hash inputs normalAliases values)
    (lowerAliases : LowerAliasAgreement hash inputs witness normalAliases state.aliases values)
    (meaning : LowerStateMeaning hash witness state)
    (admitted : ∀ guard ∈ plan.guards, ScalarExpression guard)
    (valid : ∀ guard ∈ plan.guards, guard.validate Capabilities.crypto types = .ok ())
    (success : ∀ guard ∈ plan.guards, guard.eval ctx values = .ok true)
    (budget : ((Zkir.lowerConstraints plan.guards).run state).2.next ≤
      Native.maxInstructions * Native.maxVectorLength) :
    ∃ extension : PrefixExtension hash witness state
        ((Zkir.lowerConstraints plan.guards).run state).2,
      LowerAliasAgreement hash inputs extension.witness normalAliases
        ((Zkir.lowerConstraints plan.guards).run state).2.aliases values := by
  exact completes_plan_guard_list ctx hash implementation inputs normalAliases values types
    sourceAliases plan.guards admitted valid success witness state meaning lowerAliases budget

end Noctium.Verification.ScalarWitnessConstruction
