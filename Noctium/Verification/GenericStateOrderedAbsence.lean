import Noctium.Verification.GenericStateAbsenceAuthentication
import Noctium.Verification.GenericStateAbsenceInversion
import Noctium.Verification.GuardedEffectPrefix

namespace Noctium.Verification.GenericStateOrderedAbsence
open Backend ScalarNormalization NativeState NativeRelation

private def absenceReadName (ordinal : Nat) : String :=
  s!"_noctium_absence_{ordinal}"

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem appendEffectWithActivity_none_result_full
    (state : List StateDecl) (effect : Effect) (before after : Impact.Plan)
    (accepted : Impact.appendEffectWithActivity state effect none before = .ok after) :
    ∃ result, Impact.appendEffect state effect before = .ok result ∧
      after.operations = result.operations ∧ after.reads = result.reads ∧
      after.guards = result.guards := by
  have shape : Impact.appendEffectWithActivity state effect none before = (do
      let result ← Impact.appendEffect state effect before
      if before.activityGuards.isEmpty then
        pure result
      else
        let guards := before.activityGuards ++
          List.replicate (result.operations.length - before.operations.length) none
        pure ({result with activityGuards := guards} : Impact.Plan)) := by
    cases effect <;> rfl
  rw [shape, bind_ok] at accepted
  obtain ⟨result, appended, finished⟩ := accepted
  refine ⟨result, appended, ?_, ?_, ?_⟩
  · split at finished <;> cases finished <;> rfl
  · split at finished <;> cases finished <;> rfl
  · split at finished <;> cases finished <;> rfl

private theorem appendEffect_requireAbsent_prefix (state : List StateDecl)
    (name : String) (keyTy : Ty) (keyExpr : Expr keyTy)
    (before result : Impact.Plan)
    (accepted : Impact.appendEffect state (.requireAbsent name keyTy keyExpr)
      before = .ok result) :
    ∃ base, Impact.appendEffect state (.requireAbsent name keyTy keyExpr) {} = .ok base ∧
      result.operations = before.operations ++ base.operations ∧
      result.reads = before.reads ++
        [{name := (absenceReadName before.reads.length), ty := .bool}] ∧
      result.guards = before.guards ++ [.eq
        (.ref (absenceReadName before.reads.length) : Expr .bool)
        (.bool false)] := by
  simp only [Impact.appendEffect, bind_ok] at accepted
  rcases accepted with ⟨slot, slotAccepted, aligned, alignedAccepted, resultAccepted⟩
  simp only [Pure.pure, Except.pure] at resultAccepted
  have resultShape := Except.ok.inj resultAccepted
  cases emptyResult : Impact.appendEffect state
      (.requireAbsent name keyTy keyExpr) {} with
  | error message =>
    simp only [Impact.appendEffect, slotAccepted, alignedAccepted,
      Bind.bind, Except.bind, Pure.pure, Except.pure] at emptyResult
    cases emptyResult
  | ok base =>
    have baseAccepted : Impact.appendEffect state
        (.requireAbsent name keyTy keyExpr) {} = .ok base := emptyResult
    have baseAcceptedParts := baseAccepted
    simp only [Impact.appendEffect, bind_ok] at baseAcceptedParts
    rcases baseAcceptedParts with
      ⟨emptySlot, emptySlotAccepted, emptyAligned, emptyAlignedAccepted, emptyResultAccepted⟩
    have slotEq : emptySlot = slot :=
      Except.ok.inj (emptySlotAccepted.symm.trans slotAccepted)
    have alignedEq : emptyAligned = aligned :=
      Except.ok.inj (emptyAlignedAccepted.symm.trans alignedAccepted)
    simp only [Pure.pure, Except.pure] at emptyResultAccepted
    have baseShape := Except.ok.inj emptyResultAccepted
    let chunk := result.operations.drop before.operations.length
    have resultOperationsProjection := congrArg Impact.Plan.operations resultShape
    have resultOperations : result.operations = before.operations ++ chunk := by
      change result.operations = before.operations ++
        result.operations.drop before.operations.length
      rw [← resultOperationsProjection]
      simp
    have baseOperationsProjection := congrArg Impact.Plan.operations baseShape
    have resultDropProjection := congrArg (fun plan : Impact.Plan =>
      plan.operations.drop before.operations.length) resultShape
    have baseOperations : base.operations = chunk := by
      change base.operations = result.operations.drop before.operations.length
      calc
        base.operations = _ := baseOperationsProjection.symm
        _ = _ := by simp [slotEq, alignedEq]
        _ = result.operations.drop before.operations.length := resultDropProjection
    have operations : result.operations = before.operations ++ base.operations := by
      rw [resultOperations, ← baseOperations]
    have reads : result.reads = before.reads ++
        [{name := (absenceReadName before.reads.length), ty := .bool}] := by
      have projected := congrArg (fun plan : Impact.Plan => plan.reads) resultShape
      simpa [absenceReadName] using projected.symm
    have guards : result.guards = before.guards ++ [.eq
        (.ref (absenceReadName before.reads.length) : Expr .bool)
        (.bool false)] := by
      have projected := congrArg (fun plan : Impact.Plan => plan.guards) resultShape
      simpa [absenceReadName] using projected.symm
    exact ⟨base, rfl, operations, reads, guards⟩

/-- A checked production absence suffix, at any accepted prefix, proves the
source absence transition. The generated descriptor uses the live read
ordinal, and the checked key comes from the evaluated suffix itself. -/
theorem requireAbsent_checked_suffix (ctx : EvalContext)
    (sourceEnv candidateEnv : EvalEnv) (state : List StateDecl)
    (current : LedgerState) (slots : List NativeState.Slot)
    (name : String) (keyTy valueTy : Ty) (keyExpr : Expr keyTy)
    (admission : ScalarExpression keyExpr)
    (keyAgreement : keyExpr.eval ctx sourceEnv = keyExpr.eval ctx candidateEnv)
    (before plan : Impact.Plan) (segment : List NativeState.Op)
    (reads : List NativeState.Cell) (after : NativeState.Machine)
    (compiled : Impact.appendEffectWithActivity state
      (.requireAbsent name keyTy keyExpr) none before = .ok plan)
    (declaration : StateDecl)
    (declared : state.find? (·.name == name) = some declaration)
    (named : declaration.name = name)
    (kind : declaration.kind = .map keyTy valueTy)
    (encoded : GenericStateEncoding.encodeState state current = some slots)
    (modulus : ctx.modulus = Field.modulus)
    (evaluated : (plan.operations.drop before.operations.length).mapM
      (GenericStateOps.evalOp ctx candidateEnv) = .ok segment)
    (checked : NativeState.run segment ⟨[.vector slots], reads⟩ = some after) :
    SourceEffects.step ctx (.requireAbsent name keyTy keyExpr) (sourceEnv, current) =
      .ok (sourceEnv, current) ∧
    after = ⟨[.vector slots], reads ++ [NativeState.boolean false]⟩ ∧
    plan.reads = before.reads ++
      [{name := absenceReadName before.reads.length, ty := .bool}] ∧
    plan.guards = before.guards ++ [.eq
      (.ref (absenceReadName before.reads.length) : Expr .bool)
      (.bool false)] := by
  obtain ⟨raw, appended, operations, readsShape, guardsShape⟩ :=
    appendEffectWithActivity_none_result_full state
      (.requireAbsent name keyTy keyExpr) before plan compiled
  obtain ⟨support⟩ := GenericStateEvaluationCanonical.scalarExpression_type admission
  obtain ⟨base, baseAccepted, baseOperations, baseReads, baseGuards⟩ :=
    appendEffect_requireAbsent_prefix state name keyTy keyExpr before raw appended
  have planOperations : plan.operations = before.operations ++ base.operations := by
    calc
      plan.operations = raw.operations := operations
      _ = before.operations ++ base.operations := baseOperations
  have evaluatedBase : base.operations.mapM
      (GenericStateOps.evalOp ctx candidateEnv) = .ok segment := by
    rw [planOperations] at evaluated
    simpa using evaluated
  obtain ⟨key, candidateEval⟩ :=
    GenericStateAbsenceInversion.requireAbsent_source_evaluates state name keyTy
      keyExpr base support ctx candidateEnv segment baseAccepted modulus evaluatedBase
  have sourceEval : keyExpr.eval ctx sourceEnv = .ok key :=
    keyAgreement.trans candidateEval
  have canonical := GenericStateEvaluationCanonical.expression_eval_canonical
    ctx candidateEnv keyExpr admission key modulus candidateEval
  obtain ⟨sourceStep, nativeResult⟩ :=
    GenericStateAbsenceAuthentication.requireAbsent_candidate_source_step ctx
      sourceEnv candidateEnv state current slots name keyTy valueTy keyExpr key base
      segment reads after baseAccepted declaration declared named kind encoded modulus
      candidateEval sourceEval canonical evaluatedBase checked
  exact ⟨sourceStep, nativeResult, readsShape.trans baseReads,
    guardsShape.trans baseGuards⟩

end Noctium.Verification.GenericStateOrderedAbsence
