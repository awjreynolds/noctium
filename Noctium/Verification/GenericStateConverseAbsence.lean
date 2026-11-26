import Noctium.Verification.GenericStateSourceTrace
import Noctium.Verification.GenericStateAbsenceAuthentication
import Noctium.Verification.GuardedPlanExecution
import Noctium.Verification.GuardedSourceEffects

namespace Noctium.Verification.GenericStateConverseAbsence
open Backend NativeRelation ScalarNormalization NativeState GenericStateEncoding

/-- Original source absence drives the exact compiled segment and a successful
native missing-key check, with arbitrary source declaration spans. -/
theorem source_requireAbsent_native (ctx : EvalContext)
    (sourceEnv candidateEnv : EvalEnv) (state : List StateDecl)
    (current : LedgerState) (slots : List Slot)
    (name : String) (keyTy valueTy : Ty) (keyExpr : Expr keyTy)
    (admission : ScalarExpression keyExpr)
    (sourceAfter : SourceEffects.Frame) (base : Impact.Plan) (reads : List Cell)
    (sourceStep : SourceEffects.step ctx (.requireAbsent name keyTy keyExpr)
      (sourceEnv, current) = .ok sourceAfter)
    (candidateAgreement : keyExpr.eval ctx candidateEnv = keyExpr.eval ctx sourceEnv)
    (declaration : StateDecl)
    (declared : state.find? (·.name == name) = some declaration)
    (named : declaration.name = name) (kind : declaration.kind = .map keyTy valueTy)
    (compiled : Impact.appendEffect state (.requireAbsent name keyTy keyExpr) {} = .ok base)
    (encoded : encodeState state current = some slots)
    (modulus : ctx.modulus = Field.modulus) :
    ∃ slot key, state.findIdx? (·.name == name) = some slot ∧
      base.operations.mapM (GenericStateOps.evalOp ctx candidateEnv) =
        .ok (GenericStateVM.requireAbsentOps slot (scalar (number keyTy key))) ∧
      run (GenericStateVM.requireAbsentOps slot (scalar (number keyTy key)))
        ⟨[.vector slots], reads⟩ = some ⟨[.vector slots], reads ++ [boolean false]⟩ ∧
      sourceAfter = (sourceEnv, current) := by
  obtain ⟨key, entries, keyEval, canonical, lookup, missing, sourceShape⟩ :=
    GenericStateSourceTrace.requireAbsent_step_key ctx sourceEnv current name keyTy keyExpr
      admission sourceAfter modulus sourceStep
  have candidateEval : keyExpr.eval ctx candidateEnv = .ok key := by
    rw [candidateAgreement]
    exact keyEval
  obtain ⟨slot, located, segmentEval⟩ :=
    GenericStateAbsenceAuthentication.requireAbsent_candidate_eval state name keyTy keyExpr
      base ctx candidateEnv key compiled modulus candidateEval canonical
  have declarationAt : state[slot]? = some declaration := by
    rw [List.find?_eq_bind_findIdx?_getElem?, located] at declared
    exact declared
  obtain ⟨nativeEntries, mapped, slotFound⟩ := encoded_map_slot state current slots slot
    declaration name keyTy valueTy entries declarationAt named kind encoded lookup
  have absent := sourceMap_absent keyTy valueTy entries nativeEntries key canonical mapped missing
  exact ⟨slot, key, located, segmentEval,
    GenericStateVM.requireAbsent_exact slots slot nativeEntries (scalar (number keyTy key))
      reads slotFound absent, sourceShape⟩

private theorem bind_ok {α β : Type} {first : Except ε α} {next : α → Except ε β}
    {result : β} : (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem absence_chunk (state : List StateDecl) (name : String) (keyTy : Ty)
    (key : Expr keyTy) (before after : Impact.Plan)
    (compiled : Impact.appendEffectWithActivity state (.requireAbsent name keyTy key) none
      before = .ok after) :
    ∃ base, Impact.appendEffect state (.requireAbsent name keyTy key) {} = .ok base ∧
      after.operations = before.operations ++ base.operations := by
  obtain ⟨raw, appended, operations, _⟩ := GuardedEffectPrefix.appendEffectWithActivity_none_result
    state (.requireAbsent name keyTy key) before after compiled
  simp only [Impact.appendEffect, bind_ok] at appended
  obtain ⟨slot, slotAccepted, aligned, keyAccepted, result⟩ := appended
  cases result
  let base : Impact.Plan := {
    operations := after.operations.drop before.operations.length
    reads := [{name := "_noctium_absence_0", ty := .bool}]
    guards := [.eq (.ref "_noctium_absence_0" : Expr .bool) (.bool false)] }
  refine ⟨base, ?_, ?_⟩
  · simp only [Impact.appendEffect, bind_ok]
    exact ⟨slot, slotAccepted, aligned, keyAccepted,
      by simp [base, operations, Pure.pure, Except.pure] <;> decide⟩
  · simp [base, operations]

/-- Source absence evaluates the actual unguarded operation suffix and
records the native false read at the current transcript position. -/
theorem source_requireAbsent_chunk (ctx : EvalContext)
    (sourceEnv candidateEnv : EvalEnv) (state : List StateDecl)
    (current : LedgerState) (slots : List Slot)
    (name : String) (keyTy valueTy : Ty) (keyExpr : Expr keyTy)
    (admission : ScalarExpression keyExpr)
    (sourceAfter : SourceEffects.Frame) (before after : Impact.Plan) (reads : List Cell)
    (sourceStep : GuardedSourceEffects.step ctx none (.requireAbsent name keyTy keyExpr)
      (sourceEnv, current) = .ok sourceAfter)
    (candidateAgreement : keyExpr.eval ctx candidateEnv = keyExpr.eval ctx sourceEnv)
    (declaration : StateDecl)
    (declared : state.find? (·.name == name) = some declaration)
    (named : declaration.name = name) (kind : declaration.kind = .map keyTy valueTy)
    (compiled : Impact.appendEffectWithActivity state (.requireAbsent name keyTy keyExpr) none
      before = .ok after)
    (encoded : encodeState state current = some slots)
    (modulus : ctx.modulus = Field.modulus) :
    ∃ segment,
      GuardedPlanExecution.evalChunk ctx candidateEnv none (after.operations.drop before.operations.length) =
        .ok (none, segment) ∧
      run segment ⟨[.vector slots], reads⟩ = some ⟨[.vector slots], reads ++ [boolean false]⟩ ∧
      sourceAfter = (sourceEnv, current) := by
  obtain ⟨base, emptyCompiled, operations⟩ := absence_chunk state name keyTy keyExpr before after compiled
  rw [GuardedSourceEffects.step_unguarded] at sourceStep
  obtain ⟨slot, key, _, evaluated, nativeRun, shape⟩ :=
    source_requireAbsent_native ctx sourceEnv candidateEnv state current slots name keyTy valueTy
      keyExpr admission sourceAfter base reads sourceStep candidateAgreement declaration declared
      named kind emptyCompiled encoded modulus
  refine ⟨GenericStateVM.requireAbsentOps slot (scalar (number keyTy key)), ?_, nativeRun, shape⟩
  rw [operations, List.drop_left]
  change (base.operations.mapM (GenericStateOps.evalOp ctx candidateEnv)).map (fun result => (none, result)) = _
  rw [evaluated]
  rfl

end Noctium.Verification.GenericStateConverseAbsence
