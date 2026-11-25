import Noctium.Verification.ScalarExpressionNativeArithmetic
import Noctium.Verification.ScalarAllocationOutputFrame

namespace Noctium.Verification.ScalarWitnessConstruction

open Lean Backend NativeRelation NativeRelationJson ScalarNormalization ScalarLowering
open ScalarInstructionEncoding ScalarWitness ScalarAllocationOutputFrame

private def boolCastTail (text : String) : StateM Zkir.LowerState String := do
  let compared ← Zkir.binary "test_eq" text "0x00"
  Zkir.unary "not" compared

private theorem boolCastTail_preservesOutputCapacityFrame (text : String) :
    Zkir.PreservesOutputCapacityFrame (boolCastTail text) := by
  unfold boolCastTail
  apply Zkir.bind_preservesOutputCapacityFrame _ _
    (Zkir.ordinaryBinary_preservesOutputCapacityFrame "test_eq" text "0x00"
      ⟨by decide, by decide, by decide⟩)
  intro compared
  exact Zkir.ordinaryUnary_preservesOutputCapacityFrame "not" compared
    ⟨by decide, by decide, by decide⟩

private theorem lowerExpr_boolCast (value : Expr sourceTy) :
    Zkir.lowerExpr (.cast .bool value) =
      (do
        let text ← Zkir.lowerExpr value
        boolCastTail text) := by
  simp only [Zkir.lowerExpr, boolCastTail]

/-- The Bool cast's actual `test_eq` and `not` instructions produce the
normalized nonzero predicate, preserving cache hits, fresh assignments, and
the output-slot frame. -/
private theorem boolCast_step (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (text : String) (term : Native.Term)
    (stateMeaning : LowerStateMeaning hash witness state)
    (meaning : OperandMeaning hash inputs witness text term)
    (scope : TextScope state.next text)
    (budget : ((boolCastTail text).run state).2.next ≤
      Native.maxInstructions * Native.maxVectorLength) :
    Nonempty (NativeStepResult hash inputs witness state (boolCastTail text)
      (.unary "not" (.binary "test_eq" term (.constant 0)))) := by
  have notFrame (compared : String) :
      Zkir.PreservesOutputCapacityFrame (Zkir.unary "not" compared) :=
    Zkir.ordinaryUnary_preservesOutputCapacityFrame "not" compared
      ⟨by decide, by decide, by decide⟩
  have compareBudget : ((Zkir.binary "test_eq" text "0x00").run state).2.next ≤
      Native.maxInstructions * Native.maxVectorLength := by
    have frame := (notFrame ((Zkir.binary "test_eq" text "0x00").run state).1
      ((Zkir.binary "test_eq" text "0x00").run state).2).next
    change ((do
      let compared ← Zkir.binary "test_eq" text "0x00"
      Zkir.unary "not" compared).run state).2.next ≤ _ at budget
    rw [StateT.run_bind] at budget
    exact Nat.le_trans frame budget
  have zeroSpelling : Zkir.fieldImmediate 0 = "0x00" := by decide
  have zeroMeaning : OperandMeaning hash inputs witness "0x00" (.constant 0) := by
    simpa only [zeroSpelling] using
      OperandMeaning.fieldImmediate hash inputs witness 0 (by decide)
  have zeroScope : TextScope state.next "0x00" := by
    simpa only [zeroSpelling] using TextScope.fieldImmediate state.next 0 (by decide)
  obtain ⟨compared⟩ := binary_testEq_step hash inputs witness state text "0x00"
    term (.constant 0) stateMeaning meaning zeroMeaning scope zeroScope compareBudget
  have compareNext : state.next ≤ compared.finalState.next := by
    simpa only [compared.run] using
      (Zkir.ordinaryBinary_preservesOutputCapacityFrame "test_eq" text "0x00"
        ⟨by decide, by decide, by decide⟩ state).next
  have boolean : interpret hash inputs (.binary "test_eq" term (.constant 0)) = zero ∨
      interpret hash inputs (.binary "test_eq" term (.constant 0)) = one := by
    rcases meaning with ⟨source, _, sourceValue⟩
    rw [interpret_testEq]
    simp only [sourceValue, interpret_constant, Option.bind_some, scalar_zero]
    cases decide (source.read witness = zero) <;> simp [bit]
  have notBudget : ((Zkir.unary "not" compared.text).run compared.finalState).2.next ≤
      Native.maxInstructions * Native.maxVectorLength := by
    change ((do
      let comparedText ← Zkir.binary "test_eq" text "0x00"
      Zkir.unary "not" comparedText).run state).2.next ≤ _ at budget
    rw [StateT.run_bind, compared.run] at budget
    exact budget
  obtain ⟨negated⟩ := unary_not_step hash inputs compared.finalWitness compared.finalState
    compared.text (.binary "test_eq" term (.constant 0)) compared.stateMeaning
    compared.operandMeaning compared.textScope boolean notBudget
  exact ⟨compared.chain (fun comparedText => Zkir.unary "not" comparedText)
    negated compareNext⟩

/-- A checked scalar source cast to Bool lowers through `test_eq` against zero
and `not`. `sourceType` covers Native, Bool, and UInt sources. -/
theorem complete_cast_bool {sourceTy : Ty} (value : Expr sourceTy)
    (sourceType : ScalarType sourceTy) (admission : ScalarExpression value)
    (complete : ExprComplete value) : ExprComplete (.cast .bool value) := by
  intro ctx hash implementation inputs witness state normalAliases values types result
    valid success aliases lowerAliases stateMeaning budget
  have validChildren : (do
      Ty.bool.validate Capabilities.crypto
      value.validate Capabilities.crypto types) = .ok () := by
    cases sourceType <;>
      simpa [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString,
        Ty.isJubjub, Ty.isForeign, Capabilities.crypto] using valid
  obtain ⟨_, _, valueValid⟩ := ScalarValidationMeaning.bind_ok.mp validChildren
  cases valueEvaluation : value.eval ctx values with
  | error message =>
    cases sourceType <;>
      simp [Expr.eval, valueEvaluation, Bind.bind, Except.bind, Ty.isBytes,
        Ty.isJubjub, Ty.isForeign] at success
  | ok sourceValue =>
    have castValue : result = (number sourceType sourceValue != 0) := by
      rw [eval_cast_scalar ctx values value sourceType ScalarType.bool sourceValue valueEvaluation]
        at success
      simp only [scalarCast] at success
      exact (Except.ok.inj success).symm
    have castAdmission : ScalarExpression (.cast .bool value) :=
      .cast value sourceType .bool admission
    have tailFrame (text : String) :
        Zkir.PreservesOutputCapacityFrame (boolCastTail text) :=
      boolCastTail_preservesOutputCapacityFrame text
    have childBudget : ((Zkir.lowerExpr value).run state).2.next ≤
        Native.maxInstructions * Native.maxVectorLength := by
      rw [lowerExpr_boolCast, StateT.run_bind] at budget
      exact Nat.le_trans
        (tailFrame ((Zkir.lowerExpr value).run state).1
          ((Zkir.lowerExpr value).run state).2).next budget
    obtain ⟨child⟩ := complete ctx hash implementation inputs witness state normalAliases values
      types sourceValue valueValid valueEvaluation aliases lowerAliases stateMeaning childBudget
    have childNext : state.next ≤ child.finalState.next := by
      simpa only [child.run] using
        (lowerExpr_admitted_preservesOutputCapacityFrame value admission state).next
    have tailBudget : (boolCastTail child.text).run child.finalState |>.2.next ≤
        Native.maxInstructions * Native.maxVectorLength := by
      have bound := budget
      rw [lowerExpr_boolCast, StateT.run_bind, child.run] at bound
      exact bound
    obtain ⟨native⟩ := boolCast_step hash inputs child.finalWitness child.finalState
      child.text child.normalized.term child.stateMeaning child.operandMeaning child.textScope
      tailBudget
    obtain ⟨normalized, normalization, represents⟩ := normalize_success ctx hash
      implementation inputs normalAliases values aliases (.cast .bool value) castAdmission result success
    have termEq : normalized.term =
        .unary "not" (.binary "test_eq" child.normalized.term (.constant 0)) := by
      have normal := normalization
      simp only [Backend.Native.normalize, child.normalization] at normal
      cases normal
      simp only [Backend.Native.requireSourceType_eq]
    have targetNumber : number ScalarType.bool result =
        (if number sourceType sourceValue = 0 then 0 else 1) := by
      rw [castValue]
      cases sourceType with
      | native => cases sourceValue <;> rfl
      | bool => cases sourceValue <;> rfl
      | uint maximum => cases sourceValue <;> rfl
    have targetMeaning : interpret hash inputs normalized.term =
        some (scalar (if number sourceType sourceValue = 0 then 0 else 1)) := by
      have represented := represents.2.2
      rw [sourceScalar_number ScalarType.bool result] at represented
      rw [targetNumber] at represented
      exact represented
    have aliasesInScope : ∀ name text, (name, text) ∈ native.finalState.aliases →
        TextScope child.finalState.next text := by
      intro name text member
      rw [native.aliasesPreserved] at member
      exact child.stateMeaning.aliases name text member
    have childAliasAgreement : LowerAliasAgreement hash inputs child.finalWitness
        normalAliases native.finalState.aliases values := by
      simpa only [native.aliasesPreserved] using child.aliasAgreement
    refine ⟨{
      text := native.text
      finalState := native.finalState
      finalWitness := native.finalWitness
      normalized
      run := ?_
      normalization
      represents
      operandMeaning := ?_
      textScope := native.textScope
      stateMeaning := native.stateMeaning
      budget := native.budget
      aliasAgreement := ?_
      aliasesPreserved := native.aliasesPreserved.trans child.aliasesPreserved
      frame := ?_
    }⟩
    · rw [lowerExpr_boolCast, StateT.run_bind, child.run]
      exact native.run
    · rcases native.operandMeaning with ⟨operand, parsed, nativeMeaning⟩
      have nativeMeaningAtNormalized : interpret hash inputs normalized.term =
          some (operand.read native.finalWitness) := by
        rw [termEq]
        exact nativeMeaning
      have outputMeaning : operand.read native.finalWitness =
          scalar (if number sourceType sourceValue = 0 then 0 else 1) :=
        Option.some.inj (nativeMeaningAtNormalized.symm.trans targetMeaning)
      refine ⟨operand, parsed, ?_⟩
      rw [termEq]
      calc
        interpret hash inputs
            (.unary "not" (.binary "test_eq" child.normalized.term (.constant 0))) =
            some (scalar (if number sourceType sourceValue = 0 then 0 else 1)) := by
          rw [← termEq]
          exact targetMeaning
        _ = some (operand.read native.finalWitness) := by rw [outputMeaning.symm]
    · exact LowerAliasAgreement.of_frame hash inputs child.finalWitness native.finalWitness
        child.finalState.next normalAliases native.finalState.aliases values childAliasAgreement
        aliasesInScope native.frame
    · intro name inScopeAt
      exact (native.frame name (InScope.mono childNext inScopeAt)).trans
        (child.frame name inScopeAt)

end Noctium.Verification.ScalarWitnessConstruction
