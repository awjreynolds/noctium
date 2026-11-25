import Noctium.Verification.ScalarStateExtensions

namespace Noctium.Verification.ScalarWitnessConstruction

open Lean Backend NativeRelation NativeRelationJson ScalarNormalization ScalarLowering
open ScalarInstructionEncoding ScalarWitness

private def unchanged_result (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (normalAliases : Native.AliasEnvironment) (values : EvalEnv)
    (expression : Expr ty) (value : ty.Denote) (text : String) (normalized : Native.Normalized)
    (run : (Zkir.lowerExpr expression).run state = (text, state))
    (normalization : Native.normalize normalAliases expression = .ok normalized)
    (represents : Represents hash inputs ty normalized value)
    (meaning : OperandMeaning hash inputs witness text normalized.term)
    (scope : TextScope state.next text)
    (aliases : LowerAliasAgreement hash inputs witness normalAliases state.aliases values)
    (stateMeaning : LowerStateMeaning hash witness state)
    (budget : ((Zkir.lowerExpr expression).run state).2.next ≤
      Native.maxInstructions * Native.maxVectorLength) :
    ExprStepResult hash inputs witness state normalAliases values expression value := {
  text, finalState := state, finalWitness := witness, normalized
  run, normalization, represents, operandMeaning := meaning, textScope := scope, stateMeaning
  budget := by rw [run] at budget; exact budget
  aliasAgreement := aliases
  aliasesPreserved := rfl
  frame := by intro name _; rfl
}

theorem complete_native (number : Nat) : ExprComplete (.native number) := by
  intro ctx hash implementation inputs witness state normalAliases values types value
    valid success aliases lowerAliases stateMeaning budget
  have admission : ScalarExpression (.native number) := .native number
  have sourceSuccess := success
  simp only [Expr.eval] at success
  split at success
  next canonical =>
    cases success
    have canonical : number < Field.modulus := by
      simpa only [implementation.modulus] using canonical
    obtain ⟨normalized, normalization, represents⟩ :=
      normalize_success ctx hash implementation inputs normalAliases values aliases
        (.native number) admission number sourceSuccess
    have normalizedEq : normalized = ({term := .constant number} : Native.Normalized) := by
      have norm := normalization
      simp only [Native.normalize, pure, Except.pure] at norm
      exact (Except.ok.inj norm).symm
    exact ⟨unchanged_result hash inputs witness state normalAliases values
      (.native number) number _ normalized (lowerExpr_native_run state number) normalization represents
      (by rw [normalizedEq]; exact OperandMeaning.fieldImmediate hash inputs witness number canonical)
      (TextScope.fieldImmediate state.next number canonical) lowerAliases stateMeaning budget⟩
  next => cases success

theorem complete_bool (boolean : Bool) : ExprComplete (.bool boolean) := by
  intro ctx hash implementation inputs witness state normalAliases values types value
    valid success aliases lowerAliases stateMeaning budget
  have admission : ScalarExpression (.bool boolean) := .bool boolean
  have sourceSuccess := success
  simp only [Expr.eval] at success
  cases success
  obtain ⟨normalized, normalization, represents⟩ :=
    normalize_success ctx hash implementation inputs normalAliases values aliases
      (.bool boolean) admission boolean sourceSuccess
  cases boolean
  ·
    have normalizedEq : normalized =
        {term := .constant 0, bounds := [(.constant 0, 1)] : Native.Normalized} := by
      have norm := normalization
      simp only [Native.normalize, Native.requireSourceType_eq, pure, Except.pure] at norm
      exact (Except.ok.inj norm).symm
    have spelling : Zkir.fieldImmediate 0 = "0x00" := by decide
    exact ⟨unchanged_result hash inputs witness state normalAliases values
      (.bool false) false "0x00" normalized
      (by simpa using lowerExpr_bool_run state false) normalization represents
      (by rw [normalizedEq]; simpa only [spelling] using OperandMeaning.fieldImmediate hash inputs witness 0 (by decide))
      (by simpa only [spelling] using TextScope.fieldImmediate state.next 0 (by decide))
      lowerAliases stateMeaning budget⟩
  ·
    have normalizedEq : normalized =
        {term := .constant 1, bounds := [(.constant 1, 1)] : Native.Normalized} := by
      have norm := normalization
      simp only [Native.normalize, Native.requireSourceType_eq, pure, Except.pure] at norm
      exact (Except.ok.inj norm).symm
    have spelling : Zkir.fieldImmediate 1 = "0x01" := by decide
    exact ⟨unchanged_result hash inputs witness state normalAliases values
      (.bool true) true "0x01" normalized
      (by simpa using lowerExpr_bool_run state true) normalization represents
      (by rw [normalizedEq]; simpa only [spelling] using OperandMeaning.fieldImmediate hash inputs witness 1 (by decide))
      (by simpa only [spelling] using TextScope.fieldImmediate state.next 1 (by decide))
      lowerAliases stateMeaning budget⟩

theorem complete_uint (maximum number : Nat) : ExprComplete (.uint maximum number) := by
  intro ctx hash implementation inputs witness state normalAliases values types value
    valid success aliases lowerAliases stateMeaning budget
  have admission : ScalarExpression (.uint maximum number) := .uint maximum number
  have sourceSuccess := success
  simp only [Expr.eval] at success
  split at success
  next canonical =>
    cases success
    obtain ⟨normalized, normalization, represents⟩ :=
      normalize_success ctx hash implementation inputs normalAliases values aliases
        (.uint maximum number) admission number sourceSuccess
    have normalizedEq : normalized =
        {term := .constant number, bounds := [(.constant number, maximum)] : Native.Normalized} := by
      have norm := normalization
      simp only [Native.normalize, Native.requireSourceType_eq, pure, Except.pure] at norm
      exact (Except.ok.inj norm).symm
    have fieldCanonical : number < Field.modulus := represents.1.1
    exact ⟨unchanged_result hash inputs witness state normalAliases values
      (.uint maximum number) number _ normalized (lowerExpr_uint_run state maximum number) normalization represents
      (by rw [normalizedEq]; exact OperandMeaning.fieldImmediate hash inputs witness number fieldCanonical)
      (TextScope.fieldImmediate state.next number fieldCanonical)
      lowerAliases stateMeaning budget⟩
  next => cases success

theorem complete_ref (ty : Ty) (supported : ScalarType ty) (name : String) :
    ExprComplete (.ref (ty := ty) name) := by
  intro ctx hash implementation inputs witness state normalAliases values types value
    valid success aliases lowerAliases stateMeaning budget
  have admission : ScalarExpression (.ref (ty := ty) name) := .ref name supported
  have sourceSuccess := success
  simp only [Expr.eval] at success
  cases lookup : values.lookup name with
  | none => simp [lookup] at success
  | some raw =>
    simp only [lookup] at success
    cases typed : raw.as ty with
    | none => simp [typed] at success
    | some foundValue =>
      simp only [typed] at success
      split at success
      next => cases success
      next =>
        cases success
        obtain ⟨term, normalLookup, meaning⟩ := lowerAliases name ty raw value lookup typed
        obtain ⟨normalized, normalization, represents⟩ :=
          normalize_success ctx hash implementation inputs normalAliases values aliases
            (.ref (ty := ty) name) admission value sourceSuccess
        have termEq : normalized.term = term := by
          have normal := normalization
          simp only [Native.normalize, normalLookup] at normal
          cases normal
          simp only [Native.requireSourceType_eq]
        have scope : TextScope state.next
            (state.aliases.lookup name |>.getD ("%input_" ++ name)) := by
          obtain ⟨operand, parsed, _⟩ := meaning
          exact TextScope.lookup_default state.next state.aliases name operand parsed stateMeaning.aliases
        exact ⟨unchanged_result hash inputs witness state normalAliases values
          (.ref (ty := ty) name) value _ normalized
          (lowerExpr_ref_run state ty supported name) normalization represents
          (by rw [termEq]; exact meaning) scope lowerAliases stateMeaning budget⟩

end Noctium.Verification.ScalarWitnessConstruction
