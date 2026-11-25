import Noctium.Verification.ScalarStateExtensions
import Noctium.Verification.ScalarExpressionArithmetic

namespace Noctium.Verification.ScalarExpressionAssertion
open Lean Backend NativeRelation NativeRelationJson ScalarNormalization ScalarLowering ScalarWitness ScalarAllocation

/-- A helper assertion is emitted after its successful Boolean condition and
before its body. Native nonzero follows from the source value one. -/
theorem exprComplete_assertE (condition : Expr .bool) (body : Expr ty)
    (conditionComplete : ExprComplete condition) (bodyComplete : ExprComplete body) :
    ExprComplete (.assertE condition body) := by
  intro ctx hash implementation inputs witness state normalAliases values types value
    valid success aliases lowerAliases meaning budget
  have validation := valid
  change (do condition.validate {poseidon2 := true} types; body.validate {poseidon2 := true} types) = .ok () at validation
  simp only [ScalarValidation.bind_ok] at validation
  obtain ⟨checkedUnit, conditionValid, bodyValid⟩ := validation
  have sourceSuccess := success
  cases conditionEval : condition.eval ctx values with
  | error message => simp [Expr.eval, conditionEval, Bind.bind, Except.bind] at success
  | ok bit =>
    cases bit with
    | false => simp [Expr.eval, conditionEval, Bind.bind, Except.bind] at success
    | true =>
      have bodySuccess : body.eval ctx values = .ok value := by
        simpa only [Expr.eval, conditionEval, Bind.bind, Except.bind, Bool.true_eq_false, ↓reduceIte] using success
      have suffixFrame : ∀ (text : String), PreservesFrame (do
        Zkir.emit "assert" [("cond", toJson text)]
        Zkir.lowerExpr body) := by
        intro text
        exact bind_preserves _ _ (emit_preserves _ _) (fun _ => lowerExpr_preserves body)
      have conditionBudget : ((Zkir.lowerExpr condition).run state).2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
        apply bind_middle_budget (Zkir.lowerExpr condition)
          (fun text => do Zkir.emit "assert" [("cond", toJson text)]; Zkir.lowerExpr body)
          state suffixFrame (Native.maxInstructions * Native.maxVectorLength)
        exact budget
      obtain ⟨first⟩ := conditionComplete ctx hash implementation inputs witness state normalAliases values types true
        conditionValid conditionEval aliases lowerAliases meaning conditionBudget
      let assertedState : Zkir.LowerState := {first.finalState with
        instructions := first.finalState.instructions.push (Zkir.instruction "assert" [("cond", toJson first.text)])}
      obtain ⟨operand, parsed, read⟩ := first.operandMeaning
      have oneValue : operand.read first.finalWitness = one :=
        read.trans (by simpa [number, scalar_one] using first.represents.2.2)
      have assertionMeaning : LowerStateMeaning hash first.finalWitness assertedState := by
        apply LowerStateMeaning.append hash first.finalWitness first.finalState first.stateMeaning _ _
          (ScalarInstructionEncoding.decode_assert_instruction parsed)
        · change operand.read first.finalWitness ≠ zero
          rw [oneValue]
          decide
        · exact ScalarExpressionArithmetic.TextScope.identifiers first.textScope parsed
      have bodyBudget : ((Zkir.lowerExpr body).run assertedState).2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
        have endBudget := budget
        change ((do
          let text ← Zkir.lowerExpr condition
          Zkir.emit "assert" [("cond", toJson text)]
          Zkir.lowerExpr body).run state).2.next ≤ _ at endBudget
        rw [StateT.run_bind, first.run] at endBudget
        exact endBudget
      obtain ⟨second⟩ := bodyComplete ctx hash implementation inputs first.finalWitness assertedState
        normalAliases values types value bodyValid bodySuccess aliases first.aliasAgreement assertionMeaning bodyBudget
      obtain ⟨normalized, normalization, represents⟩ := normalize_success ctx hash implementation inputs
        normalAliases values aliases (.assertE condition body) value sourceSuccess
      have termEq : normalized.term = second.normalized.term := by
        have actual := normalization
        change (do
          let condition ← Native.normalize normalAliases condition
          let body ← Native.normalize normalAliases body
          pure {body with bounds := condition.bounds ++ body.bounds, assertions := condition.assertions ++ [condition.term] ++ body.assertions}) = .ok normalized at actual
        rw [first.normalization, second.normalization] at actual
        change Except.ok _ = Except.ok normalized at actual
        cases actual
        rfl
      refine ⟨{text := second.text, finalState := second.finalState, finalWitness := second.finalWitness, normalized, run := ?_, normalization, represents, operandMeaning := ?_, textScope := second.textScope, stateMeaning := second.stateMeaning, budget := second.budget, aliasAgreement := second.aliasAgreement, aliasesPreserved := second.aliasesPreserved.trans first.aliasesPreserved, frame := ?_}⟩
      · change ((do
          let text ← Zkir.lowerExpr condition
          Zkir.emit "assert" [("cond", toJson text)]
          Zkir.lowerExpr body).run state) = _
        rw [StateT.run_bind, first.run]
        exact second.run
      · rw [termEq]
        exact second.operandMeaning
      · intro name scope
        have monotone := lowerExpr_next condition state
        rw [first.run] at monotone
        exact (second.frame name (InScope.mono monotone scope)).trans (first.frame name scope)

end Noctium.Verification.ScalarExpressionAssertion
