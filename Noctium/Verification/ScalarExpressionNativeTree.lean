import Noctium.Verification.ScalarExpressionNativeArithmetic

namespace Noctium.Verification.ScalarWitnessConstruction

open Lean Backend NativeRelation NativeRelationJson ScalarNormalization ScalarLowering
open ScalarInstructionEncoding ScalarWitness

/-- Disclosure keeps evaluation, normalization, and lowering evidence from its
child expression. -/
private theorem complete_disclose (span : SourceSpan) (expression : Expr ty)
    (complete : ExprComplete expression) : ExprComplete (.disclose span expression) := by
  intro ctx hash implementation inputs witness state normalAliases values types value
    valid success aliasAgreement lowerAliasAgreement lowerStateMeaning budget
  have childValid : expression.validate {poseidon2 := true} types = .ok () := by
    simpa only [Expr.validate] using valid
  have childSuccess : expression.eval ctx values = .ok value := by
    simpa only [Expr.eval] using success
  rcases complete ctx hash implementation inputs witness state normalAliases values types value
      childValid childSuccess aliasAgreement lowerAliasAgreement lowerStateMeaning
      (by simpa only [Zkir.lowerExpr] using budget) with ⟨result⟩
  refine ⟨?_⟩
  refine {
    text := result.text
    finalState := result.finalState
    finalWitness := result.finalWitness
    normalized := result.normalized
    run := ?_
    normalization := ?_
    represents := result.represents
    operandMeaning := result.operandMeaning
    textScope := result.textScope
    stateMeaning := result.stateMeaning
    budget := result.budget
    aliasAgreement := result.aliasAgreement
    aliasesPreserved := result.aliasesPreserved
    frame := result.frame }
  · simpa only [Zkir.lowerExpr] using result.run
  · simpa only [Backend.Native.normalize] using result.normalization

/-- The admitted Native arithmetic fragment has only literals, Native refs,
add, multiply, subtract, and disclosure. Every admitted expression has both a
scalar-normalization admission and a witness-complete lowerer proof. -/
inductive NativeArithmeticTree : Expr .native → Prop where
  | literal (number : Nat) : NativeArithmeticTree (.native number)
  | ref (name : String) : NativeArithmeticTree (.ref (ty := .native) name)
  | add {left right : Expr .native} (leftTree : NativeArithmeticTree left)
      (rightTree : NativeArithmeticTree right) : NativeArithmeticTree (.add left right)
  | mul {left right : Expr .native} (leftTree : NativeArithmeticTree left)
      (rightTree : NativeArithmeticTree right) : NativeArithmeticTree (.mul left right)
  | sub {left right : Expr .native} (leftTree : NativeArithmeticTree left)
      (rightTree : NativeArithmeticTree right) : NativeArithmeticTree (.sub left right)
  | disclose (span : SourceSpan) {value : Expr .native}
      (valueTree : NativeArithmeticTree value) : NativeArithmeticTree (.disclose span value)

theorem nativeArithmeticTree_complete {expression : Expr .native}
    (tree : NativeArithmeticTree expression) :
    ScalarExpression expression ∧ ExprComplete expression := by
  induction tree with
  | literal number =>
    exact ⟨.native number, complete_native number⟩
  | ref name =>
    exact ⟨.ref name ScalarType.native,
      complete_ref .native ScalarType.native name⟩
  | add leftTree rightTree ihLeft ihRight =>
    obtain ⟨leftAdmitted, completeLeft⟩ := ihLeft
    obtain ⟨rightAdmitted, completeRight⟩ := ihRight
    exact ⟨.add _ _ leftAdmitted rightAdmitted,
      complete_add _ _ leftAdmitted rightAdmitted completeLeft completeRight⟩
  | mul leftTree rightTree ihLeft ihRight =>
    obtain ⟨leftAdmitted, completeLeft⟩ := ihLeft
    obtain ⟨rightAdmitted, completeRight⟩ := ihRight
    exact ⟨.mul _ _ leftAdmitted rightAdmitted,
      complete_mul _ _ leftAdmitted rightAdmitted completeLeft completeRight⟩
  | sub leftTree rightTree ihLeft ihRight =>
    obtain ⟨leftAdmitted, completeLeft⟩ := ihLeft
    obtain ⟨rightAdmitted, completeRight⟩ := ihRight
    exact ⟨.sub _ _ leftAdmitted rightAdmitted,
      complete_sub _ _ leftAdmitted rightAdmitted completeLeft completeRight⟩
  | disclose span valueTree ih =>
    obtain ⟨valueAdmitted, completeValue⟩ := ih
    exact ⟨.disclose span _ valueAdmitted, complete_disclose span _ completeValue⟩

end Noctium.Verification.ScalarWitnessConstruction
