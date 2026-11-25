import Noctium.Verification.ScalarCircuit
import Noctium.Verification.ScalarLowering

namespace Noctium.Verification.ScalarWitnessConstruction

open Backend NativeRelation ScalarNormalization ScalarLowering

/-- A Native cast emits exactly the child lowering. Successful checked source
evaluation therefore supplies the child witness step, while normalization
records the same Native term for the cast result. -/
theorem complete_native_cast {ty : Ty} (value : Expr ty)
    (sourceType : ScalarType ty) (admitted : ScalarExpression value)
    (complete : ExprComplete value) : ExprComplete (.cast .native value) := by
  intro ctx hash implementation inputs witness state normalAliases values types result
    valid success aliases lowerAliases stateMeaning budget
  have childValid : value.validate Capabilities.crypto types = .ok () := by
    cases sourceType <;>
      simpa [Expr.validate, Ty.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString,
        Ty.isJubjub, Ty.isForeign, Ty.scalarKind, ScalarPolicy.validate,
        Capabilities.crypto] using valid
  have childEvaluates : ∃ childValue, value.eval ctx values = .ok childValue := by
    cases sourceType with
    | native =>
      cases sourceEval : value.eval ctx values with
      | error message =>
        simp only [Expr.eval, sourceEval, Bind.bind, Except.bind] at success
        cases success
      | ok childValue => exact ⟨childValue, rfl⟩
    | bool =>
      cases sourceEval : value.eval ctx values with
      | error message =>
        simp only [Expr.eval, sourceEval, Bind.bind, Except.bind] at success
        cases success
      | ok childValue => exact ⟨childValue, rfl⟩
    | uint maximum =>
      cases sourceEval : value.eval ctx values with
      | error message =>
        simp only [Expr.eval, sourceEval, Bind.bind, Except.bind] at success
        cases success
      | ok childValue => exact ⟨childValue, rfl⟩
  obtain ⟨childValue, childSuccess⟩ := childEvaluates
  have childBudget : ((Zkir.lowerExpr value).run state).2.next ≤
      Native.maxInstructions * Native.maxVectorLength := by
    have sameLower : Zkir.lowerExpr (.cast .native value) = Zkir.lowerExpr value := by
      simp [Zkir.lowerExpr]
    simpa only [sameLower] using budget
  obtain ⟨child⟩ := complete ctx hash implementation inputs witness state normalAliases
    values types childValue childValid childSuccess aliases lowerAliases stateMeaning childBudget
  have castAdmission : ScalarExpression (.cast .native value) :=
    .cast value sourceType .native admitted
  obtain ⟨normalized, normalization, represents⟩ :=
    normalize_success ctx hash implementation inputs normalAliases values aliases
      (.cast .native value) castAdmission result success
  have termEq : normalized.term = child.normalized.term := by
    have checked := normalization
    simp only [Native.normalize, child.normalization, Bind.bind, Except.bind,
      Pure.pure, Except.pure] at checked
    cases checked
    rfl
  refine ⟨{
    text := child.text
    finalState := child.finalState
    finalWitness := child.finalWitness
    normalized := normalized
    run := ?_
    normalization := normalization
    represents := represents
    operandMeaning := ?_
    textScope := child.textScope
    stateMeaning := child.stateMeaning
    budget := child.budget
    aliasAgreement := child.aliasAgreement
    aliasesPreserved := child.aliasesPreserved
    frame := child.frame
  }⟩
  · have sameLower : Zkir.lowerExpr (.cast .native value) = Zkir.lowerExpr value := by
      simp [Zkir.lowerExpr]
    simpa only [sameLower] using child.run
  · rw [termEq]
    exact child.operandMeaning

/-- Scalar circuit outputs project to one native field. Their field witness
completeness follows from the source expression, including Bool and UInt casts. -/
theorem complete_scalar_return_fields (circuit : Circuit)
    (admitted : ScalarCircuitAdmission circuit)
    (complete : ∀ returned ∈ circuit.outputs, ExprComplete returned.value) :
    ∀ returned ∈ circuit.outputs, ∀ fields,
      returned.nativeReturnFields = .ok fields →
      ∀ field ∈ fields, ExprComplete field := by
  intro returned returnedMember fields projection field fieldMember
  cases returned with
  | mk name ty value span =>
    obtain ⟨sourceType, expressionAdmission⟩ :=
      admitted.outputs ⟨name, ty, value, span⟩ returnedMember
    cases sourceType with
    | native =>
      have fieldsEq : fields = [value] := by
        change Except.ok [value] = Except.ok fields at projection
        exact (Except.ok.inj projection).symm
      subst fields
      have fieldEq : field = value := List.mem_singleton.mp fieldMember
      subst field
      exact complete ⟨name, .native, value, span⟩ returnedMember
    | bool =>
      have fieldsEq : fields = [.cast .native value] := by
        change Except.ok [.cast .native value] = Except.ok fields at projection
        exact (Except.ok.inj projection).symm
      subst fields
      have fieldEq : field = .cast .native value := List.mem_singleton.mp fieldMember
      subst field
      exact complete_native_cast value .bool expressionAdmission
        (complete ⟨name, .bool, value, span⟩ returnedMember)
    | uint maximum =>
      have fieldsEq : fields = [.cast .native value] := by
        change Except.ok [.cast .native value] = Except.ok fields at projection
        exact (Except.ok.inj projection).symm
      subst fields
      have fieldEq : field = .cast .native value := List.mem_singleton.mp fieldMember
      subst field
      exact complete_native_cast value (.uint maximum) expressionAdmission
        (complete ⟨name, .uint maximum, value, span⟩ returnedMember)

end Noctium.Verification.ScalarWitnessConstruction
