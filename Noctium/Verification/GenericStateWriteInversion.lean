import Noctium.Verification.GenericStateWriteEvaluation

namespace Noctium.Verification.GenericStateWriteInversion
open Backend ScalarNormalization

/-- Successful evaluation of the actual field projection requires successful
source evaluation and preserves its number. No source success is assumed. -/
theorem scalarProjection_invert (ctx : EvalContext) (env : EvalEnv)
    {ty : Ty} (support : ScalarType ty) (expression : Expr ty) (projectedNumber : Nat)
    (modulus : ctx.modulus = Field.modulus)
    (evaluated : (GenericStateWriteEvaluation.scalarProjection support expression).eval
      ctx env = .ok projectedNumber) :
    ∃ value, expression.eval ctx env = .ok value ∧
      projectedNumber = ScalarNormalization.number support value := by
  cases support with
  | native => exact ⟨projectedNumber, evaluated, rfl⟩
  | bool =>
    cases source : expression.eval ctx env with
    | error message =>
      simp [GenericStateWriteEvaluation.scalarProjection, Expr.eval, source,
        bind, Except.bind] at evaluated
    | ok value =>
      have projected : (GenericStateWriteEvaluation.scalarProjection ScalarType.bool
          expression).eval ctx env =
          .ok (ScalarNormalization.number ScalarType.bool value) := by
        cases value <;> simp [GenericStateWriteEvaluation.scalarProjection, Expr.eval, source,
          modulus, Field.modulus, ScalarNormalization.number, bind, Except.bind] <;> rfl
      rw [projected] at evaluated
      exact ⟨value, rfl, (Except.ok.inj evaluated).symm⟩
  | uint maximum =>
    cases source : expression.eval ctx env with
    | error message =>
      simp [GenericStateWriteEvaluation.scalarProjection, Expr.eval, source,
        Ty.isBytes, Ty.isJubjub, Ty.isForeign, bind, Except.bind] at evaluated
    | ok value =>
      simp only [GenericStateWriteEvaluation.scalarProjection] at evaluated
      rw [Expr.eval, source] at evaluated
      change (if value < ctx.modulus then Except.ok value
        else Except.error "noncanonical scalar conversion") = .ok projectedNumber at evaluated
      split at evaluated
      · exact ⟨value, rfl, (Except.ok.inj evaluated).symm⟩
      · cases evaluated

private theorem mapM_member_success (operations : List Impact.Op)
    (ctx : EvalContext) (env : EvalEnv) (native : List NativeState.Op)
    (evaluated : operations.mapM (GenericStateOps.evalOp ctx env) = .ok native) :
    ∀ operation ∈ operations, ∃ result, GenericStateOps.evalOp ctx env operation = .ok result := by
  induction operations generalizing native with
  | nil => simp
  | cons head rest ih =>
    simp only [List.mapM_cons] at evaluated
    cases first : GenericStateOps.evalOp ctx env head with
    | error message => simp [first, bind, Except.bind] at evaluated
    | ok result =>
      cases later : rest.mapM (GenericStateOps.evalOp ctx env) with
      | error message => simp [first, later, bind, Except.bind] at evaluated
      | ok results =>
        intro operation member
        rcases List.mem_cons.mp member with equal | present
        · subst operation
          exact ⟨result, first⟩
        · exact ih results later operation present

private theorem eval_push_source (ctx : EvalContext) (env : EvalEnv)
    (expression : Expr .native) (storage : Bool) (result : NativeState.Op)
    (evaluated : GenericStateOps.evalOp ctx env (.push (.field expression) storage) = .ok result) :
    ∃ number, expression.eval ctx env = .ok number := by
  cases source : expression.eval ctx env with
  | error message =>
    simp [GenericStateOps.evalOp, GenericStateOps.evalAligned,
      source, bind, Except.bind] at evaluated
  | ok number => exact ⟨number, rfl⟩

/-- An accepted, successfully evaluated production cell-write segment forces
the original typed source expression to evaluate. -/
theorem writeCell_source_evaluates (state : List StateDecl) (name : String)
    (ty : Ty) (expression : Expr ty) (support : ScalarType ty)
    (declaration : Impact.UnalignedCellDeclaration state name ty)
    (base : Impact.Plan)
    (ctx : EvalContext) (env : EvalEnv) (native : List NativeState.Op)
    (accepted : Impact.appendEffect state (.writeCell name ty expression) {} = .ok base)
    (modulus : ctx.modulus = Field.modulus)
    (evaluated : base.operations.mapM (GenericStateOps.evalOp ctx env) = .ok native) :
    ∃ value, expression.eval ctx env = .ok value := by
  obtain ⟨slot, _, shape⟩ := GenericStateWriteEvaluation.writeCell_scalar_chunk
    state name ty expression base support declaration accepted
  have member : Impact.Op.push
      (.field (GenericStateWriteEvaluation.scalarProjection support expression)) true ∈
      [Impact.Op.push (.field (.native slot)),
        .push (.field (GenericStateWriteEvaluation.scalarProjection support expression)) true,
        .insert 1] := by simp
  have shapedEvaluation := evaluated
  rw [shape] at shapedEvaluation
  obtain ⟨operation, operationEval⟩ :=
    mapM_member_success _ ctx env native shapedEvaluation _ member
  obtain ⟨number, projected⟩ := eval_push_source ctx env _ true operation operationEval
  obtain ⟨value, source, _⟩ := scalarProjection_invert ctx env support expression
    number modulus projected
  exact ⟨value, source⟩

/-- Both typed source map-write expressions evaluate whenever the actual
production key/value pushes evaluate successfully. -/
theorem writeMap_source_evaluates (state : List StateDecl) (name : String)
    (keyTy valueTy : Ty) (keyExpr : Expr keyTy) (valueExpr : Expr valueTy)
    (keySupport : ScalarType keyTy) (valueSupport : ScalarType valueTy)
    (base : Impact.Plan) (ctx : EvalContext) (env : EvalEnv)
    (native : List NativeState.Op)
    (accepted : Impact.appendEffect state
      (.writeMap name keyTy valueTy keyExpr valueExpr) {} = .ok base)
    (modulus : ctx.modulus = Field.modulus)
    (evaluated : base.operations.mapM (GenericStateOps.evalOp ctx env) = .ok native) :
    ∃ key value, keyExpr.eval ctx env = .ok key ∧ valueExpr.eval ctx env = .ok value := by
  obtain ⟨slot, _, shape⟩ := GenericStateWriteEvaluation.writeMap_scalar_chunk
    state name keyTy valueTy keyExpr valueExpr base keySupport valueSupport accepted
  have keyMember : Impact.Op.push
      (.field (GenericStateWriteEvaluation.scalarProjection keySupport keyExpr)) false ∈
      [.index slot true,
        .push (.field (GenericStateWriteEvaluation.scalarProjection keySupport keyExpr)),
        .push (.field (GenericStateWriteEvaluation.scalarProjection valueSupport valueExpr)) true,
        .insert 2] := by simp
  have valueMember : Impact.Op.push
      (.field (GenericStateWriteEvaluation.scalarProjection valueSupport valueExpr)) true ∈
      [.index slot true,
        .push (.field (GenericStateWriteEvaluation.scalarProjection keySupport keyExpr)),
        .push (.field (GenericStateWriteEvaluation.scalarProjection valueSupport valueExpr)) true,
        .insert 2] := by simp
  have shapedEvaluation := evaluated
  rw [shape] at shapedEvaluation
  obtain ⟨keyOp, keyOpEval⟩ :=
    mapM_member_success _ ctx env native shapedEvaluation _ keyMember
  obtain ⟨valueOp, valueOpEval⟩ :=
    mapM_member_success _ ctx env native shapedEvaluation _ valueMember
  obtain ⟨keyNumber, keyProjection⟩ := eval_push_source ctx env _ false keyOp keyOpEval
  obtain ⟨valueNumber, valueProjection⟩ := eval_push_source ctx env _ true valueOp valueOpEval
  obtain ⟨key, keyEval, _⟩ := scalarProjection_invert ctx env keySupport keyExpr
    keyNumber modulus keyProjection
  obtain ⟨value, valueEval, _⟩ := scalarProjection_invert ctx env valueSupport valueExpr
    valueNumber modulus valueProjection
  exact ⟨key, value, keyEval, valueEval⟩

end Noctium.Verification.GenericStateWriteInversion
