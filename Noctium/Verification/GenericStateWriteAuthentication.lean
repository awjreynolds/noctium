import Noctium.Verification.GenericStateWriteInversion
import Noctium.Verification.GenericStateEvaluationCanonical
import Noctium.Verification.GenericStateSchemaSpans
import Noctium.Verification.GuardedEffectPrefix

namespace Noctium.Verification.GenericStateWriteAuthentication
open Backend NativeState NativeRelation ScalarNormalization

/-- The exact appended Cell write agrees with the source when the emitted expressions
have the original evaluation. -/
theorem writeCell_chunk_source_step (ctx : EvalContext)
    (sourceEnv candidateEnv : EvalEnv) (state : List StateDecl)
    (current : LedgerState) (slots : List NativeState.Slot)
    (name : String) (ty : Ty) (expression emittedValue : Expr ty)
    (admission : ScalarExpression expression)
    (agreement : expression.eval ctx sourceEnv = emittedValue.eval ctx candidateEnv)
    (before plan : Impact.Plan) (segment : List NativeState.Op)
    (reads : List NativeState.Cell) (after : NativeState.Machine)
    (compiled : Impact.appendEffect state (.writeCell name ty emittedValue)
      before = .ok plan)
    (sourceDeclaration : StateDecl)
    (sourceFound : state.find? (·.name == name) = some sourceDeclaration)
    (sourceNamed : sourceDeclaration.name = name)
    (sourceKind : sourceDeclaration.kind = .cell ty)
    (distinct : state.Pairwise (fun left right => left.name ≠ right.name))
    (encoded : GenericStateEncoding.encodeState state current = some slots)
    (stateBound : state.length < Field.modulus)
    (modulus : ctx.modulus = Field.modulus)
    (evaluated : (plan.operations.drop before.operations.length).mapM
        (GenericStateOps.evalOp ctx candidateEnv) =
      .ok segment)
    (checked : NativeState.run segment ⟨[.vector slots], reads⟩ = some after) :
    ∃ next nextSlots,
      SourceEffects.step ctx (.writeCell name ty expression) (sourceEnv, current) =
        .ok (sourceEnv, next) ∧
      GenericStateEncoding.encodeState state next = some nextSlots ∧
      after = ⟨[.vector nextSlots], reads⟩ := by
  obtain ⟨base, compiledBase, appended⟩ :=
    GuardedEffectPrefix.appendEffect_writeCell_chunk
      state name ty emittedValue before plan compiled
  have alignment := GenericStateSchemaSpans.encoded_named_cell_alignment_none
    state current slots name sourceDeclaration ty sourceFound sourceKind encoded
  have cellDecl : Impact.UnalignedCellDeclaration state name ty :=
    ⟨sourceDeclaration, sourceFound, sourceKind, alignment⟩
  have baseEval : base.operations.mapM (GenericStateOps.evalOp ctx candidateEnv) = .ok segment := by
    simpa [appended] using evaluated
  obtain ⟨support⟩ := GenericStateEvaluationCanonical.scalarExpression_type admission
  obtain ⟨value, candidateEval⟩ :=
    GenericStateWriteInversion.writeCell_source_evaluates state name ty emittedValue support
      cellDecl base ctx candidateEnv segment compiledBase modulus baseEval
  have sourceEval : expression.eval ctx sourceEnv = .ok value :=
    agreement.trans candidateEval
  have canonical :=
    GenericStateEvaluationCanonical.expression_eval_canonical
      ctx sourceEnv expression admission value modulus sourceEval
  obtain ⟨slot, located, segmentEval⟩ :=
    GenericStateWriteEvaluation.writeCell_candidate_eval state name ty
      emittedValue base ctx candidateEnv value compiledBase cellDecl stateBound modulus
      candidateEval canonical
  have typedAt : state[slot]? = some sourceDeclaration := by
    rw [List.find?_eq_bind_findIdx?_getElem?, located] at sourceFound
    exact sourceFound
  obtain ⟨next, sourceStep, nextEncoded, nativeRun⟩ :=
    GenericStateSchemaSpans.writeCell_source_step ctx sourceEnv state current
      slots slot sourceDeclaration name ty expression value reads typedAt
      sourceNamed sourceKind distinct encoded stateBound sourceEval canonical
  rw [segmentEval] at baseEval
  cases baseEval
  rw [nativeRun] at checked
  cases checked
  exact ⟨next, _, sourceStep, nextEncoded, rfl⟩

/-- A checked unguarded production cell-write suffix has exactly the source
transition and encoded successor, at Impact's actual chosen slot. -/
theorem writeCell_candidate_source_step (ctx : EvalContext)
    (sourceEnv candidateEnv : EvalEnv) (state : List StateDecl)
    (current : LedgerState) (slots : List NativeState.Slot)
    (name : String) (ty : Ty) (expression : Expr ty)
    (admission : ScalarExpression expression)
    (agreement : expression.eval ctx sourceEnv = expression.eval ctx candidateEnv)
    (before plan : Impact.Plan) (segment : List NativeState.Op)
    (reads : List NativeState.Cell) (after : NativeState.Machine)
    (compiled : Impact.appendEffectWithActivity state (.writeCell name ty expression)
      none before = .ok plan)
    (sourceDeclaration : StateDecl)
    (sourceFound : state.find? (·.name == name) = some sourceDeclaration)
    (sourceNamed : sourceDeclaration.name = name)
    (sourceKind : sourceDeclaration.kind = .cell ty)
    (distinct : state.Pairwise (fun left right => left.name ≠ right.name))
    (encoded : GenericStateEncoding.encodeState state current = some slots)
    (stateBound : state.length < Field.modulus)
    (modulus : ctx.modulus = Field.modulus)
    (evaluated : (plan.operations.drop before.operations.length).mapM
        (GenericStateOps.evalOp ctx candidateEnv) =
      .ok segment)
    (checked : NativeState.run segment ⟨[.vector slots], reads⟩ = some after) :
    ∃ next nextSlots,
      SourceEffects.step ctx (.writeCell name ty expression) (sourceEnv, current) =
        .ok (sourceEnv, next) ∧
      GenericStateEncoding.encodeState state next = some nextSlots ∧
      after = ⟨[.vector nextSlots], reads⟩ := by
  obtain ⟨raw, appended, sameOps, _⟩ := GuardedEffectPrefix.appendEffectWithActivity_none_result
    state (.writeCell name ty expression) before plan compiled
  rw [sameOps] at evaluated
  exact writeCell_chunk_source_step ctx sourceEnv candidateEnv state current slots name ty
    expression expression admission agreement before raw segment reads after appended
    sourceDeclaration sourceFound sourceNamed sourceKind distinct encoded stateBound modulus evaluated checked

/-- The exact appended Map write agrees with the source when the emitted expressions
have the original evaluation. -/
theorem writeMap_chunk_source_step (ctx : EvalContext)
    (sourceEnv candidateEnv : EvalEnv) (state : List StateDecl)
    (current : LedgerState) (slots : List NativeState.Slot)
    (name : String) (keyTy valueTy : Ty)
    (keyExpr emittedKey : Expr keyTy) (valueExpr emittedValue : Expr valueTy)
    (keyAdmission : ScalarExpression keyExpr) (valueAdmission : ScalarExpression valueExpr)
    (keyAgreement : keyExpr.eval ctx sourceEnv = emittedKey.eval ctx candidateEnv)
    (valueAgreement : valueExpr.eval ctx sourceEnv = emittedValue.eval ctx candidateEnv)
    (before plan : Impact.Plan) (segment : List NativeState.Op)
    (reads : List NativeState.Cell) (after : NativeState.Machine)
    (compiled : Impact.appendEffect state
      (.writeMap name keyTy valueTy emittedKey emittedValue) before = .ok plan)
    (sourceDeclaration : StateDecl)
    (sourceFound : state.find? (·.name == name) = some sourceDeclaration)
    (sourceNamed : sourceDeclaration.name = name)
    (sourceKind : sourceDeclaration.kind = .map keyTy valueTy)
    (distinct : state.Pairwise (fun left right => left.name ≠ right.name))
    (encoded : GenericStateEncoding.encodeState state current = some slots)
    (stateBound : state.length < Field.modulus)
    (modulus : ctx.modulus = Field.modulus)
    (evaluated : (plan.operations.drop before.operations.length).mapM
        (GenericStateOps.evalOp ctx candidateEnv) =
      .ok segment)
    (checked : NativeState.run segment ⟨[.vector slots], reads⟩ = some after) :
    ∃ next nextSlots,
      SourceEffects.step ctx
        (.writeMap name keyTy valueTy keyExpr valueExpr) (sourceEnv, current) =
        .ok (sourceEnv, next) ∧
      GenericStateEncoding.encodeState state next = some nextSlots ∧
      after = ⟨[.vector nextSlots], reads⟩ := by
  obtain ⟨base, compiledBase, appended⟩ :=
    GuardedEffectPrefix.appendEffect_writeMap_chunk
      state name keyTy valueTy emittedKey emittedValue before plan compiled
  have baseEval : base.operations.mapM (GenericStateOps.evalOp ctx candidateEnv) = .ok segment := by
    simpa [appended] using evaluated
  obtain ⟨keySupport⟩ := GenericStateEvaluationCanonical.scalarExpression_type keyAdmission
  obtain ⟨valueSupport⟩ := GenericStateEvaluationCanonical.scalarExpression_type valueAdmission
  obtain ⟨key, value, candidateKey, candidateValue⟩ :=
    GenericStateWriteInversion.writeMap_source_evaluates state name keyTy valueTy emittedKey emittedValue
      keySupport valueSupport base ctx candidateEnv segment compiledBase modulus baseEval
  have sourceKey : keyExpr.eval ctx sourceEnv = .ok key := keyAgreement.trans candidateKey
  have sourceValue : valueExpr.eval ctx sourceEnv = .ok value := valueAgreement.trans candidateValue
  have keyCanonical :=
    GenericStateEvaluationCanonical.expression_eval_canonical
      ctx sourceEnv keyExpr keyAdmission key modulus sourceKey
  have valueCanonical :=
    GenericStateEvaluationCanonical.expression_eval_canonical
      ctx sourceEnv valueExpr valueAdmission value modulus sourceValue
  obtain ⟨slot, located, segmentEval⟩ :=
    GenericStateWriteEvaluation.writeMap_candidate_eval state name keyTy valueTy
      emittedKey emittedValue base ctx candidateEnv key value compiledBase modulus
      candidateKey candidateValue keyCanonical valueCanonical
  have typedAt : state[slot]? = some sourceDeclaration := by
    rw [List.find?_eq_bind_findIdx?_getElem?, located] at sourceFound
    exact sourceFound
  obtain ⟨next, entries, sourceStep, nextEncoded, nativeRun⟩ :=
    GenericStateSchemaSpans.writeMap_source_step ctx sourceEnv state current
      slots slot sourceDeclaration name keyTy valueTy keyExpr valueExpr key value
      reads typedAt sourceNamed sourceKind distinct encoded stateBound sourceKey
      sourceValue keyCanonical valueCanonical
  rw [segmentEval] at baseEval
  cases baseEval
  rw [nativeRun] at checked
  cases checked
  exact ⟨next, _, sourceStep, nextEncoded, rfl⟩

/-- A checked unguarded production map-write suffix updates source and encoded
native slot by the same key and value. -/
theorem writeMap_candidate_source_step (ctx : EvalContext)
    (sourceEnv candidateEnv : EvalEnv) (state : List StateDecl)
    (current : LedgerState) (slots : List NativeState.Slot)
    (name : String) (keyTy valueTy : Ty)
    (keyExpr : Expr keyTy) (valueExpr : Expr valueTy)
    (keyAdmission : ScalarExpression keyExpr) (valueAdmission : ScalarExpression valueExpr)
    (keyAgreement : keyExpr.eval ctx sourceEnv = keyExpr.eval ctx candidateEnv)
    (valueAgreement : valueExpr.eval ctx sourceEnv = valueExpr.eval ctx candidateEnv)
    (before plan : Impact.Plan) (segment : List NativeState.Op)
    (reads : List NativeState.Cell) (after : NativeState.Machine)
    (compiled : Impact.appendEffectWithActivity state
      (.writeMap name keyTy valueTy keyExpr valueExpr) none before = .ok plan)
    (sourceDeclaration : StateDecl)
    (sourceFound : state.find? (·.name == name) = some sourceDeclaration)
    (sourceNamed : sourceDeclaration.name = name)
    (sourceKind : sourceDeclaration.kind = .map keyTy valueTy)
    (distinct : state.Pairwise (fun left right => left.name ≠ right.name))
    (encoded : GenericStateEncoding.encodeState state current = some slots)
    (stateBound : state.length < Field.modulus)
    (modulus : ctx.modulus = Field.modulus)
    (evaluated : (plan.operations.drop before.operations.length).mapM
        (GenericStateOps.evalOp ctx candidateEnv) =
      .ok segment)
    (checked : NativeState.run segment ⟨[.vector slots], reads⟩ = some after) :
    ∃ next nextSlots,
      SourceEffects.step ctx
        (.writeMap name keyTy valueTy keyExpr valueExpr) (sourceEnv, current) =
        .ok (sourceEnv, next) ∧
      GenericStateEncoding.encodeState state next = some nextSlots ∧
      after = ⟨[.vector nextSlots], reads⟩ := by
  obtain ⟨raw, appended, sameOps, _⟩ := GuardedEffectPrefix.appendEffectWithActivity_none_result
    state (.writeMap name keyTy valueTy keyExpr valueExpr) before plan compiled
  rw [sameOps] at evaluated
  exact writeMap_chunk_source_step ctx sourceEnv candidateEnv state current slots name keyTy valueTy
    keyExpr keyExpr valueExpr valueExpr keyAdmission valueAdmission keyAgreement valueAgreement
    before raw segment reads after appended sourceDeclaration sourceFound sourceNamed sourceKind
    distinct encoded stateBound modulus evaluated checked

end Noctium.Verification.GenericStateWriteAuthentication
