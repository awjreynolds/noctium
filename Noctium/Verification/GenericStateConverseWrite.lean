import Noctium.Verification.GenericStateSchemaSpans
import Noctium.Verification.GenericStateWriteSourceTrace
import Noctium.Verification.GenericStateWriteEvaluation
import Noctium.Verification.GuardedEffectPrefix

namespace Noctium.Verification.GenericStateConverseWrite
open Backend NativeRelation ScalarNormalization NativeState GenericStateEncoding

/-- A successful source cell write drives the actual unguarded suffix and
the same encoded VM successor. Candidate evaluation must agree on the
source-validated expression scope, established separately for full calls. -/
theorem source_writeCell_native (ctx : EvalContext)
    (sourceEnv candidateEnv : EvalEnv) (state : List StateDecl)
    (current : LedgerState) (slots : List Slot)
    (name : String) (ty : Ty) (expression : Expr ty)
    (admission : ScalarExpression expression)
    (sourceAfter : SourceEffects.Frame) (before plan : Impact.Plan)
    (reads : List Cell)
    (sourceStep : SourceEffects.step ctx (.writeCell name ty expression)
      (sourceEnv, current) = .ok sourceAfter)
    (candidateAgreement : expression.eval ctx candidateEnv =
      expression.eval ctx sourceEnv)
    (sourceDeclaration : StateDecl)
    (declared : state.find? (·.name == name) = some sourceDeclaration)
    (named : sourceDeclaration.name = name)
    (kind : sourceDeclaration.kind = .cell ty)
    (compiled : Impact.appendEffectWithActivity state (.writeCell name ty expression)
      none before = .ok plan)
    (encoded : encodeState state current = some slots)
    (distinct : state.Pairwise (fun left right => left.name ≠ right.name))
    (stateBound : state.length < Field.modulus)
    (modulus : ctx.modulus = Field.modulus) :
    ∃ slot value nextSlots,
      state.findIdx? (·.name == name) = some slot ∧
      (plan.operations.drop before.operations.length).mapM
        (GenericStateOps.evalOp ctx candidateEnv) =
        .ok (GenericStateVM.writeCellOps slot
          (field (scalar (number ty value)))) ∧
      encodeState state sourceAfter.2 = some nextSlots ∧
      run (GenericStateVM.writeCellOps slot
        (field (scalar (number ty value))))
        ⟨[.vector slots], reads⟩ =
        some ⟨[.vector nextSlots], reads⟩ ∧
      sourceAfter.1 = sourceEnv := by
  obtain ⟨_, value, _, sourceEval, canonical, _⟩ :=
    GenericStateWriteSourceTrace.writeCell_step_value ctx sourceEnv current
      name ty expression sourceAfter admission modulus sourceStep
  have candidateEval : expression.eval ctx candidateEnv = .ok value := by
    rw [candidateAgreement]
    exact sourceEval
  obtain ⟨base, compiledBase, appended⟩ :=
    GuardedEffectPrefix.appendEffectWithActivity_unguarded_writeCell_chunk
      state name ty expression before plan compiled
  have alignment := GenericStateSchemaSpans.encoded_named_cell_alignment_none
    state current slots name sourceDeclaration ty declared kind encoded
  have cellDecl : Impact.UnalignedCellDeclaration state name ty :=
    ⟨sourceDeclaration, declared, kind, alignment⟩
  obtain ⟨slot, located, segmentEval⟩ :=
    GenericStateWriteEvaluation.writeCell_candidate_eval state name ty
      expression base ctx candidateEnv value compiledBase cellDecl stateBound modulus
      candidateEval canonical
  have declarationAt : state[slot]? = some sourceDeclaration := by
    rw [List.find?_eq_bind_findIdx?_getElem?, located] at declared
    exact declared
  obtain ⟨next, sourceAgain, encodedNext, nativeRun⟩ :=
    GenericStateSchemaSpans.writeCell_source_step ctx sourceEnv state current
      slots slot sourceDeclaration name ty expression value reads declarationAt
      named kind distinct encoded stateBound sourceEval canonical
  have sameFrame : sourceAfter = (sourceEnv, next) := by
    rw [sourceStep] at sourceAgain
    exact Except.ok.inj sourceAgain
  refine ⟨slot, value,
    slots.set slot (.cell (field (scalar (number ty value)))), located,
    (by simpa [appended] using segmentEval), ?_, nativeRun, ?_⟩
  · rw [sameFrame]
    exact encodedNext
  · rw [sameFrame]

/-- A successful source map write drives the actual unguarded key/value
segment and the same encoded VM successor. -/
theorem source_writeMap_native (ctx : EvalContext)
    (sourceEnv candidateEnv : EvalEnv) (state : List StateDecl)
    (current : LedgerState) (slots : List Slot)
    (name : String) (keyTy valueTy : Ty)
    (keyExpr : Expr keyTy) (valueExpr : Expr valueTy)
    (keyAdmission : ScalarExpression keyExpr) (valueAdmission : ScalarExpression valueExpr)
    (sourceAfter : SourceEffects.Frame) (before plan : Impact.Plan)
    (reads : List Cell)
    (sourceStep : SourceEffects.step ctx
      (.writeMap name keyTy valueTy keyExpr valueExpr)
      (sourceEnv, current) = .ok sourceAfter)
    (candidateKeyAgreement : keyExpr.eval ctx candidateEnv =
      keyExpr.eval ctx sourceEnv)
    (candidateValueAgreement : valueExpr.eval ctx candidateEnv =
      valueExpr.eval ctx sourceEnv)
    (sourceDeclaration : StateDecl)
    (declared : state.find? (·.name == name) = some sourceDeclaration)
    (named : sourceDeclaration.name = name)
    (kind : sourceDeclaration.kind = .map keyTy valueTy)
    (compiled : Impact.appendEffectWithActivity state
      (.writeMap name keyTy valueTy keyExpr valueExpr) none before = .ok plan)
    (encoded : encodeState state current = some slots)
    (distinct : state.Pairwise (fun left right => left.name ≠ right.name))
    (stateBound : state.length < Field.modulus)
    (modulus : ctx.modulus = Field.modulus) :
    ∃ slot key value nextSlots,
      state.findIdx? (·.name == name) = some slot ∧
      (plan.operations.drop before.operations.length).mapM
        (GenericStateOps.evalOp ctx candidateEnv) =
        .ok (GenericStateVM.writeMapOps slot
          (scalar (number keyTy key)) (scalar (number valueTy value))) ∧
      encodeState state sourceAfter.2 = some nextSlots ∧
      run (GenericStateVM.writeMapOps slot
        (scalar (number keyTy key)) (scalar (number valueTy value)))
        ⟨[.vector slots], reads⟩ =
        some ⟨[.vector nextSlots], reads⟩ ∧
      sourceAfter.1 = sourceEnv := by
  obtain ⟨key, value, _, sourceKey, sourceValue,
    canonicalKey, canonicalValue, _, _⟩ :=
    GenericStateWriteSourceTrace.writeMap_step_values ctx sourceEnv current
      name keyTy valueTy keyExpr valueExpr sourceAfter keyAdmission valueAdmission modulus sourceStep
  have candidateKey : keyExpr.eval ctx candidateEnv = .ok key := by
    rw [candidateKeyAgreement]
    exact sourceKey
  have candidateValue : valueExpr.eval ctx candidateEnv = .ok value := by
    rw [candidateValueAgreement]
    exact sourceValue
  obtain ⟨base, compiledBase, appended⟩ :=
    GuardedEffectPrefix.appendEffectWithActivity_unguarded_writeMap_chunk
      state name keyTy valueTy keyExpr valueExpr before plan compiled
  obtain ⟨slot, located, segmentEval⟩ :=
    GenericStateWriteEvaluation.writeMap_candidate_eval state name keyTy valueTy
      keyExpr valueExpr base ctx candidateEnv key value compiledBase modulus
      candidateKey candidateValue canonicalKey canonicalValue
  have declarationAt : state[slot]? = some sourceDeclaration := by
    rw [List.find?_eq_bind_findIdx?_getElem?, located] at declared
    exact declared
  obtain ⟨next, encodedEntries, sourceAgain, encodedNext, nativeRun⟩ :=
    GenericStateSchemaSpans.writeMap_source_step ctx sourceEnv state current
      slots slot sourceDeclaration name keyTy valueTy keyExpr valueExpr key value
      reads declarationAt named kind distinct encoded stateBound sourceKey
      sourceValue canonicalKey canonicalValue
  have sameFrame : sourceAfter = (sourceEnv, next) := by
    rw [sourceStep] at sourceAgain
    exact Except.ok.inj sourceAgain
  refine ⟨slot, key, value,
    slots.set slot (.map ((scalar (number keyTy key),
      scalar (number valueTy value)) ::
      encodedEntries.filter (fun pair => pair.1 != scalar (number keyTy key)))),
    located, (by simpa [appended] using segmentEval), ?_, nativeRun, ?_⟩
  · rw [sameFrame]
    exact encodedNext
  · rw [sameFrame]

end Noctium.Verification.GenericStateConverseWrite
