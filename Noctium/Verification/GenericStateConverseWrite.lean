import Noctium.Verification.GenericStateSchemaSpans
import Noctium.Verification.GenericStateWriteSourceTrace
import Noctium.Verification.GenericStateWriteEvaluation
import Noctium.Verification.GuardedEffectPrefix
import Noctium.Verification.GuardedSourceEffects
import Noctium.Verification.GuardedWriteSourceStep
import Noctium.Verification.GuardedPlanExecution
import Noctium.Verification.GuardedWriteLowering

namespace Noctium.Verification.GenericStateConverseWrite
open Backend NativeRelation ScalarNormalization NativeState GenericStateEncoding

/-- The exact appended Cell write agrees with the source when the emitted expressions
have the original evaluation. -/
theorem source_writeCell_chunk (ctx : EvalContext)
    (sourceEnv candidateEnv : EvalEnv) (state : List StateDecl)
    (current : LedgerState) (slots : List Slot)
    (name : String) (ty : Ty) (expression emittedValue : Expr ty)
    (admission : ScalarExpression expression)
    (sourceAfter : SourceEffects.Frame) (before plan : Impact.Plan)
    (reads : List Cell)
    (sourceStep : SourceEffects.step ctx (.writeCell name ty expression)
      (sourceEnv, current) = .ok sourceAfter)
    (candidateAgreement : emittedValue.eval ctx candidateEnv =
      expression.eval ctx sourceEnv)
    (sourceDeclaration : StateDecl)
    (declared : state.find? (·.name == name) = some sourceDeclaration)
    (named : sourceDeclaration.name = name)
    (kind : sourceDeclaration.kind = .cell ty)
    (compiled : Impact.appendEffect state (.writeCell name ty emittedValue)
      before = .ok plan)
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
  have candidateEval : emittedValue.eval ctx candidateEnv = .ok value := by
    rw [candidateAgreement]
    exact sourceEval
  obtain ⟨base, compiledBase, appended⟩ :=
    GuardedEffectPrefix.appendEffect_writeCell_chunk
      state name ty emittedValue before plan compiled
  have alignment := GenericStateSchemaSpans.encoded_named_cell_alignment_none
    state current slots name sourceDeclaration ty declared kind encoded
  have cellDecl : Impact.UnalignedCellDeclaration state name ty :=
    ⟨sourceDeclaration, declared, kind, alignment⟩
  obtain ⟨slot, located, segmentEval⟩ :=
    GenericStateWriteEvaluation.writeCell_candidate_eval state name ty
      emittedValue base ctx candidateEnv value compiledBase cellDecl stateBound modulus
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
  obtain ⟨raw, appended, sameOps, _⟩ := GuardedEffectPrefix.appendEffectWithActivity_none_result
    state (.writeCell name ty expression) before plan compiled
  rw [sameOps]
  exact source_writeCell_chunk ctx sourceEnv candidateEnv state current slots name ty
    expression expression admission sourceAfter before raw reads sourceStep candidateAgreement
    sourceDeclaration declared named kind appended encoded distinct stateBound modulus

/-- The exact appended Map write agrees with the source when the emitted expressions
have the original evaluation. -/
theorem source_writeMap_chunk (ctx : EvalContext)
    (sourceEnv candidateEnv : EvalEnv) (state : List StateDecl)
    (current : LedgerState) (slots : List Slot)
    (name : String) (keyTy valueTy : Ty)
    (keyExpr emittedKey : Expr keyTy) (valueExpr emittedValue : Expr valueTy)
    (keyAdmission : ScalarExpression keyExpr) (valueAdmission : ScalarExpression valueExpr)
    (sourceAfter : SourceEffects.Frame) (before plan : Impact.Plan)
    (reads : List Cell)
    (sourceStep : SourceEffects.step ctx
      (.writeMap name keyTy valueTy keyExpr valueExpr)
      (sourceEnv, current) = .ok sourceAfter)
    (candidateKeyAgreement : emittedKey.eval ctx candidateEnv =
      keyExpr.eval ctx sourceEnv)
    (candidateValueAgreement : emittedValue.eval ctx candidateEnv =
      valueExpr.eval ctx sourceEnv)
    (sourceDeclaration : StateDecl)
    (declared : state.find? (·.name == name) = some sourceDeclaration)
    (named : sourceDeclaration.name = name)
    (kind : sourceDeclaration.kind = .map keyTy valueTy)
    (compiled : Impact.appendEffect state
      (.writeMap name keyTy valueTy emittedKey emittedValue) before = .ok plan)
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
  have candidateKey : emittedKey.eval ctx candidateEnv = .ok key := by
    rw [candidateKeyAgreement]
    exact sourceKey
  have candidateValue : emittedValue.eval ctx candidateEnv = .ok value := by
    rw [candidateValueAgreement]
    exact sourceValue
  obtain ⟨base, compiledBase, appended⟩ :=
    GuardedEffectPrefix.appendEffect_writeMap_chunk
      state name keyTy valueTy emittedKey emittedValue before plan compiled
  obtain ⟨slot, located, segmentEval⟩ :=
    GenericStateWriteEvaluation.writeMap_candidate_eval state name keyTy valueTy
      emittedKey emittedValue base ctx candidateEnv key value compiledBase modulus
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
  obtain ⟨raw, appended, sameOps, _⟩ := GuardedEffectPrefix.appendEffectWithActivity_none_result
    state (.writeMap name keyTy valueTy keyExpr valueExpr) before plan compiled
  rw [sameOps]
  exact source_writeMap_chunk ctx sourceEnv candidateEnv state current slots name keyTy valueTy
    keyExpr keyExpr valueExpr valueExpr keyAdmission valueAdmission sourceAfter before raw reads
    sourceStep candidateKeyAgreement candidateValueAgreement sourceDeclaration declared named kind
    appended encoded distinct stateBound modulus

private theorem guarded_write_encoded (ctx : EvalContext) (declarations : List StateDecl)
    (guard : Option (Expr .bool)) (effect : Effect) (before after : SourceEffects.Frame)
    (slots : List Slot) (encoded : encodeState declarations before.2 = some slots)
    (supported : ∀ condition,
      GenericStateCheckedReadTrace.GuardedScalarReadEffect (some condition) effect)
    (active : ∀ condition, condition.eval ctx before.1 = .ok true →
      GuardedSourceEffects.step ctx (some condition) effect before = SourceEffects.step ctx effect before)
    (inactive : ∀ condition, condition.eval ctx before.1 = .ok false →
      GuardedSourceEffects.step ctx (some condition) effect before = .ok before)
    (ordinary : SourceEffects.step ctx effect before = .ok after →
      ∃ nextSlots, encodeState declarations after.2 = some nextSlots)
    (success : GuardedSourceEffects.step ctx guard effect before = .ok after) :
    ∃ nextSlots, encodeState declarations after.2 = some nextSlots := by
  cases guard with
  | none => exact ordinary ((GuardedSourceEffects.step_unguarded ctx effect before).symm.trans success)
  | some condition =>
    cases evaluated : condition.eval ctx before.1 with
    | error message =>
      rw [GuardedSourceEffects.step_guard_error ctx condition effect before message
        (supported condition) evaluated] at success
      cases success
    | ok selected =>
      cases selected with
      | false =>
        have same := Except.ok.inj ((inactive condition evaluated).symm.trans success)
        rw [← same]
        exact ⟨slots, encoded⟩
      | true => exact ordinary ((active condition evaluated).symm.trans success)

/-- Every successful admitted guarded Cell write preserves encodability of
its actual source successor. -/
theorem guarded_source_writeCell_encoded (ctx : EvalContext) (declarations : List StateDecl)
    (env : EvalEnv) (current : LedgerState) (after : SourceEffects.Frame)
    (name : String) (ty : Ty) (expression : Expr ty) (guard : Option (Expr .bool))
    (slots : List Slot) (encoded : encodeState declarations current = some slots)
    (declaration : StateDecl) (declared : declarations.find? (·.name == name) = some declaration)
    (kind : declaration.kind = .cell ty)
    (distinct : declarations.Pairwise (fun left right => left.name ≠ right.name))
    (slotBound : declarations.length < Field.modulus)
    (admitted : ScalarExpression expression) (modulus : ctx.modulus = Field.modulus)
    (success : GuardedSourceEffects.step ctx guard (.writeCell name ty expression)
      (env, current) = .ok after) :
    ∃ nextSlots, encodeState declarations after.2 = some nextSlots := by
  apply guarded_write_encoded ctx declarations guard (.writeCell name ty expression)
    (env, current) after slots encoded _ _ _ _ success
  · intro condition
    exact .writeCell condition name ty expression
  · intro condition selected
    exact GuardedWriteSourceStep.run_active_writeCell ctx env current name expression condition selected
  · intro condition selected
    exact GuardedWriteSourceStep.run_inactive_writeCell ctx env current name expression condition selected
  · intro actual
    obtain ⟨_, value, _, evaluated, canonical, _⟩ :=
      GenericStateWriteSourceTrace.writeCell_step_value ctx env current name ty expression
        after admitted modulus actual
    obtain ⟨slot, _, indexed⟩ := GenericStateSchemaSpans.find_declaration_slot
      declarations name declaration declared
    have named := beq_iff_eq.mp (List.find?_some (p := fun item : StateDecl => item.name == name) declared)
    obtain ⟨next, modeled, nextEncoded, _⟩ := GenericStateSchemaSpans.writeCell_source_step
      ctx env declarations current slots slot declaration name ty expression value []
      indexed named kind distinct encoded slotBound evaluated canonical
    have same := Except.ok.inj (modeled.symm.trans actual)
    rw [← same]
    exact ⟨_, nextEncoded⟩

/-- Every successful admitted guarded Map write preserves encodability of
its actual source successor, including a replacement at an existing key. -/
theorem guarded_source_writeMap_encoded (ctx : EvalContext) (declarations : List StateDecl)
    (env : EvalEnv) (current : LedgerState) (after : SourceEffects.Frame)
    (name : String) (keyTy valueTy : Ty) (key : Expr keyTy) (value : Expr valueTy)
    (guard : Option (Expr .bool)) (slots : List Slot)
    (encoded : encodeState declarations current = some slots)
    (declaration : StateDecl) (declared : declarations.find? (·.name == name) = some declaration)
    (kind : declaration.kind = .map keyTy valueTy)
    (distinct : declarations.Pairwise (fun left right => left.name ≠ right.name))
    (slotBound : declarations.length < Field.modulus)
    (keyAdmitted : ScalarExpression key) (valueAdmitted : ScalarExpression value)
    (modulus : ctx.modulus = Field.modulus)
    (success : GuardedSourceEffects.step ctx guard (.writeMap name keyTy valueTy key value)
      (env, current) = .ok after) :
    ∃ nextSlots, encodeState declarations after.2 = some nextSlots := by
  apply guarded_write_encoded ctx declarations guard (.writeMap name keyTy valueTy key value)
    (env, current) after slots encoded _ _ _ _ success
  · intro condition
    exact .writeMap condition name keyTy valueTy key value
  · intro condition selected
    exact GuardedWriteSourceStep.run_active_writeMap ctx env current name key value condition selected
  · intro condition selected
    exact GuardedWriteSourceStep.run_inactive_writeMap ctx env current name key value condition selected
  · intro actual
    obtain ⟨resolved, evaluated, _, keyEval, valueEval, keyCanonical, valueCanonical, _, _⟩ :=
      GenericStateWriteSourceTrace.writeMap_step_values ctx env current name keyTy valueTy key value
        after keyAdmitted valueAdmitted modulus actual
    obtain ⟨slot, _, indexed⟩ := GenericStateSchemaSpans.find_declaration_slot
      declarations name declaration declared
    have named := beq_iff_eq.mp (List.find?_some (p := fun item : StateDecl => item.name == name) declared)
    obtain ⟨next, _, modeled, nextEncoded, _⟩ := GenericStateSchemaSpans.writeMap_source_step
      ctx env declarations current slots slot declaration name keyTy valueTy key value
      resolved evaluated [] indexed named kind distinct encoded slotBound keyEval valueEval
      keyCanonical valueCanonical
    have same := Except.ok.inj (modeled.symm.trans actual)
    rw [← same]
    exact ⟨_, nextEncoded⟩

/-- A successful guarded Cell write determines the actual emitted chunk and
the same encoded VM successor. A false guard skips operand evaluation. -/
theorem guarded_source_writeCell_converse (ctx : EvalContext)
    (sourceEnv candidateEnv : EvalEnv) (state : List StateDecl)
    (guard : Option (Expr .bool)) (current : LedgerState) (slots : List Slot)
    (name : String) (ty : Ty) (expression : Expr ty)
    (admission : ScalarExpression expression)
    (sourceAfter : SourceEffects.Frame) (before afterPlan : Impact.Plan)
    (reads : List Cell)
    (sourceStep : GuardedSourceEffects.step ctx guard (.writeCell name ty expression)
      (sourceEnv, current) = .ok sourceAfter)
    (guardAgreement : ∀ condition, guard = some condition →
      condition.eval ctx sourceEnv = condition.eval ctx candidateEnv)
    (candidateAgreement : expression.eval ctx candidateEnv =
      expression.eval ctx sourceEnv)
    (sourceDeclaration : StateDecl)
    (declared : state.find? (·.name == name) = some sourceDeclaration)
    (named : sourceDeclaration.name = name)
    (kind : sourceDeclaration.kind = .cell ty)
    (compiled : Impact.appendEffectWithActivity state
      (.writeCell name ty expression) guard before = .ok afterPlan)
    (encoded : encodeState state current = some slots)
    (distinct : state.Pairwise (fun left right => left.name ≠ right.name))
    (stateBound : state.length < Field.modulus)
    (modulus : ctx.modulus = Field.modulus) :
    ∃ activity segment nextSlots,
      GuardedPlanExecution.evalChunk ctx candidateEnv guard
        (afterPlan.operations.drop before.operations.length) = .ok (activity, segment) ∧
      run segment ⟨[.vector slots], reads⟩ =
        some ⟨[.vector nextSlots], reads⟩ ∧
      encodeState state sourceAfter.2 = some nextSlots ∧
      sourceAfter.1 = sourceEnv := by
  cases guard with
  | none =>
      have unguarded : SourceEffects.step ctx (.writeCell name ty expression)
          (sourceEnv, current) = .ok sourceAfter := by
        rw [GuardedSourceEffects.step_unguarded] at sourceStep
        exact sourceStep
      obtain ⟨slot, value, nextSlots, _, evaluated, encodedNext, nativeRun, frame⟩ :=
        source_writeCell_native ctx sourceEnv candidateEnv state current slots name ty
          expression admission sourceAfter before afterPlan reads unguarded
          candidateAgreement sourceDeclaration declared named kind compiled encoded distinct
          stateBound modulus
      refine ⟨none, GenericStateVM.writeCellOps slot
        (field (scalar (number ty value))), nextSlots, ?_, nativeRun, encodedNext, frame⟩
      have noGuard : (none : Option (Expr .bool)).mapM
          (fun condition => condition.eval ctx candidateEnv) = .ok none := rfl
      rw [GuardedPlanExecution.evalChunk, noGuard]
      rw [evaluated]
      rfl
  | some condition =>
      have guardSame := guardAgreement condition rfl
      cases evaluatedGuard : condition.eval ctx sourceEnv with
      | error message =>
          rw [GuardedSourceEffects.step_guard_error ctx condition
            (.writeCell name ty expression) (sourceEnv, current) message
            (.writeCell condition name ty expression) evaluatedGuard] at sourceStep
          cases sourceStep
      | ok selected =>
          cases selected with
          | false =>
              have candidateGuard : condition.eval ctx candidateEnv = .ok false := by
                rw [← guardSame]
                exact evaluatedGuard
              have sameFrame : sourceAfter = (sourceEnv, current) := by
                have skipped := GuardedWriteSourceStep.run_inactive_writeCell ctx
                  sourceEnv current name expression condition evaluatedGuard
                exact Except.ok.inj (sourceStep.symm.trans skipped)
              refine ⟨some false, [], slots, ?_, ?_, ?_, ?_⟩
              · have activityEval : (some condition).mapM
                    (fun condition => condition.eval ctx candidateEnv) = .ok (some false) := by
                  simp [candidateGuard] <;> rfl
                rw [GuardedPlanExecution.evalChunk, activityEval]
                rfl
              · rfl
              · simpa [sameFrame] using encoded
              · exact congrArg Prod.fst sameFrame
          | true =>
              have candidateGuard : condition.eval ctx candidateEnv = .ok true := by
                rw [← guardSame]
                exact evaluatedGuard
              have sourceActive := GuardedWriteSourceStep.run_active_writeCell
                ctx sourceEnv current name expression condition evaluatedGuard
              have unguarded : SourceEffects.step ctx (.writeCell name ty expression)
                  (sourceEnv, current) = .ok sourceAfter := by
                have guardedRun : runEffectsWithGuardsAndEnv ctx
                    [.writeCell name ty expression] [some condition] sourceEnv current =
                    .ok sourceAfter := by
                  simpa [GuardedSourceEffects.step] using sourceStep
                rw [sourceActive] at guardedRun
                exact guardedRun
              obtain ⟨emitted, emittedEval, raw, rawCompiled, sameOperations⟩ :=
                GuardedWriteLowering.active_writeCell_chunk ctx candidateEnv state name ty
                  expression admission condition before afterPlan candidateGuard modulus compiled
              obtain ⟨slot, value, nextSlots, _, evaluated, encodedNext, nativeRun, frame⟩ :=
                source_writeCell_chunk ctx sourceEnv candidateEnv state current slots name ty
                  expression emitted admission sourceAfter before raw reads unguarded
                  (emittedEval.trans candidateAgreement) sourceDeclaration declared named kind
                  rawCompiled encoded distinct stateBound modulus
              refine ⟨some true, GenericStateVM.writeCellOps slot
                (field (scalar (number ty value))), nextSlots, ?_, nativeRun, encodedNext, frame⟩
              have actualSuffix : afterPlan.operations.drop before.operations.length =
                  raw.operations.drop before.operations.length := by
                rw [sameOperations]
              have activityEval : (some condition).mapM
                  (fun condition => condition.eval ctx candidateEnv) = .ok (some true) := by
                simp [candidateGuard] <;> rfl
              rw [GuardedPlanExecution.evalChunk, activityEval]
              rw [actualSuffix, evaluated]
              rfl

/-- A successful guarded Map write determines the actual emitted chunk and
the same encoded VM successor. A false guard skips key and value evaluation. -/
theorem guarded_source_writeMap_converse (ctx : EvalContext)
    (sourceEnv candidateEnv : EvalEnv) (state : List StateDecl)
    (guard : Option (Expr .bool)) (current : LedgerState) (slots : List Slot)
    (name : String) (keyTy valueTy : Ty)
    (keyExpr : Expr keyTy) (valueExpr : Expr valueTy)
    (keyAdmission : ScalarExpression keyExpr) (valueAdmission : ScalarExpression valueExpr)
    (sourceAfter : SourceEffects.Frame) (before afterPlan : Impact.Plan)
    (reads : List Cell)
    (sourceStep : GuardedSourceEffects.step ctx guard
      (.writeMap name keyTy valueTy keyExpr valueExpr) (sourceEnv, current) = .ok sourceAfter)
    (guardAgreement : ∀ condition, guard = some condition →
      condition.eval ctx sourceEnv = condition.eval ctx candidateEnv)
    (candidateKeyAgreement : keyExpr.eval ctx candidateEnv = keyExpr.eval ctx sourceEnv)
    (candidateValueAgreement : valueExpr.eval ctx candidateEnv = valueExpr.eval ctx sourceEnv)
    (sourceDeclaration : StateDecl)
    (declared : state.find? (·.name == name) = some sourceDeclaration)
    (named : sourceDeclaration.name = name)
    (kind : sourceDeclaration.kind = .map keyTy valueTy)
    (compiled : Impact.appendEffectWithActivity state
      (.writeMap name keyTy valueTy keyExpr valueExpr) guard before = .ok afterPlan)
    (encoded : encodeState state current = some slots)
    (distinct : state.Pairwise (fun left right => left.name ≠ right.name))
    (stateBound : state.length < Field.modulus)
    (modulus : ctx.modulus = Field.modulus) :
    ∃ activity segment nextSlots,
      GuardedPlanExecution.evalChunk ctx candidateEnv guard
        (afterPlan.operations.drop before.operations.length) = .ok (activity, segment) ∧
      run segment ⟨[.vector slots], reads⟩ =
        some ⟨[.vector nextSlots], reads⟩ ∧
      encodeState state sourceAfter.2 = some nextSlots ∧
      sourceAfter.1 = sourceEnv := by
  cases guard with
  | none =>
      have unguarded : SourceEffects.step ctx
          (.writeMap name keyTy valueTy keyExpr valueExpr)
          (sourceEnv, current) = .ok sourceAfter := by
        rw [GuardedSourceEffects.step_unguarded] at sourceStep
        exact sourceStep
      obtain ⟨slot, key, value, nextSlots, _, evaluated, encodedNext, nativeRun, frame⟩ :=
        source_writeMap_native ctx sourceEnv candidateEnv state current slots name keyTy valueTy
          keyExpr valueExpr keyAdmission valueAdmission sourceAfter before afterPlan reads
          unguarded candidateKeyAgreement candidateValueAgreement sourceDeclaration declared
          named kind compiled encoded distinct stateBound modulus
      refine ⟨none, GenericStateVM.writeMapOps slot
        (scalar (number keyTy key)) (scalar (number valueTy value)), nextSlots,
        ?_, nativeRun, encodedNext, frame⟩
      have noGuard : (none : Option (Expr .bool)).mapM
          (fun condition => condition.eval ctx candidateEnv) = .ok none := rfl
      rw [GuardedPlanExecution.evalChunk, noGuard]
      rw [evaluated]
      rfl
  | some condition =>
      have guardSame := guardAgreement condition rfl
      cases evaluatedGuard : condition.eval ctx sourceEnv with
      | error message =>
          rw [GuardedSourceEffects.step_guard_error ctx condition
            (.writeMap name keyTy valueTy keyExpr valueExpr) (sourceEnv, current) message
            (.writeMap condition name keyTy valueTy keyExpr valueExpr) evaluatedGuard] at sourceStep
          cases sourceStep
      | ok selected =>
          cases selected with
          | false =>
              have candidateGuard : condition.eval ctx candidateEnv = .ok false := by
                rw [← guardSame]
                exact evaluatedGuard
              have sameFrame : sourceAfter = (sourceEnv, current) := by
                have skipped := GuardedWriteSourceStep.run_inactive_writeMap ctx
                  sourceEnv current name keyExpr valueExpr condition evaluatedGuard
                exact Except.ok.inj (sourceStep.symm.trans skipped)
              refine ⟨some false, [], slots, ?_, ?_, ?_, ?_⟩
              · have activityEval : (some condition).mapM
                    (fun condition => condition.eval ctx candidateEnv) = .ok (some false) := by
                  simp [candidateGuard] <;> rfl
                rw [GuardedPlanExecution.evalChunk, activityEval]
                rfl
              · rfl
              · simpa [sameFrame] using encoded
              · exact congrArg Prod.fst sameFrame
          | true =>
              have candidateGuard : condition.eval ctx candidateEnv = .ok true := by
                rw [← guardSame]
                exact evaluatedGuard
              have sourceActive := GuardedWriteSourceStep.run_active_writeMap
                ctx sourceEnv current name keyExpr valueExpr condition evaluatedGuard
              have unguarded : SourceEffects.step ctx
                  (.writeMap name keyTy valueTy keyExpr valueExpr)
                  (sourceEnv, current) = .ok sourceAfter := by
                have guardedRun : runEffectsWithGuardsAndEnv ctx
                    [.writeMap name keyTy valueTy keyExpr valueExpr] [some condition]
                    sourceEnv current = .ok sourceAfter := by
                  simpa [GuardedSourceEffects.step] using sourceStep
                rw [sourceActive] at guardedRun
                exact guardedRun
              obtain ⟨emittedKey, emittedValue, keyEval, valueEval, raw, rawCompiled,
                sameOperations⟩ := GuardedWriteLowering.active_writeMap_chunk
                  ctx candidateEnv state name keyTy valueTy keyExpr valueExpr keyAdmission
                  valueAdmission condition before afterPlan candidateGuard modulus compiled
              obtain ⟨slot, key, value, nextSlots, _, evaluated, encodedNext, nativeRun, frame⟩ :=
                source_writeMap_chunk ctx sourceEnv candidateEnv state current slots name keyTy
                  valueTy keyExpr emittedKey valueExpr emittedValue keyAdmission valueAdmission
                  sourceAfter before raw reads unguarded (keyEval.trans candidateKeyAgreement)
                  (valueEval.trans candidateValueAgreement) sourceDeclaration declared named kind
                  rawCompiled encoded distinct stateBound modulus
              refine ⟨some true, GenericStateVM.writeMapOps slot
                (scalar (number keyTy key)) (scalar (number valueTy value)), nextSlots,
                ?_, nativeRun, encodedNext, frame⟩
              have actualSuffix : afterPlan.operations.drop before.operations.length =
                  raw.operations.drop before.operations.length := by
                rw [sameOperations]
              have activityEval : (some condition).mapM
                  (fun condition => condition.eval ctx candidateEnv) = .ok (some true) := by
                simp [candidateGuard] <;> rfl
              rw [GuardedPlanExecution.evalChunk, activityEval]
              rw [actualSuffix, evaluated]
              rfl

end Noctium.Verification.GenericStateConverseWrite
