import Noctium.Verification.GenericStateConverseWrite
import Noctium.Verification.GenericStateWriteAuthentication
import Noctium.Verification.GuardedWriteLowering
import Noctium.Verification.GuardedWriteSourceStep

namespace Noctium.Verification.GuardedWriteAuthentication
open Backend NativeRelation NativeState ScalarNormalization GenericStateEncoding

/-- A checked active Cell write uses the source value and the exact
emitted suffix to determine the next source and native states. -/
theorem active_writeCell_candidate_source_step (ctx : EvalContext)
    (sourceEnv candidateEnv : EvalEnv) (state : List StateDecl)
    (guard : Expr .bool) (active : guard.eval ctx sourceEnv = .ok true)
    (guardAgreement : guard.eval ctx sourceEnv = guard.eval ctx candidateEnv)
    (current : LedgerState) (slots : List NativeState.Slot)
    (name : String) (ty : Ty) (expression : Expr ty)
    (admission : ScalarExpression expression)
    (agreement : expression.eval ctx sourceEnv = expression.eval ctx candidateEnv)
    (before plan : Impact.Plan) (segment : List NativeState.Op)
    (reads : List NativeState.Cell) (after : NativeState.Machine)
    (compiled : Impact.appendEffectWithActivity state (.writeCell name ty expression)
      (some guard) before = .ok plan)
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
      runEffectsWithGuardsAndEnv ctx [.writeCell name ty expression] [some guard] sourceEnv current =
        .ok (sourceEnv, next) ∧
      GenericStateEncoding.encodeState state next = some nextSlots ∧
      after = ⟨[.vector nextSlots], reads⟩ := by
  obtain ⟨emittedValue, valueEval, raw, appended, sameOps⟩ :=
    GuardedWriteLowering.active_writeCell_chunk ctx candidateEnv state name ty expression
      admission guard before plan (guardAgreement.symm.trans active) modulus compiled
  rw [sameOps] at evaluated
  rw [GuardedWriteSourceStep.run_active_writeCell ctx sourceEnv current name expression guard active]
  exact GenericStateWriteAuthentication.writeCell_chunk_source_step
    ctx sourceEnv candidateEnv state current slots name ty expression emittedValue
    admission (agreement.trans valueEval.symm) before raw segment reads after appended
    sourceDeclaration sourceFound sourceNamed sourceKind distinct encoded stateBound modulus evaluated checked

/-- A successful active source Cell write determines the emitted native
suffix and the encoding of the same successor state. -/
theorem source_active_writeCell_emitted (ctx : EvalContext)
    (sourceEnv candidateEnv : EvalEnv) (state : List StateDecl)
    (guard : Expr .bool) (active : guard.eval ctx sourceEnv = .ok true)
    (guardAgreement : guard.eval ctx sourceEnv = guard.eval ctx candidateEnv)
    (current : LedgerState) (slots : List Slot)
    (name : String) (ty : Ty) (expression : Expr ty)
    (admission : ScalarExpression expression)
    (sourceAfter : SourceEffects.Frame) (before plan : Impact.Plan)
    (reads : List Cell)
    (sourceStep : runEffectsWithGuardsAndEnv ctx [.writeCell name ty expression]
      [some guard] sourceEnv current = .ok sourceAfter)
    (candidateAgreement : expression.eval ctx candidateEnv =
      expression.eval ctx sourceEnv)
    (sourceDeclaration : StateDecl)
    (declared : state.find? (·.name == name) = some sourceDeclaration)
    (named : sourceDeclaration.name = name)
    (kind : sourceDeclaration.kind = .cell ty)
    (compiled : Impact.appendEffectWithActivity state (.writeCell name ty expression)
      (some guard) before = .ok plan)
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
  obtain ⟨emittedValue, valueEval, raw, appended, sameOps⟩ :=
    GuardedWriteLowering.active_writeCell_chunk ctx candidateEnv state name ty expression
      admission guard before plan (guardAgreement.symm.trans active) modulus compiled
  rw [sameOps]
  rw [GuardedWriteSourceStep.run_active_writeCell ctx sourceEnv current name expression guard active]
    at sourceStep
  exact GenericStateConverseWrite.source_writeCell_chunk
    ctx sourceEnv candidateEnv state current slots name ty expression emittedValue
    admission sourceAfter before raw reads sourceStep (valueEval.trans candidateAgreement)
    sourceDeclaration declared named kind appended encoded distinct stateBound modulus

/-- A checked active Map write uses the source value and the exact
emitted suffix to determine the next source and native states. -/
theorem active_writeMap_candidate_source_step (ctx : EvalContext)
    (sourceEnv candidateEnv : EvalEnv) (state : List StateDecl)
    (guard : Expr .bool) (active : guard.eval ctx sourceEnv = .ok true)
    (guardAgreement : guard.eval ctx sourceEnv = guard.eval ctx candidateEnv)
    (current : LedgerState) (slots : List NativeState.Slot)
    (name : String) (keyTy valueTy : Ty)
    (keyExpr : Expr keyTy) (valueExpr : Expr valueTy)
    (keyAdmission : ScalarExpression keyExpr) (valueAdmission : ScalarExpression valueExpr)
    (keyAgreement : keyExpr.eval ctx sourceEnv = keyExpr.eval ctx candidateEnv)
    (valueAgreement : valueExpr.eval ctx sourceEnv = valueExpr.eval ctx candidateEnv)
    (before plan : Impact.Plan) (segment : List NativeState.Op)
    (reads : List NativeState.Cell) (after : NativeState.Machine)
    (compiled : Impact.appendEffectWithActivity state
      (.writeMap name keyTy valueTy keyExpr valueExpr) (some guard) before = .ok plan)
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
      runEffectsWithGuardsAndEnv ctx [.writeMap name keyTy valueTy keyExpr valueExpr]
        [some guard] sourceEnv current =
        .ok (sourceEnv, next) ∧
      GenericStateEncoding.encodeState state next = some nextSlots ∧
      after = ⟨[.vector nextSlots], reads⟩ := by
  obtain ⟨emittedKey, emittedValue, keyEval, valueEval, raw, appended, sameOps⟩ :=
    GuardedWriteLowering.active_writeMap_chunk ctx candidateEnv state name keyTy valueTy keyExpr valueExpr
      keyAdmission valueAdmission guard before plan (guardAgreement.symm.trans active) modulus compiled
  rw [sameOps] at evaluated
  rw [GuardedWriteSourceStep.run_active_writeMap ctx sourceEnv current name keyExpr valueExpr guard active]
  exact GenericStateWriteAuthentication.writeMap_chunk_source_step
    ctx sourceEnv candidateEnv state current slots name keyTy valueTy keyExpr emittedKey valueExpr emittedValue
    keyAdmission valueAdmission (keyAgreement.trans keyEval.symm) (valueAgreement.trans valueEval.symm) before raw segment reads after appended
    sourceDeclaration sourceFound sourceNamed sourceKind distinct encoded stateBound modulus evaluated checked

/-- A successful active source Map write determines the emitted native
suffix and the encoding of the same successor state. -/
theorem source_active_writeMap_emitted (ctx : EvalContext)
    (sourceEnv candidateEnv : EvalEnv) (state : List StateDecl)
    (guard : Expr .bool) (active : guard.eval ctx sourceEnv = .ok true)
    (guardAgreement : guard.eval ctx sourceEnv = guard.eval ctx candidateEnv)
    (current : LedgerState) (slots : List Slot)
    (name : String) (keyTy valueTy : Ty)
    (keyExpr : Expr keyTy) (valueExpr : Expr valueTy)
    (keyAdmission : ScalarExpression keyExpr) (valueAdmission : ScalarExpression valueExpr)
    (sourceAfter : SourceEffects.Frame) (before plan : Impact.Plan)
    (reads : List Cell)
    (sourceStep : runEffectsWithGuardsAndEnv ctx [.writeMap name keyTy valueTy keyExpr valueExpr]
      [some guard] sourceEnv current = .ok sourceAfter)
    (candidateKeyAgreement : keyExpr.eval ctx candidateEnv =
      keyExpr.eval ctx sourceEnv)
    (candidateValueAgreement : valueExpr.eval ctx candidateEnv =
      valueExpr.eval ctx sourceEnv)
    (sourceDeclaration : StateDecl)
    (declared : state.find? (·.name == name) = some sourceDeclaration)
    (named : sourceDeclaration.name = name)
    (kind : sourceDeclaration.kind = .map keyTy valueTy)
    (compiled : Impact.appendEffectWithActivity state
      (.writeMap name keyTy valueTy keyExpr valueExpr) (some guard) before = .ok plan)
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
  obtain ⟨emittedKey, emittedValue, keyEval, valueEval, raw, appended, sameOps⟩ :=
    GuardedWriteLowering.active_writeMap_chunk ctx candidateEnv state name keyTy valueTy keyExpr valueExpr
      keyAdmission valueAdmission guard before plan (guardAgreement.symm.trans active) modulus compiled
  rw [sameOps]
  rw [GuardedWriteSourceStep.run_active_writeMap ctx sourceEnv current name keyExpr valueExpr guard active]
    at sourceStep
  exact GenericStateConverseWrite.source_writeMap_chunk
    ctx sourceEnv candidateEnv state current slots name keyTy valueTy keyExpr emittedKey valueExpr emittedValue
    keyAdmission valueAdmission sourceAfter before raw reads sourceStep (keyEval.trans candidateKeyAgreement) (valueEval.trans candidateValueAgreement)
    sourceDeclaration declared named kind appended encoded distinct stateBound modulus

end Noctium.Verification.GuardedWriteAuthentication
