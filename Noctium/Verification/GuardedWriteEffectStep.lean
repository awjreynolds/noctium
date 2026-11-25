import Noctium.Verification.GenericStateEffectValidation
import Noctium.Verification.GenericStatePrefixEnvironment
import Noctium.Verification.GuardedWriteAuthentication

namespace Noctium.Verification.GuardedWriteEffectStep

open Backend NativeState NativeRelation ScalarNormalization
open GenericStatePrefixEnvironment GenericStateEffectValidation

private theorem declaration_name (state : List StateDecl) (name : String)
    (declaration : StateDecl) (found : state.find? (·.name == name) = some declaration) :
    declaration.name = name :=
  beq_iff_eq.mp (List.find?_some (p := fun item : StateDecl => item.name == name) found)

/-- A validated active Cell write agrees across the source effect runner and
the checked native suffix, with the source environment and read tape unchanged. -/
theorem checked_active_writeCell_step (ctx : EvalContext) (state : List StateDecl)
    (types nextTypes : TypeEnv) (sourceEnv complete : EvalEnv)
    (current : LedgerState) (slots : List NativeState.Slot)
    (reads : List NativeState.Cell) (name : String) (ty : Ty)
    (expression : Expr ty) (guard : Expr .bool)
    (validated : EffectValidation state types (.writeCell name ty expression) nextTypes)
    (admission : ScalarExpression expression)
    (agrees : AgreesOnTypes types sourceEnv complete)
    (active : guard.eval ctx sourceEnv = .ok true)
    (guardAgreement : guard.eval ctx sourceEnv = guard.eval ctx complete)
    (before plan : Impact.Plan) (segment : List NativeState.Op)
    (after : NativeState.Machine)
    (compiled : Impact.appendEffectWithActivity state
      (.writeCell name ty expression) (some guard) before = .ok plan)
    (evaluated : (plan.operations.drop before.operations.length).mapM
      (GenericStateOps.evalOp ctx complete) = .ok segment)
    (checked : NativeState.run segment ⟨[.vector slots], reads⟩ = some after)
    (encoded : GenericStateEncoding.encodeState state current = some slots)
    (distinct : state.Pairwise (fun left right => left.name ≠ right.name))
    (stateBound : state.length < Field.modulus)
    (modulus : ctx.modulus = Field.modulus) :
    ∃ nextEnv nextState nextSlots nextReads,
      runEffectsWithGuardsAndEnv ctx [.writeCell name ty expression] [some guard]
        sourceEnv current = .ok (nextEnv, nextState) ∧
      GenericStateEncoding.encodeState state nextState = some nextSlots ∧
      after = ⟨[.vector nextSlots], nextReads⟩ ∧
      AgreesOnTypes nextTypes nextEnv complete ∧
      nextEnv = sourceEnv ∧ nextReads = reads := by
  cases validated with
  | @writeCell name ty expression declared valueValid =>
    obtain ⟨sourceDeclaration, sourceFound, sourceKind⟩ := declared
    have sourceNamed := declaration_name state name sourceDeclaration sourceFound
    have valueAgreement := eval_scoped types sourceEnv complete agrees ctx
      stateEffectCaps expression valueValid
    obtain ⟨nextState, nextSlots, sourceStep, nextEncoded, nativeState⟩ :=
      GuardedWriteAuthentication.active_writeCell_candidate_source_step
        ctx sourceEnv complete state guard active guardAgreement current slots
        name ty expression admission valueAgreement before plan segment reads after
        compiled sourceDeclaration sourceFound sourceNamed sourceKind distinct encoded
        stateBound modulus evaluated checked
    exact ⟨sourceEnv, nextState, nextSlots, reads, sourceStep, nextEncoded,
      nativeState, agrees, rfl, rfl⟩

/-- A validated active Map write agrees across the source effect runner and
the checked native suffix, with the source environment and read tape unchanged. -/
theorem checked_active_writeMap_step (ctx : EvalContext) (state : List StateDecl)
    (types nextTypes : TypeEnv) (sourceEnv complete : EvalEnv)
    (current : LedgerState) (slots : List NativeState.Slot)
    (reads : List NativeState.Cell) (name : String)
    (keyTy valueTy : Ty) (key : Expr keyTy) (value : Expr valueTy)
    (guard : Expr .bool)
    (validated : EffectValidation state types
      (.writeMap name keyTy valueTy key value) nextTypes)
    (keyAdmission : ScalarExpression key) (valueAdmission : ScalarExpression value)
    (agrees : AgreesOnTypes types sourceEnv complete)
    (active : guard.eval ctx sourceEnv = .ok true)
    (guardAgreement : guard.eval ctx sourceEnv = guard.eval ctx complete)
    (before plan : Impact.Plan) (segment : List NativeState.Op)
    (after : NativeState.Machine)
    (compiled : Impact.appendEffectWithActivity state
      (.writeMap name keyTy valueTy key value) (some guard) before = .ok plan)
    (evaluated : (plan.operations.drop before.operations.length).mapM
      (GenericStateOps.evalOp ctx complete) = .ok segment)
    (checked : NativeState.run segment ⟨[.vector slots], reads⟩ = some after)
    (encoded : GenericStateEncoding.encodeState state current = some slots)
    (distinct : state.Pairwise (fun left right => left.name ≠ right.name))
    (stateBound : state.length < Field.modulus)
    (modulus : ctx.modulus = Field.modulus) :
    ∃ nextEnv nextState nextSlots nextReads,
      runEffectsWithGuardsAndEnv ctx [.writeMap name keyTy valueTy key value] [some guard]
        sourceEnv current = .ok (nextEnv, nextState) ∧
      GenericStateEncoding.encodeState state nextState = some nextSlots ∧
      after = ⟨[.vector nextSlots], nextReads⟩ ∧
      AgreesOnTypes nextTypes nextEnv complete ∧
      nextEnv = sourceEnv ∧ nextReads = reads := by
  cases validated with
  | @writeMap name keyTy valueTy key value declared keyValid valueValid =>
    obtain ⟨sourceDeclaration, sourceFound, sourceKind⟩ := declared
    have sourceNamed := declaration_name state name sourceDeclaration sourceFound
    have keyAgreement := eval_scoped types sourceEnv complete agrees ctx
      stateEffectCaps key keyValid
    have valueAgreement := eval_scoped types sourceEnv complete agrees ctx
      stateEffectCaps value valueValid
    obtain ⟨nextState, nextSlots, sourceStep, nextEncoded, nativeState⟩ :=
      GuardedWriteAuthentication.active_writeMap_candidate_source_step
        ctx sourceEnv complete state guard active guardAgreement current slots
        name keyTy valueTy key value keyAdmission valueAdmission keyAgreement valueAgreement
        before plan segment reads after compiled sourceDeclaration sourceFound sourceNamed
        sourceKind distinct encoded stateBound modulus evaluated checked
    exact ⟨sourceEnv, nextState, nextSlots, reads, sourceStep, nextEncoded,
      nativeState, agrees, rfl, rfl⟩

end Noctium.Verification.GuardedWriteEffectStep
