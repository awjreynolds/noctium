import Noctium.Verification.GenericStateConverseSource
import Noctium.Verification.GenericStateConverseAbsence
import Noctium.Verification.GenericStatePrefixEnvironment

namespace Noctium.Verification.GenericStateConverseEffectStep
open Backend NativeRelation ScalarNormalization NativeState
open GenericStatePrefixEnvironment GenericStateEffectValidation GenericStateCheckedReadTrace
open ScalarGuardedPlanAdmission (ScalarEffect)
open GenericStateConverseSource (ReadDestinationAgrees)

/-- A successful source effect drives the exact emitted operation suffix,
its native successor, and the environment for subsequent source effects. -/
theorem source_effect_native (ctx : EvalContext) (state : List StateDecl)
    (types nextTypes : TypeEnv) (effect : Effect) (guard : Option (Expr .bool))
    (sourceEnv complete : EvalEnv) (current : LedgerState)
    (sourceAfter : SourceEffects.Frame) (slots : List Slot) (reads : List Cell)
    (beforePlan afterPlan : Impact.Plan)
    (validated : EffectValidation state types effect nextTypes)
    (guardValid : ∀ condition, guard = some condition →
      condition.validate stateEffectCaps types = .ok ())
    (admitted : ScalarEffect state effect) (scope : GuardedScalarReadEffect guard effect)
    (sourceStep : GuardedSourceEffects.step ctx guard effect (sourceEnv, current) = .ok sourceAfter)
    (agrees : AgreesOnTypes types sourceEnv complete)
    (readCandidate : ReadDestinationAgrees effect sourceAfter complete)
    (compiled : Impact.appendEffectWithActivity state effect guard beforePlan = .ok afterPlan)
    (encoded : GenericStateEncoding.encodeState state current = some slots)
    (distinct : state.Pairwise (fun left right => left.name ≠ right.name))
    (stateBound : state.length < Field.modulus) (modulus : ctx.modulus = Field.modulus) :
    ∃ activity segment nextSlots nextReads,
      GuardedPlanExecution.evalChunk ctx complete guard
        (afterPlan.operations.drop beforePlan.operations.length) = .ok (activity, segment) ∧
      NativeState.run segment ⟨[.vector slots], reads⟩ = some ⟨[.vector nextSlots], nextReads⟩ ∧
      GenericStateEncoding.encodeState state sourceAfter.2 = some nextSlots ∧
      AgreesOnTypes nextTypes sourceAfter.1 complete := by
  have guardAgreement (condition : Expr .bool) (selected : guard = some condition) :
      condition.eval ctx sourceEnv = condition.eval ctx complete :=
    eval_scoped types sourceEnv complete agrees ctx stateEffectCaps condition
      (guardValid condition selected)
  cases validated with
  | @readCell name destination ty declared fresh =>
    cases admitted with
    | cell _ cell _ =>
      cases cell with
      | readCell _ _ _ supported _ =>
        obtain ⟨declaration, found, kind⟩ := declared
        have named := beq_iff_eq.mp (List.find?_some (p := fun item : StateDecl => item.name == name) found)
        obtain ⟨base, baseCompiled⟩ := GuardedEffectPrefix.appendEffectWithActivity_readCell_empty_plan
          state name destination ty guard beforePlan afterPlan compiled
        obtain ⟨value, activity, segment, evaluated, nativeRun, frame, _⟩ :=
          GenericStateConverseRead.guarded_scalarCell_read_emitted ctx sourceEnv complete state
            current slots reads name destination ty supported guard sourceAfter beforePlan afterPlan
            base declaration found named kind compiled baseCompiled encoded modulus sourceStep
            readCandidate guardAgreement
        change complete.lookup destination = sourceAfter.1.lookup destination at readCandidate
        have matched : complete.lookup destination = some (Value.pack ty value) := by
          rw [readCandidate, frame]
          simp
        exact ⟨activity, segment, slots, _, evaluated, nativeRun,
          by rw [frame]; exact encoded,
          by
            simpa [frame] using extend_read types sourceEnv complete destination ty
              (Value.pack ty value) agrees fresh matched⟩
  | @readMap name destination keyTy valueTy key declared keyValid fresh =>
    cases admitted with
    | cell _ cell _ => cases cell
    | readMap _ _ _ _ _ _ supported keyAdmitted =>
      obtain ⟨declaration, found, kind⟩ := declared
      have keyAgreement := eval_scoped types sourceEnv complete agrees ctx stateEffectCaps key keyValid
      obtain ⟨value, activity, segment, evaluated, nativeRun, frame, _⟩ :=
        GenericStateConverseRead.guarded_scalarMap_read_emitted ctx sourceEnv complete state
          current slots reads name destination keyTy valueTy key keyAdmitted supported guard
          sourceAfter beforePlan afterPlan declaration found kind compiled encoded modulus
          sourceStep readCandidate (fun _guardIsNone => keyAgreement.symm)
          (fun _condition _guardSelected _sourceGuardTrue => keyAgreement.symm) guardAgreement
      change complete.lookup destination = sourceAfter.1.lookup destination at readCandidate
      have matched : complete.lookup destination = some (Value.pack valueTy value) := by
        rw [readCandidate, frame]
        simp
      exact ⟨activity, segment, slots, _, evaluated, nativeRun,
        by rw [frame]; exact encoded,
        by
          simpa [frame] using extend_read types sourceEnv complete destination valueTy
            (Value.pack valueTy value) agrees fresh matched⟩
  | @require required _ =>
    obtain ⟨activity, evaluated, frame⟩ := GuardedRequireSemantics.source_guarded_require_chunk
      ctx state sourceEnv complete current sourceAfter required guard beforePlan afterPlan
      (fun condition selected => (guardAgreement condition selected).symm) compiled sourceStep
    subst sourceAfter
    exact ⟨activity, [], slots, reads, evaluated, rfl, encoded, agrees⟩
  | @writeCell name ty value declared valueValid =>
    cases admitted with
    | cell _ _ operand =>
      obtain ⟨declaration, found, kind⟩ := declared
      have named := beq_iff_eq.mp (List.find?_some (p := fun item : StateDecl => item.name == name) found)
      have valueAgreement := eval_scoped types sourceEnv complete agrees ctx stateEffectCaps value valueValid
      obtain ⟨activity, segment, nextSlots, evaluated, nativeRun, nextEncoded, frame⟩ :=
        GenericStateConverseWrite.guarded_source_writeCell_converse ctx sourceEnv complete state
          guard current slots name ty value operand sourceAfter beforePlan afterPlan reads
          sourceStep guardAgreement valueAgreement.symm declaration found named kind compiled
          encoded distinct stateBound modulus
      exact ⟨activity, segment, nextSlots, reads, evaluated, nativeRun, nextEncoded,
        by rw [frame]; exact agrees⟩
  | @writeMap name keyTy valueTy key value declared keyValid valueValid =>
    cases admitted with
    | cell _ cell _ => cases cell
    | writeMap _ _ _ _ _ _ _ keyAdmitted valueAdmitted =>
      obtain ⟨declaration, found, kind⟩ := declared
      have named := beq_iff_eq.mp (List.find?_some (p := fun item : StateDecl => item.name == name) found)
      have keyAgreement := eval_scoped types sourceEnv complete agrees ctx stateEffectCaps key keyValid
      have valueAgreement := eval_scoped types sourceEnv complete agrees ctx stateEffectCaps value valueValid
      obtain ⟨activity, segment, nextSlots, evaluated, nativeRun, nextEncoded, frame⟩ :=
        GenericStateConverseWrite.guarded_source_writeMap_converse ctx sourceEnv complete state
          guard current slots name keyTy valueTy key value keyAdmitted valueAdmitted
          sourceAfter beforePlan afterPlan reads sourceStep guardAgreement keyAgreement.symm
          valueAgreement.symm declaration found named kind compiled encoded distinct stateBound modulus
      exact ⟨activity, segment, nextSlots, reads, evaluated, nativeRun, nextEncoded,
        by rw [frame]; exact agrees⟩
  | @requireAbsent name keyTy key valueTy declared keyValid =>
    cases scope with
    | unguarded _ =>
      cases admitted with
      | cell _ cell _ => cases cell
      | requireAbsent _ _ _ _ keyAdmitted =>
        obtain ⟨declaration, found, kind⟩ := declared
        have named := beq_iff_eq.mp (List.find?_some (p := fun item : StateDecl => item.name == name) found)
        have keyAgreement := eval_scoped types sourceEnv complete agrees ctx stateEffectCaps key keyValid
        obtain ⟨segment, evaluated, nativeRun, frame⟩ :=
          GenericStateConverseAbsence.source_requireAbsent_chunk ctx sourceEnv complete state
            current slots name keyTy valueTy key keyAdmitted sourceAfter beforePlan afterPlan reads
            sourceStep keyAgreement.symm declaration found named kind compiled encoded modulus
        subst sourceAfter
        exact ⟨none, segment, slots, reads ++ [boolean false], evaluated, nativeRun, encoded, agrees⟩

end Noctium.Verification.GenericStateConverseEffectStep
