import Noctium.Verification.ScalarGuardedPlanAdmission
import Noctium.Verification.GuardedPlanActivity

namespace Noctium.Verification.ScalarGuardedActivityAdmission

open Backend GenericStateCheckedReadTrace GuardedPlanActivity
open ScalarGuardedPlanAdmission (ScalarEffect)

private theorem scalar_effect_guarded_read_effect
    (state : List StateDecl) (effect : Effect) (guard : Option (Expr .bool))
    (before after : Impact.Plan) (source : ScalarEffect state effect)
    (accepted : Impact.appendEffectWithActivity state effect guard before = .ok after) :
    GuardedScalarReadEffect guard effect := by
  cases guard with
  | none =>
    apply GuardedScalarReadEffect.unguarded
    cases source with
    | cell effect cell operand =>
      cases cell with
      | readCell name destination ty scalar declaration =>
        exact ScalarReadEffect.readCell name destination ty
      | writeCell name ty value scalar declaration =>
        exact ScalarReadEffect.writeCell name ty value
    | readMap name destination keyTy valueTy key keyScalar valueScalar keyAdmitted =>
      exact ScalarReadEffect.readMap name destination keyTy valueTy key
    | writeMap name keyTy valueTy key value keyScalar valueScalar keyAdmitted valueAdmitted =>
      exact ScalarReadEffect.writeMap name keyTy valueTy key value
    | require condition admitted => exact ScalarReadEffect.require condition
    | requireAbsent name keyTy key keyScalar keyAdmitted =>
      exact ScalarReadEffect.requireAbsent name keyTy key
  | some condition =>
    cases source with
    | cell effect cell operand =>
      cases cell with
      | readCell name destination ty scalar declaration =>
        exact GuardedScalarReadEffect.readCell condition name destination ty
      | writeCell name ty value scalar declaration =>
        exact GuardedScalarReadEffect.writeCell condition name ty value
    | readMap name destination keyTy valueTy key keyScalar valueScalar keyAdmitted =>
      exact GuardedScalarReadEffect.readMap condition name destination keyTy valueTy key
    | writeMap name keyTy valueTy key value keyScalar valueScalar keyAdmitted valueAdmitted =>
      exact GuardedScalarReadEffect.writeMap condition name keyTy valueTy key value
    | require required admitted =>
      exact GuardedScalarReadEffect.require condition required
    | requireAbsent name keyTy key keyScalar keyAdmitted =>
      exact False.elim (ScalarRequireOperationAdmission.append_requireAbsent_guarded_rejected
        state name keyTy key condition before after accepted)

private theorem trace_operation_guard_mem
    {state : List StateDecl} {guards : List (Option (Expr .bool))}
    {items : List (Effect × Nat)} {initial final : Impact.Plan} {offsets : List Nat}
    (trace : Impact.GuardedEffectTrace state guards items initial final offsets)
    (effects : ∀ item ∈ items, ScalarEffect state item.1)
    (aligned : (operationGuards initial).length = initial.operations.length) :
    ∃ schedule, operationGuards final = operationGuards initial ++ schedule ∧
      ∀ condition, some condition ∈ schedule → some condition ∈ guards := by
  induction trace with
  | nil plan =>
    exact ⟨[], by simp, by simp⟩
  | @cons item rest before next final offsets step tail ih =>
    have source : ScalarEffect state item.1 := effects item (by simp)
    have scope := scalar_effect_guarded_read_effect state item.1
      (guards[item.2]?.getD none) before next source step
    obtain ⟨chunk, operations, guardSources⟩ := appendActivity_chunk state item.1
      (guards[item.2]?.getD none) scope before next aligned step
    have nextAligned : (operationGuards next).length = next.operations.length := by
      rw [guardSources, operations, List.length_append, List.length_append,
        List.length_replicate, aligned]
    have remainingEffects : ∀ remaining ∈ rest, ScalarEffect state remaining.1 := by
      intro remaining member
      exact effects remaining (List.mem_cons_of_mem item member)
    obtain ⟨tailSchedule, tailGuards, tailSources⟩ := ih remainingEffects nextAligned
    refine ⟨List.replicate chunk.length (guards[item.2]?.getD none) ++ tailSchedule,
      ?_, ?_⟩
    · rw [tailGuards, guardSources]
      simp [List.append_assoc]
    · intro condition member
      rcases List.mem_append.mp member with current | later
      · have selected : some condition = guards[item.2]?.getD none :=
          (List.mem_replicate.mp current).2
        cases found : guards[item.2]? with
        | none => simp [found] at selected
        | some guard =>
          have same : guard = some condition := by simpa [found] using selected.symm
          exact same ▸ List.mem_of_getElem? found
      · exact tailSources condition later

/-- Any active guard recorded by accepted scalar lowering comes from an
admitted source effect. Public input lowering starts with unconditional
operations, and guarded absence checks are rejected by the production
activity wrapper. -/
theorem lower_activity_guard_mem (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan)
    (lowered : Impact.lower state entry = .ok plan)
    (effects : ∀ effect ∈ entry.effects, ScalarEffect state effect)
    (condition : Expr .bool)
    (member : some condition ∈ plan.activityGuards) :
    some condition ∈ entry.effectGuards := by
  obtain ⟨_, inputPlan, _, inputAccepted, trace⟩ :=
    GenericStateAdmissionPrefix.lower_guarded_effect_trace state entry plan lowered
  have empty := Impact.publicInputPlan_activity_guards entry.circuit.inputs {}
    inputPlan inputAccepted
  have initialAligned : (operationGuards inputPlan).length = inputPlan.operations.length := by
    simp [operationGuards, empty]
  have operationMember : some condition ∈ operationGuards plan := by
    unfold operationGuards
    split
    · simp_all
    · exact member
  obtain ⟨schedule, traceGuards, traceSources⟩ := trace_operation_guard_mem trace (by
    intro item itemMember
    apply effects item.1
    rw [← List.zipIdx_map_fst 0 entry.effects]
    exact List.mem_map_of_mem itemMember) initialAligned
  rw [traceGuards] at operationMember
  rcases List.mem_append.mp operationMember with initial | source
  · simp [operationGuards, empty] at initial
  · exact traceSources condition source

end Noctium.Verification.ScalarGuardedActivityAdmission
