import Noctium.Verification.GenericStateAdmissionPrefix
import Noctium.Verification.GuardedEffectPrefix
import Noctium.Verification.ScalarCellSourceReads
import Noctium.Verification.ScalarCellPublicFields
import Noctium.Verification.ScalarWitnessLedgerReads

namespace Noctium.Verification.ScalarCellPlanScope

open Backend
open GenericStateCellAdmission
open ScalarNormalization
open ScalarWitnessConstruction

private theorem bind_ok {α β : Type} {first : Except ε α} {next : α → Except ε β}
    {result : β} : (first >>= next) = .ok result ↔
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private def scalarTypeOfCell {ty : Ty} : ScalarCellType ty → ScalarType ty
  | .native => .native
  | .bool => .bool
  | .uint maximum _ => .uint maximum

private theorem appendEffect_scalarCell_preserves_guards
    (state : List StateDecl) (effect : Effect) (source : ScalarCellEffect state effect)
    (before after : Impact.Plan)
    (accepted : Impact.appendEffect state effect before = .ok after) :
    after.guards = before.guards ∧ after.activityGuards = before.activityGuards := by
  have same :
      (fun plan : Impact.Plan => (plan.guards, plan.activityGuards)) <$>
        Impact.appendEffect state effect before =
      (fun _ : Impact.Plan => (before.guards, before.activityGuards)) <$>
        Impact.appendEffect state effect before := by
    cases source <;>
      simp only [Impact.appendEffect, map_bind, LawfulApplicative.map_pure] <;> rfl
  rw [accepted] at same
  exact Prod.mk.inj (Except.ok.inj same)

private theorem appendEffectWithActivity_none_empty
    (state : List StateDecl) (effect : Effect) (before after : Impact.Plan)
    (beforeActivity : before.activityGuards = [])
    (accepted : Impact.appendEffectWithActivity state effect none before = .ok after) :
    ∃ raw, Impact.appendEffect state effect before = .ok raw ∧ after = raw := by
  have shape : Impact.appendEffectWithActivity state effect none before = (do
      let raw ← Impact.appendEffect state effect before
      if before.activityGuards.isEmpty then pure raw
      else
        let guards := before.activityGuards ++
          List.replicate (raw.operations.length - before.operations.length) none
        pure ({raw with activityGuards := guards} : Impact.Plan)) := by
    cases effect <;> rfl
  rw [shape] at accepted
  have empty : before.activityGuards.isEmpty = true := by simp [beforeActivity]
  simp only [empty, ite_true, bind_ok] at accepted
  obtain ⟨raw, appended, finished⟩ := accepted
  simp only [Pure.pure, Except.pure] at finished
  exact ⟨raw, appended, (Except.ok.inj finished).symm⟩

private theorem appendEffect_readCell_plain
    (state : List StateDecl) (name destination : String) (ty : Ty)
    (before after : Impact.Plan)
    (accepted : Impact.appendEffect state (.readCell name destination ty) before = .ok after) :
    ∃ read, after.reads = before.reads ++ [read] ∧
      read.name = destination ∧ read.ty = ty ∧
      read.components = [] ∧ read.guard = none := by
  simp only [Impact.appendEffect, bind_ok] at accepted
  obtain ⟨slot, slotAccepted, value, valueAccepted, resultAccepted⟩ := accepted
  simp only [Pure.pure, Except.pure] at resultAccepted
  let read : Impact.Read :=
    after.reads[before.reads.length]?.getD {name := destination, ty}
  have resultEq := Except.ok.inj resultAccepted
  have readsShape : after.reads = before.reads ++ [read] := by
    simp [read, resultEq.symm]
  refine ⟨read, readsShape, ?_, ?_, ?_, ?_⟩
  · simp [read, resultEq.symm]
  · simp [read, resultEq.symm]
  · simp [read, resultEq.symm]
  · simp [read, resultEq.symm]

private theorem appendEffect_scalarCell_read_facts
    (state : List StateDecl) (effect : Effect) (source : ScalarCellEffect state effect)
    (before after : Impact.Plan)
    (beforeActivity : before.activityGuards = [])
    (accepted : Impact.appendEffectWithActivity state effect none before = .ok after) :
    ∃ added, after.reads = before.reads ++ added ∧
      ∀ read ∈ added, PlainScalarLedgerRead read ∧ Nonempty (ScalarType read.ty) := by
  obtain ⟨raw, rawAccepted, afterRaw⟩ :=
    appendEffectWithActivity_none_empty state effect before after beforeActivity accepted
  cases source with
  | readCell name destination ty scalar declaration =>
    obtain ⟨read, reads, nameEq, typeEq, components, guard⟩ :=
      appendEffect_readCell_plain state name destination ty before raw rawAccepted
    refine ⟨[read], ?_, ?_⟩
    · rw [afterRaw, reads]
    · intro candidate member
      simp only [List.mem_singleton] at member
      subst candidate
      exact ⟨⟨components, guard⟩,
        ⟨typeEq.symm ▸ scalarTypeOfCell scalar⟩⟩
  | writeCell name ty value scalar declaration =>
    have readsSame : raw.reads = before.reads := by
      have same : Impact.Plan.reads <$> Impact.appendEffect state
          (.writeCell name ty value) before =
          (fun _ : Impact.Plan => before.reads) <$> Impact.appendEffect state
            (.writeCell name ty value) before := by
        simp only [Impact.appendEffect, map_bind, LawfulApplicative.map_pure] <;> rfl
      rw [rawAccepted] at same
      exact Except.ok.inj same
    refine ⟨[], ?_, ?_⟩
    · rw [afterRaw, readsSame]
      simp
    · simp

private theorem guarded_cell_trace_facts
    {state : List StateDecl} {guards : List (Option (Expr .bool))}
    {items : List (Effect × Nat)} {initial result : Impact.Plan} {offsets : List Nat}
    (guardsEmpty : guards = [])
    (source : ∀ item ∈ items, ScalarCellEffect state item.1)
    (trace : Impact.GuardedEffectTrace state guards items initial result offsets)
    (initialActivity : initial.activityGuards = []) :
    ∃ suffix,
      result.reads = initial.reads ++ suffix ∧
      (∀ read ∈ suffix, PlainScalarLedgerRead read ∧ Nonempty (ScalarType read.ty)) ∧
      result.activityGuards = [] := by
  induction trace with
  | nil plan =>
    exact ⟨[], by simp, by simp, initialActivity⟩
  | @cons item rest before next result offsets step tail ih =>
    have sourceHead : ScalarCellEffect state item.1 := source item (by simp)
    have stepNone : Impact.appendEffectWithActivity state item.1 none before = .ok next := by
      simpa [guardsEmpty] using step
    obtain ⟨raw, rawAccepted, nextRaw⟩ :=
      appendEffectWithActivity_none_empty state item.1 before next initialActivity stepNone
    have stable := appendEffect_scalarCell_preserves_guards
      state item.1 sourceHead before raw rawAccepted
    have nextActivity : next.activityGuards = [] := by
      rw [nextRaw, stable.2, initialActivity]
    obtain ⟨headReads, headReadShape, headPlain⟩ :=
      appendEffect_scalarCell_read_facts state item.1 sourceHead before next
        initialActivity stepNone
    have tailSource : ∀ later ∈ rest, ScalarCellEffect state later.1 := by
      intro later member
      exact source later (List.mem_cons_of_mem item member)
    obtain ⟨suffix, tailReads, suffixPlain, finalActivity⟩ :=
      ih tailSource nextActivity
    refine ⟨headReads ++ suffix, ?_, ?_, finalActivity⟩
    · rw [tailReads, headReadShape]
      simp [List.append_assoc]
    · intro read member
      rcases List.mem_append.mp member with head | tail
      · exact headPlain read head
      · exact suffixPlain read tail

private theorem guarded_cell_trace_guards
    {state : List StateDecl} {guards : List (Option (Expr .bool))}
    {items : List (Effect × Nat)} {initial result : Impact.Plan} {offsets : List Nat}
    (guardsEmpty : guards = [])
    (source : ∀ item ∈ items, ScalarCellEffect state item.1)
    (trace : Impact.GuardedEffectTrace state guards items initial result offsets)
    (initialActivity : initial.activityGuards = []) :
    result.guards = initial.guards := by
  induction trace with
  | nil plan => rfl
  | @cons item rest before next result offsets step tail ih =>
    have sourceHead : ScalarCellEffect state item.1 := source item (by simp)
    have stepNone : Impact.appendEffectWithActivity state item.1 none before = .ok next := by
      simpa [guardsEmpty] using step
    obtain ⟨raw, rawAccepted, nextRaw⟩ :=
      appendEffectWithActivity_none_empty state item.1 before next initialActivity stepNone
    have stable := appendEffect_scalarCell_preserves_guards
      state item.1 sourceHead before raw rawAccepted
    have nextActivity : next.activityGuards = [] := by
      rw [nextRaw, stable.2, initialActivity]
    have nextGuards : next.guards = before.guards := by
      rw [nextRaw, stable.1]
    have tailSource : ∀ later ∈ rest, ScalarCellEffect state later.1 := by
      intro later member
      exact source later (List.mem_cons_of_mem item member)
    exact (ih tailSource nextActivity).trans nextGuards

/-- Accepted lowering of unguarded scalar-cell effects gives an unconditional
activity schedule and only plain Native, Bool, or UInt post-public reads. -/
theorem lower_scope (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan)
    (accepted : Impact.lower state entry = .ok plan)
    (unguarded : entry.effectGuards = [])
    (cellEffects : ScalarCellSourceReads.ScalarCellEffects state entry.effects) :
    plan.activityGuards.all Option.isNone = true ∧
      ∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
        PlainScalarLedgerRead read ∧ Nonempty (ScalarType read.ty) := by
  obtain ⟨boundaries, inputPlan, boundedLowering, prefixAccepted, trace⟩ :=
    GenericStateAdmissionPrefix.lower_guarded_effect_trace state entry plan accepted
  have inputActivity : inputPlan.activityGuards = [] :=
    Impact.publicInputPlan_activity_guards entry.circuit.inputs {} inputPlan prefixAccepted
  have source : ∀ item ∈ entry.effects.zipIdx, ScalarCellEffect state item.1 := by
    intro item member
    apply cellEffects item.1
    rw [← List.zipIdx_map_fst 0 entry.effects]
    exact List.mem_map_of_mem member
  obtain ⟨suffix, readsShape, suffixPlain, activity⟩ :=
    guarded_cell_trace_facts (state := state) (guards := entry.effectGuards)
      (items := entry.effects.zipIdx) (initial := inputPlan) (result := plan)
      (offsets := boundaries) unguarded source trace inputActivity
  have prefixLength := GenericStateAdmissionPrefix.publicInputPlan_readCount
    entry.circuit.inputs inputPlan prefixAccepted
  have postPublic : plan.reads.drop inputPlan.reads.length = suffix := by
    rw [readsShape, List.drop_left]
  have actualReads :
      plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs) = suffix := by
    rw [← prefixLength]
    exact postPublic
  refine ⟨?_, ?_⟩
  · simp [activity]
  · intro read member
    rw [actualReads] at member
    exact suffixPlain read member

/-- Cell-only source effects add no guards to the scalar-compatible public
input prefix. -/
theorem lower_guards_empty (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan)
    (accepted : Impact.lower state entry = .ok plan)
    (unguarded : entry.effectGuards = [])
    (compatible : ∀ input ∈ entry.circuit.inputs,
      Impact.publicInputScalarCompatible input)
    (cellEffects : ScalarCellSourceReads.ScalarCellEffects state entry.effects) :
    plan.guards = [] := by
  obtain ⟨boundaries, inputPlan, _, prefixAccepted, trace⟩ :=
    GenericStateAdmissionPrefix.lower_guarded_effect_trace state entry plan accepted
  have prefixEmpty := ScalarCellPublicFields.publicInputPlan_empty_guards
    entry.circuit.inputs inputPlan compatible prefixAccepted
  have source : ∀ item ∈ entry.effects.zipIdx, ScalarCellEffect state item.1 := by
    intro item member
    apply cellEffects item.1
    rw [← List.zipIdx_map_fst 0 entry.effects]
    exact List.mem_map_of_mem member
  have traceGuards := guarded_cell_trace_guards (state := state)
    (guards := entry.effectGuards) (items := entry.effects.zipIdx)
    (initial := inputPlan) (result := plan) (offsets := boundaries)
    unguarded source trace prefixEmpty.2
  exact traceGuards.trans prefixEmpty.1

end Noctium.Verification.ScalarCellPlanScope
