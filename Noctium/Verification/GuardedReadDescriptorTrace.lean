import Noctium.Verification.GenericStateCheckedReadTrace

namespace Noctium.Verification.GuardedReadDescriptorTrace

open Backend
open GenericStateCheckedReadTrace

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

/-- Every supported source effect preserves the current read tape as a prefix.
The suffix may contain an absence witness as well as scalar read descriptors. -/
private theorem appendEffectWithActivity_guarded_reads_append
    (state : List StateDecl) (effect : Effect) (guard : Option (Expr .bool))
    (scope : GuardedScalarReadEffect guard effect) (before after : Impact.Plan)
    (accepted : Impact.appendEffectWithActivity state effect guard before = .ok after) :
    ∃ added, after.reads = before.reads ++ added := by
  cases scope with
  | unguarded sourceScope =>
    obtain ⟨raw, appended, _, sameReads⟩ :=
      GuardedEffectPrefix.appendEffectWithActivity_none_result
        state effect before after accepted
    cases sourceScope with
    | readCell name destination ty =>
      simp only [Impact.appendEffect, bind_ok] at appended
      obtain ⟨_, _, _, _, resultAccepted⟩ := appended
      simp only [Pure.pure, Except.pure] at resultAccepted
      have stateEq := Except.ok.inj resultAccepted
      let read := raw.reads[before.reads.length]?.getD {name := destination, ty}
      have readsShape : raw.reads = before.reads ++ [read] := by
        simp [read, stateEq.symm]
      exact ⟨[read], sameReads.trans readsShape⟩
    | readMap name destination keyTy valueTy key =>
      have readsShape := GuardedEffectPrefix.appendEffect_readMap_read_suffix
        state name destination keyTy valueTy key before raw appended
      exact ⟨[{name := destination, ty := valueTy}], sameReads.trans readsShape⟩
    | requireAbsent name keyTy key =>
      simp only [Impact.appendEffect, bind_ok] at appended
      obtain ⟨_, _, _, _, resultAccepted⟩ := appended
      simp only [Pure.pure, Except.pure] at resultAccepted
      have stateEq := Except.ok.inj resultAccepted
      let read := raw.reads[before.reads.length]?.getD
        {name := "_noctium_absence_" ++ toString before.reads.length, ty := .bool}
      have readsShape : raw.reads = before.reads ++ [read] := by
        simp [read, stateEq.symm]
      exact ⟨[read], sameReads.trans readsShape⟩
    | require condition =>
      simp only [Impact.appendEffect] at appended
      have resultEq := Except.ok.inj appended
      have readsSame : raw.reads = before.reads := by
        rw [← resultEq]
      exact ⟨[], by
        calc
          after.reads = raw.reads := sameReads
          _ = before.reads := readsSame
          _ = before.reads ++ [] := by simp⟩
    | writeCell name ty value =>
      simp only [Impact.appendEffect, bind_ok] at appended
      obtain ⟨_, _, _, _, resultAccepted⟩ := appended
      simp only [Pure.pure, Except.pure] at resultAccepted
      have readsSame : raw.reads = before.reads := by
        rw [← Except.ok.inj resultAccepted]
      exact ⟨[], by
        calc
          after.reads = raw.reads := sameReads
          _ = before.reads := readsSame
          _ = before.reads ++ [] := by simp⟩
    | writeMap name keyTy valueTy key value =>
      simp only [Impact.appendEffect, bind_ok] at appended
      obtain ⟨_, _, _, _, _, _, resultAccepted⟩ := appended
      simp only [Pure.pure, Except.pure] at resultAccepted
      have readsSame : raw.reads = before.reads := by
        rw [← Except.ok.inj resultAccepted]
      exact ⟨[], by
        calc
          after.reads = raw.reads := sameReads
          _ = before.reads := readsSame
          _ = before.reads ++ [] := by simp⟩
  | readCell condition name destination ty =>
    obtain ⟨_, _, read, _, _, _, readsShape, _, _⟩ :=
      GuardedEffectPrefix.appendEffectWithActivity_readCell_provenance
        state name destination ty condition before after accepted
    exact ⟨[read], readsShape⟩
  | readMap condition name destination keyTy valueTy key =>
    have readsShape := GuardedEffectPrefix.appendEffectWithActivity_readMap_read_suffix
      state name destination keyTy valueTy key condition before after accepted
    exact ⟨[{name := destination, ty := valueTy, guard := some condition}], readsShape⟩
  | writeCell condition name ty value =>
    have readsSame := GuardedEffectPrefix.appendEffectWithActivity_guarded_writeCell_no_reads
      state name ty value condition before after accepted
    exact ⟨[], by
      calc
        after.reads = before.reads := readsSame
        _ = before.reads ++ [] := by simp⟩
  | writeMap condition name keyTy valueTy key value =>
    have readsSame := GuardedEffectPrefix.appendEffectWithActivity_guarded_writeMap_no_reads
      state name keyTy valueTy key value condition before after accepted
    exact ⟨[], by
      calc
        after.reads = before.reads := readsSame
        _ = before.reads ++ [] := by simp⟩
  | require condition required =>
    have readsSame := GuardedEffectPrefix.appendEffectWithActivity_guarded_require_no_reads
      state condition required before after accepted
    exact ⟨[], by
      calc
        after.reads = before.reads := readsSame
        _ = before.reads ++ [] := by simp⟩

private theorem guardedTrace_reads_append
    (state : List StateDecl) (guards : List (Option (Expr .bool)))
    (items : List (Effect × Nat)) (initial result : Impact.Plan) (offsets : List Nat)
    (scope : GuardedScalarReadEffects guards items)
    (trace : Impact.GuardedEffectTrace state guards items initial result offsets) :
    ∃ added, result.reads = initial.reads ++ added := by
  induction trace with
  | nil => exact ⟨[], by simp⟩
  | @cons item rest before next result offsets step tail ih =>
    have headScope : GuardedScalarReadEffect
        (guards[item.2]?.getD none) item.1 := by
      apply scope
      simp
    have tailScope : GuardedScalarReadEffects guards rest := by
      intro later member
      apply scope later
      simp [member]
    obtain ⟨added, headReads⟩ := appendEffectWithActivity_guarded_reads_append
      state item.1 (guards[item.2]?.getD none) headScope before next step
    obtain ⟨later, tailReads⟩ := ih tailScope
    refine ⟨added ++ later, ?_⟩
    rw [tailReads, headReads]
    simp [List.append_assoc]

private theorem guardedTrace_read_descriptor
    (state : List StateDecl) (guards : List (Option (Expr .bool)))
    (items : List (Effect × Nat)) (initial result : Impact.Plan) (offsets : List Nat)
    (scope : GuardedScalarReadEffects guards items)
    (trace : Impact.GuardedEffectTrace state guards items initial result offsets)
    (target : Effect × Nat) (condition : Expr .bool)
    (descriptor : Impact.Read → Prop) (member : target ∈ items)
    (sourceGuard : guards[target.2]?.getD none = some condition)
    (selected : ∀ before next,
      Impact.appendEffectWithActivity state target.1 (some condition) before = .ok next →
      ∃ read : Impact.Read, next.reads = before.reads ++ [read] ∧ descriptor read) :
    ∃ (beforeTarget suffix : List Impact.Read) (read : Impact.Read),
      result.reads = initial.reads ++ beforeTarget ++ [read] ++ suffix ∧
      descriptor read := by
  induction trace with
  | nil => simp at member
  | @cons item rest before next result offsets step tail ih =>
    rcases List.mem_cons.mp member with head | later
    · cases head
      have headStep : Impact.appendEffectWithActivity state target.1
          (some condition) before = .ok next := by
        simpa [sourceGuard] using step
      obtain ⟨read, headReads, readSelected⟩ := selected before next headStep
      have tailScope : GuardedScalarReadEffects guards rest := by
        intro later member
        apply scope later
        simp [member]
      obtain ⟨afterTarget, tailReads⟩ := guardedTrace_reads_append
        state guards rest next result offsets tailScope tail
      refine ⟨[], afterTarget, read, ?_, readSelected⟩
      rw [tailReads, headReads]
      simp [List.append_assoc]
    · have tailScope : GuardedScalarReadEffects guards rest := by
        intro laterItem member
        apply scope laterItem
        simp [member]
      obtain ⟨beforeTarget, suffix, read, readsShape, readSelected⟩ := ih tailScope later
      have headScope : GuardedScalarReadEffect
          (guards[item.2]?.getD none) item.1 := by
        apply scope
        simp
      obtain ⟨added, headReads⟩ := appendEffectWithActivity_guarded_reads_append
        state item.1 (guards[item.2]?.getD none) headScope before next step
      refine ⟨added ++ beforeTarget, suffix, read, ?_, readSelected⟩
      rw [readsShape, headReads]
      simp [List.append_assoc]

private theorem descriptor_mem_after_public_prefix
    {initial result : Impact.Plan} {beforeTarget suffix : List Impact.Read}
    {read : Impact.Read}
    (readsShape : result.reads = initial.reads ++ beforeTarget ++ [read] ++ suffix) :
    read ∈ result.reads.drop initial.reads.length := by
  rw [readsShape]
  simp

/-- An indexed guarded Cell read in the scoped source fragment has the exact
descriptor emitted by accepted production lowering, after the public-input
read prefix. -/
theorem lower_readCell_descriptor
    (state : List StateDecl) (entry : Entrypoint) (plan : Impact.Plan)
    (index : Nat) (condition : Expr .bool) (name destination : String) (ty : Ty)
    (accepted : Impact.lower state entry = .ok plan)
    (scope : GuardedScalarReadEffects entry.effectGuards entry.effects.zipIdx)
    (member : (Effect.readCell name destination ty, index) ∈ entry.effects.zipIdx)
    (sourceGuard : entry.effectGuardAt index = some condition) :
    ∃ read : Impact.Read,
      read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs) ∧
      read.name = destination ∧ read.ty = ty ∧ read.guard = some condition := by
  obtain ⟨_, inputPlan, _, prefixAccepted, trace⟩ :=
    GenericStateAdmissionPrefix.lower_guarded_effect_trace state entry plan accepted
  have exactGuard : entry.effectGuards[index]?.getD none = some condition := by
    simpa [Entrypoint.effectGuardAt] using sourceGuard
  let target : Effect × Nat := (Effect.readCell name destination ty, index)
  have selected : ∀ before next,
      Impact.appendEffectWithActivity state target.1 (some condition) before = .ok next →
      ∃ read : Impact.Read, next.reads = before.reads ++ [read] ∧
        read.name = destination ∧ read.ty = ty ∧ read.guard = some condition := by
    intro before next step
    obtain ⟨_, _, read, readName, readTy, readGuard, readsShape, _, _⟩ :=
      GuardedEffectPrefix.appendEffectWithActivity_readCell_provenance
        state name destination ty condition before next step
    exact ⟨read, readsShape, readName, readTy, readGuard⟩
  obtain ⟨beforeTarget, suffix, read, readsShape, descriptor⟩ :=
    guardedTrace_read_descriptor state entry.effectGuards entry.effects.zipIdx
      inputPlan plan _ scope trace target condition
      (fun read => read.name = destination ∧ read.ty = ty ∧
        read.guard = some condition) member exactGuard selected
  rcases descriptor with ⟨readName, readTy, readGuard⟩
  have inEffectSuffix := descriptor_mem_after_public_prefix readsShape
  have inputCount := GenericStateAdmissionPrefix.publicInputPlan_readCount
    entry.circuit.inputs inputPlan prefixAccepted
  rw [inputCount] at inEffectSuffix
  exact ⟨read, inEffectSuffix, readName, readTy, readGuard⟩

/-- An indexed guarded plain Map read in the scoped source fragment has the
exact descriptor emitted by accepted production lowering, after the
public-input read prefix. -/
theorem lower_readMap_descriptor
    (state : List StateDecl) (entry : Entrypoint) (plan : Impact.Plan)
    (index : Nat) (condition : Expr .bool) (name destination : String)
    (keyTy valueTy : Ty) (key : Expr keyTy)
    (accepted : Impact.lower state entry = .ok plan)
    (scope : GuardedScalarReadEffects entry.effectGuards entry.effects.zipIdx)
    (member : (Effect.readMap name destination keyTy valueTy key, index) ∈
      entry.effects.zipIdx)
    (sourceGuard : entry.effectGuardAt index = some condition) :
    ∃ read : Impact.Read,
      read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs) ∧
      read.name = destination ∧ read.ty = valueTy ∧ read.guard = some condition := by
  obtain ⟨_, inputPlan, _, prefixAccepted, trace⟩ :=
    GenericStateAdmissionPrefix.lower_guarded_effect_trace state entry plan accepted
  have exactGuard : entry.effectGuards[index]?.getD none = some condition := by
    simpa [Entrypoint.effectGuardAt] using sourceGuard
  let target : Effect × Nat := (Effect.readMap name destination keyTy valueTy key, index)
  have selected : ∀ before next,
      Impact.appendEffectWithActivity state target.1 (some condition) before = .ok next →
      ∃ read : Impact.Read, next.reads = before.reads ++ [read] ∧
        read.name = destination ∧ read.ty = valueTy ∧ read.guard = some condition := by
    intro before next step
    have readsShape := GuardedEffectPrefix.appendEffectWithActivity_readMap_read_suffix
      state name destination keyTy valueTy key condition before next step
    exact ⟨{name := destination, ty := valueTy, guard := some condition},
      readsShape, rfl, rfl, rfl⟩
  obtain ⟨beforeTarget, suffix, read, readsShape, descriptor⟩ :=
    guardedTrace_read_descriptor state entry.effectGuards entry.effects.zipIdx
      inputPlan plan _ scope trace target condition
      (fun read => read.name = destination ∧ read.ty = valueTy ∧
        read.guard = some condition) member exactGuard selected
  rcases descriptor with ⟨readName, readTy, readGuard⟩
  have inEffectSuffix := descriptor_mem_after_public_prefix readsShape
  have inputCount := GenericStateAdmissionPrefix.publicInputPlan_readCount
    entry.circuit.inputs inputPlan prefixAccepted
  rw [inputCount] at inEffectSuffix
  exact ⟨read, inEffectSuffix, readName, readTy, readGuard⟩

end Noctium.Verification.GuardedReadDescriptorTrace
