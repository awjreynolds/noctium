import Noctium.Backend.Impact

namespace Noctium.Verification.GuardedEffectPrefix
open Backend

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

theorem appendEffect_readCell_operation_suffix (state : List StateDecl)
    (name destination : String) (ty : Ty) (before after : Impact.Plan)
    (step : Impact.appendEffect state (.readCell name destination ty) before =
      .ok after) :
    ∃ slot value, after.operations = before.operations ++
      [.dup, .index slot, value] := by
  simp only [Impact.appendEffect, bind_ok] at step
  rcases step with ⟨slot, slotAccepted, value, valueAccepted, resultAccepted⟩
  cases resultAccepted
  exact ⟨slot, value, rfl⟩

private theorem appendEffect_readCell_read_suffix (state : List StateDecl)
    (name destination : String) (ty : Ty) (before after : Impact.Plan)
    (step : Impact.appendEffect state (.readCell name destination ty) before =
      .ok after) :
    ∃ read, after.reads = before.reads ++ [read] ∧
      read.name = destination ∧ read.ty = ty := by
  simp only [Impact.appendEffect, bind_ok] at step
  rcases step with ⟨slot, slotAccepted, value, valueAccepted, resultAccepted⟩
  simp only [Pure.pure, Except.pure] at resultAccepted
  have stateEq := Except.ok.inj resultAccepted
  let read : Impact.Read :=
    after.reads[before.reads.length]?.getD {name := destination, ty}
  have readsShape : after.reads = before.reads ++ [read] := by
    simp [read, stateEq.symm]
  exact ⟨read, readsShape, by simp [read, stateEq.symm],
    by simp [read, stateEq.symm]⟩

private theorem appendEffectWithActivity_readCell_wrapper_shape
    (state : List StateDecl) (name destination : String) (ty : Ty)
    (condition : Expr .bool) (before after : Impact.Plan)
    (step : Impact.appendEffectWithActivity state (.readCell name destination ty)
      (some condition) before = .ok after) :
    ∃ result read,
      Impact.appendEffect state (.readCell name destination ty) before = .ok result ∧
      result.reads[before.reads.length]? = some read ∧
      {result with
        reads := result.reads.take before.reads.length ++
          [{read with guard := some condition}]
        activityGuards :=
          (if before.activityGuards.isEmpty then
            List.replicate before.operations.length none else before.activityGuards) ++
            List.replicate (result.operations.length - before.operations.length)
              (some condition)} = after := by
  unfold Impact.appendEffectWithActivity at step
  simp only [bind_ok] at step
  rcases step with ⟨lowered, loweredAccepted, result, appendAccepted, wrapperAccepted⟩
  have effectShape : lowered = .readCell name destination ty := by
    change Except.ok (.readCell name destination ty) = Except.ok lowered at loweredAccepted
    exact (Except.ok.inj loweredAccepted).symm
  subst lowered
  cases readFound : result.reads[before.reads.length]? with
  | none => simp [readFound] at wrapperAccepted
  | some read =>
    simp only [readFound, Pure.pure, Except.pure] at wrapperAccepted
    exact ⟨result, read, appendAccepted, readFound, Except.ok.inj wrapperAccepted⟩

private theorem appendEffect_readCell_empty_plan_chunk
    (state : List StateDecl) (name destination : String) (ty : Ty)
    (before after base : Impact.Plan)
    (step : Impact.appendEffect state (.readCell name destination ty) before = .ok after)
    (emptyStep : Impact.appendEffect state (.readCell name destination ty) {} = .ok base) :
    ∃ slot value read,
      after.operations = before.operations ++ [.dup, .index slot, value] ∧
      base.operations = [.dup, .index slot, value] ∧
      after.reads = before.reads ++ [read] ∧ base.reads = [read] := by
  simp only [Impact.appendEffect, bind_ok] at step emptyStep
  rcases step with ⟨slot, slotAccepted, value, valueAccepted, resultAccepted⟩
  rcases emptyStep with
    ⟨emptySlot, emptySlotAccepted, emptyValue, emptyValueAccepted, emptyResultAccepted⟩
  have slotEq : slot = emptySlot :=
    Except.ok.inj (slotAccepted.symm.trans emptySlotAccepted)
  subst emptySlot
  have valueEq : value = emptyValue :=
    Except.ok.inj (valueAccepted.symm.trans emptyValueAccepted)
  subst emptyValue
  simp only [Pure.pure, Except.pure] at resultAccepted emptyResultAccepted
  have resultEq := Except.ok.inj resultAccepted
  have emptyResultEq := Except.ok.inj emptyResultAccepted
  cases resultEq
  cases emptyResultEq
  exact ⟨slot, value, _, rfl, by simp, rfl, by simp⟩

theorem appendEffect_writeCell_operation_suffix (state : List StateDecl)
    (name : String) (ty : Ty) (value : Expr ty) (before after : Impact.Plan)
    (step : Impact.appendEffect state (.writeCell name ty value) before =
      .ok after) :
    ∃ slot stored, after.operations = before.operations ++
      [.push (.field (.native slot)), stored, .insert 1] := by
  simp only [Impact.appendEffect, bind_ok] at step
  rcases step with ⟨slot, slotAccepted, stored, storedAccepted, resultAccepted⟩
  cases resultAccepted
  exact ⟨slot, stored, rfl⟩

theorem appendEffect_readMap_operation_suffix (state : List StateDecl)
    (name destination : String) (keyTy valueTy : Ty) (key : Expr keyTy)
    (before after : Impact.Plan)
    (step : Impact.appendEffect state
      (.readMap name destination keyTy valueTy key) before = .ok after) :
    ∃ slot alignedKey stored, after.operations = before.operations ++
      [.dup, .mapIndex slot alignedKey, stored] := by
  simp only [Impact.appendEffect, bind_ok] at step
  rcases step with ⟨slot, slotAccepted, alignedKey, keyAccepted,
    stored, storedAccepted, resultAccepted⟩
  cases resultAccepted
  exact ⟨slot, alignedKey, stored, rfl⟩

theorem appendEffect_writeMap_operation_suffix (state : List StateDecl)
    (name : String) (keyTy valueTy : Ty) (key : Expr keyTy)
    (value : Expr valueTy) (before after : Impact.Plan)
    (step : Impact.appendEffect state
      (.writeMap name keyTy valueTy key value) before = .ok after) :
    ∃ slot, ∃ keyPush : Impact.Op, ∃ stored,
      after.operations = before.operations ++
        [.index slot true, keyPush, stored, .insert 2] := by
  simp only [Impact.appendEffect, bind_ok] at step
  rcases step with ⟨slot, slotAccepted, _alignedKey, keyAccepted,
    stored, storedAccepted, resultAccepted⟩
  cases resultAccepted
  exact ⟨slot, _, stored, rfl⟩

theorem appendEffectWithActivity_readCell_operation_suffix
    (state : List StateDecl) (name destination : String) (ty : Ty)
    (condition : Expr .bool) (before after : Impact.Plan)
    (step : Impact.appendEffectWithActivity state (.readCell name destination ty)
      (some condition) before = .ok after) :
    ∃ slot value, after.operations = before.operations ++
      [.dup, .index slot, value] := by
  obtain ⟨result, _, appendAccepted, _, wrapperShape⟩ :=
    appendEffectWithActivity_readCell_wrapper_shape state name destination ty condition
      before after step
  obtain ⟨slot, value, operationsShape⟩ :=
    appendEffect_readCell_operation_suffix state name destination ty before result appendAccepted
  have wrappedOperations : after.operations = result.operations := by
    exact (congrArg Impact.Plan.operations wrapperShape).symm
  exact ⟨slot, value, wrappedOperations.trans operationsShape⟩

/-- A guarded cell read appends the same destination and type as its source
effect, binds that read to the source condition, and assigns the guard to all
three appended operations. Existing guard prefixes retain their padding rule. -/
theorem appendEffectWithActivity_readCell_provenance
    (state : List StateDecl) (name destination : String) (ty : Ty)
    (condition : Expr .bool) (before after : Impact.Plan)
    (step : Impact.appendEffectWithActivity state (.readCell name destination ty)
      (some condition) before = .ok after) :
    ∃ slot value read,
      read.name = destination ∧ read.ty = ty ∧ read.guard = some condition ∧
      after.reads = before.reads ++ [read] ∧
      after.operations = before.operations ++ [.dup, .index slot, value] ∧
      after.activityGuards =
        (if before.activityGuards.isEmpty then
          List.replicate before.operations.length none else before.activityGuards) ++
          List.replicate 3 (some condition) := by
  obtain ⟨result, wrapperRead, appendAccepted, wrapperReadAt, wrapperShape⟩ :=
    appendEffectWithActivity_readCell_wrapper_shape state name destination ty condition
      before after step
  obtain ⟨sourceRead, readsShape, sourceName, sourceTy⟩ :=
    appendEffect_readCell_read_suffix state name destination ty before result appendAccepted
  have sourceReadAt : result.reads[before.reads.length]? = some sourceRead := by
    rw [readsShape]
    simp
  have wrapperReadEq : wrapperRead = sourceRead :=
    Option.some.inj (wrapperReadAt.symm.trans sourceReadAt)
  obtain ⟨slot, value, operationShape⟩ :=
    appendEffect_readCell_operation_suffix state name destination ty before result appendAccepted
  let read : Impact.Read := {sourceRead with guard := some condition}
  have readFields : read.name = destination ∧ read.ty = ty ∧
      read.guard = some condition := by
    exact ⟨by simpa [read] using sourceName,
      by simpa [read] using sourceTy, rfl⟩
  have readsOut : after.reads = before.reads ++ [read] := by
    have projected := congrArg (fun plan : Impact.Plan => plan.reads) wrapperShape
    have updatedReads :
        result.reads.take before.reads.length ++
          [{wrapperRead with guard := some condition}] = before.reads ++ [read] := by
      rw [wrapperReadEq, readsShape]
      simp [read]
    exact projected.symm.trans updatedReads
  have operationsOut : after.operations = before.operations ++
      [.dup, .index slot, value] := by
    have projected := congrArg Impact.Plan.operations wrapperShape
    exact projected.symm.trans operationShape
  have operationCount : result.operations.length = before.operations.length + 3 := by
    rw [operationShape, List.length_append]
    simp
  have appendedCount : result.operations.length - before.operations.length = 3 := by
    omega
  have guardsOut : after.activityGuards =
      (if before.activityGuards.isEmpty then
        List.replicate before.operations.length none else before.activityGuards) ++
        List.replicate 3 (some condition) := by
    have projected := congrArg Impact.Plan.activityGuards wrapperShape
    calc
      after.activityGuards =
          (if before.activityGuards.isEmpty then
            List.replicate before.operations.length none else before.activityGuards) ++
            List.replicate (result.operations.length - before.operations.length)
              (some condition) := projected.symm
      _ = (if before.activityGuards.isEmpty then
          List.replicate before.operations.length none else before.activityGuards) ++
          List.replicate 3 (some condition) := by rw [appendedCount]
  exact ⟨slot, value, read, readFields.1, readFields.2.1, readFields.2.2,
    readsOut, operationsOut, guardsOut⟩

/-- A guarded cell read appends the same operation and read chunk as an
unguarded empty-plan read. The source guard updates only the read descriptor. -/
theorem appendEffectWithActivity_readCell_empty_chunk
    (state : List StateDecl) (name destination : String) (ty : Ty)
    (condition : Expr .bool) (before after base : Impact.Plan)
    (guardedStep : Impact.appendEffectWithActivity state
      (.readCell name destination ty) (some condition) before = .ok after)
    (emptyStep : Impact.appendEffect state (.readCell name destination ty) {} = .ok base) :
    after.operations = before.operations ++ base.operations ∧
      after.reads = before.reads ++
        base.reads.map (fun read => {read with guard := some condition}) := by
  obtain ⟨result, wrapperRead, appendAccepted, wrapperReadAt, wrapperShape⟩ :=
    appendEffectWithActivity_readCell_wrapper_shape state name destination ty condition
      before after guardedStep
  obtain ⟨slot, value, sourceRead, resultOperations, baseOperations,
    resultReads, baseReads⟩ := appendEffect_readCell_empty_plan_chunk
      state name destination ty before result base appendAccepted emptyStep
  have sourceReadAt : result.reads[before.reads.length]? = some sourceRead := by
    rw [resultReads]
    simp
  have wrapperReadEq : wrapperRead = sourceRead :=
    Option.some.inj (wrapperReadAt.symm.trans sourceReadAt)
  have operationsOut : after.operations = before.operations ++ base.operations := by
    have projected := congrArg Impact.Plan.operations wrapperShape
    calc
      after.operations = result.operations := projected.symm
      _ = before.operations ++ [.dup, .index slot, value] := resultOperations
      _ = before.operations ++ base.operations := by rw [baseOperations]
  have readsOut : after.reads = before.reads ++
      base.reads.map (fun read => {read with guard := some condition}) := by
    have projected := congrArg (fun plan : Impact.Plan => plan.reads) wrapperShape
    have updatedReads :
        result.reads.take before.reads.length ++
          [{wrapperRead with guard := some condition}] =
        before.reads ++ [{sourceRead with guard := some condition}] := by
      rw [wrapperReadEq, resultReads]
      simp
    calc
      after.reads = before.reads ++ [{sourceRead with guard := some condition}] :=
        projected.symm.trans updatedReads
      _ = before.reads ++ base.reads.map (fun read =>
          {read with guard := some condition}) := by
        rw [baseReads]
        simp
  exact ⟨operationsOut, readsOut⟩

theorem appendEffectWithActivity_writeCell_operation_suffix
    (state : List StateDecl) (name : String) (ty : Ty) (value : Expr ty)
    (condition : Expr .bool) (before after : Impact.Plan)
    (step : Impact.appendEffectWithActivity state (.writeCell name ty value)
      (some condition) before = .ok after) :
    ∃ slot stored, after.operations = before.operations ++
      [.push (.field (.native slot)), stored, .insert 1] := by
  unfold Impact.appendEffectWithActivity at step
  simp only [bind_ok] at step
  rcases step with ⟨lowered, loweredAccepted, result, appendAccepted, wrapperAccepted⟩
  have effectShape : ∃ guardedValue,
      lowered = .writeCell name ty guardedValue := by
    simp only [Pure.pure, Except.pure] at loweredAccepted
    cases loweredAccepted
    exact ⟨_, rfl⟩
  obtain ⟨guardedValue, rfl⟩ := effectShape
  obtain ⟨slot, stored, operationsShape⟩ :=
    appendEffect_writeCell_operation_suffix state name ty _ before result appendAccepted
  have wrappedOperations : after.operations = result.operations := by
    have projected := congrArg (Except.map Impact.Plan.operations) wrapperAccepted
    simp only [Pure.pure, Except.pure, Except.map] at projected
    exact (Except.ok.inj projected).symm
  exact ⟨slot, stored, wrappedOperations.trans operationsShape⟩

theorem appendEffectWithActivity_readMap_operation_suffix
    (state : List StateDecl) (name destination : String)
    (keyTy valueTy : Ty) (key : Expr keyTy) (condition : Expr .bool)
    (before after : Impact.Plan)
    (step : Impact.appendEffectWithActivity state
      (.readMap name destination keyTy valueTy key) (some condition) before =
      .ok after) :
    ∃ slot, ∃ alignedKey : Impact.Aligned, ∃ stored,
      after.operations = before.operations ++
        [.dup, .mapIndex slot alignedKey, stored] := by
  unfold Impact.appendEffectWithActivity at step
  simp only [bind_ok] at step
  rcases step with ⟨lowered, loweredAccepted, result, appendAccepted, wrapperAccepted⟩
  have effectShape : ∃ guardedKey : Expr keyTy,
      lowered = .readMap name destination keyTy valueTy guardedKey := by
    simp only [Pure.pure, Except.pure] at loweredAccepted
    cases loweredAccepted
    exact ⟨_, rfl⟩
  obtain ⟨guardedKey, rfl⟩ := effectShape
  obtain ⟨slot, alignedKey, stored, operationsShape⟩ :=
    appendEffect_readMap_operation_suffix state name destination keyTy valueTy _
      before result appendAccepted
  have wrappedOperations : after.operations = result.operations := by
    cases readFound : result.reads[before.reads.length]? with
    | none => simp [readFound] at wrapperAccepted
    | some read =>
      have projected := congrArg (Except.map Impact.Plan.operations) wrapperAccepted
      simp only [readFound, Pure.pure, Except.pure, Except.map] at projected
      exact (Except.ok.inj projected).symm
  exact ⟨slot, alignedKey, stored, wrappedOperations.trans operationsShape⟩

theorem appendEffectWithActivity_writeMap_operation_suffix
    (state : List StateDecl) (name : String) (keyTy valueTy : Ty)
    (key : Expr keyTy) (value : Expr valueTy) (condition : Expr .bool)
    (before after : Impact.Plan)
    (step : Impact.appendEffectWithActivity state
      (.writeMap name keyTy valueTy key value) (some condition) before =
      .ok after) :
    ∃ slot, ∃ keyPush : Impact.Op, ∃ stored,
      after.operations = before.operations ++
        [.index slot true, keyPush, stored, .insert 2] := by
  unfold Impact.appendEffectWithActivity at step
  simp only [bind_ok] at step
  rcases step with ⟨lowered, loweredAccepted, result, appendAccepted, wrapperAccepted⟩
  have effectShape : ∃ guardedKey : Expr keyTy, ∃ guardedValue : Expr valueTy,
      lowered = .writeMap name keyTy valueTy guardedKey guardedValue := by
    simp only [Pure.pure, Except.pure] at loweredAccepted
    cases loweredAccepted
    exact ⟨_, _, rfl⟩
  obtain ⟨guardedKey, guardedValue, rfl⟩ := effectShape
  obtain ⟨slot, keyPush, stored, operationsShape⟩ :=
    appendEffect_writeMap_operation_suffix state name keyTy valueTy _ _ before result
      appendAccepted
  have wrappedOperations : after.operations = result.operations := by
    have projected := congrArg (Except.map Impact.Plan.operations) wrapperAccepted
    simp only [Pure.pure, Except.pure, Except.map] at projected
    exact (Except.ok.inj projected).symm
  exact ⟨slot, keyPush, stored,
    wrappedOperations.trans operationsShape⟩

end Noctium.Verification.GuardedEffectPrefix
