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
  unfold Impact.appendEffectWithActivity at step
  simp only [bind_ok] at step
  rcases step with ⟨lowered, loweredAccepted, result, appendAccepted, wrapperAccepted⟩
  have effectShape : lowered = .readCell name destination ty := by
    change Except.ok (.readCell name destination ty) = Except.ok lowered at loweredAccepted
    exact (Except.ok.inj loweredAccepted).symm
  subst lowered
  obtain ⟨slot, value, operationsShape⟩ :=
    appendEffect_readCell_operation_suffix state name destination ty before result appendAccepted
  have wrappedOperations : after.operations = result.operations := by
    cases readFound : result.reads[before.reads.length]? with
    | none => simp [readFound] at wrapperAccepted
    | some read =>
      have projected := congrArg (Except.map Impact.Plan.operations) wrapperAccepted
      simp only [readFound, Pure.pure, Except.pure, Except.map] at projected
      exact (Except.ok.inj projected).symm
  exact ⟨slot, value, wrappedOperations.trans operationsShape⟩

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
