import Noctium.Verification.GenericStateCheckedReadTrace

namespace Noctium.Verification.GuardedEffectChunkShape
open Backend
open GenericStateCheckedReadTrace

private theorem append_nonempty_suffix_ne_self {α : Type} (base suffix : List α)
    (nonempty : 0 < suffix.length) : base ++ suffix ≠ base := by
  intro same
  have lengths := congrArg List.length same
  simp only [List.length_append] at lengths
  omega

/-- An accepted guarded scalar effect that leaves the operation list unchanged
must be a source requirement. Guarded reads and writes append nonempty chunks
in the production lowering. -/
theorem guarded_empty_effect_is_require
    (state : List StateDecl) (effect : Effect) (guard : Expr .bool)
    (scope : GuardedScalarReadEffect (some guard) effect)
    (before after : Impact.Plan)
    (accepted : Impact.appendEffectWithActivity state effect (some guard) before =
      .ok after)
    (operationsUnchanged : after.operations = before.operations) :
    ∃ required : Expr .bool, effect = .require required := by
  cases scope with
  | require =>
    rename_i required
    exact ⟨required, rfl⟩
  | readCell =>
    rename_i name destination ty
    obtain ⟨slot, value, operationsShape⟩ :=
      GuardedEffectPrefix.appendEffectWithActivity_readCell_operation_suffix
        state name destination ty guard before after accepted
    have sameAppend : before.operations ++ [.dup, .index slot, value] = before.operations := by
      calc
        before.operations ++ [.dup, .index slot, value] = after.operations :=
          operationsShape.symm
        _ = before.operations := operationsUnchanged
    have impossible := append_nonempty_suffix_ne_self before.operations
      [.dup, .index slot, value] (by simp) sameAppend
    exact False.elim impossible
  | readMap =>
    rename_i name destination keyTy valueTy key
    obtain ⟨slot, alignedKey, stored, operationsShape⟩ :=
      GuardedEffectPrefix.appendEffectWithActivity_readMap_operation_suffix
        state name destination keyTy valueTy key guard before after accepted
    have sameAppend : before.operations ++
        [.dup, .mapIndex slot alignedKey, stored] = before.operations := by
      calc
        before.operations ++ [.dup, .mapIndex slot alignedKey, stored] =
            after.operations := operationsShape.symm
        _ = before.operations := operationsUnchanged
    have impossible := append_nonempty_suffix_ne_self before.operations
      [.dup, .mapIndex slot alignedKey, stored] (by simp) sameAppend
    exact False.elim impossible
  | writeCell =>
    rename_i name ty value
    obtain ⟨slot, stored, operationsShape⟩ :=
      GuardedEffectPrefix.appendEffectWithActivity_writeCell_operation_suffix
        state name ty value guard before after accepted
    have sameAppend : before.operations ++
        [.push (.field (.native slot)), stored, .insert 1] = before.operations := by
      calc
        before.operations ++
            [.push (.field (.native slot)), stored, .insert 1] = after.operations :=
          operationsShape.symm
        _ = before.operations := operationsUnchanged
    have impossible := append_nonempty_suffix_ne_self before.operations
      [.push (.field (.native slot)), stored, .insert 1] (by simp) sameAppend
    exact False.elim impossible
  | writeMap =>
    rename_i name keyTy valueTy key value
    obtain ⟨slot, keyPush, stored, operationsShape⟩ :=
      GuardedEffectPrefix.appendEffectWithActivity_writeMap_operation_suffix
        state name keyTy valueTy key value guard before after accepted
    have sameAppend : before.operations ++
        [.index slot true, keyPush, stored, .insert 2] = before.operations := by
      calc
        before.operations ++
            [.index slot true, keyPush, stored, .insert 2] = after.operations :=
          operationsShape.symm
        _ = before.operations := operationsUnchanged
    have impossible := append_nonempty_suffix_ne_self before.operations
      [.index slot true, keyPush, stored, .insert 2] (by simp) sameAppend
    exact False.elim impossible

end Noctium.Verification.GuardedEffectChunkShape
