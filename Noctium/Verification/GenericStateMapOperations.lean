import Noctium.Verification.GenericStateCellAdmission

namespace Noctium.Verification.GenericStateMapOperations

open Backend GenericStateCellAdmission

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem append_suffix_supported (before suffix : List Impact.Op)
    (previous : ∀ operation ∈ before, GenericStateOps.ScalarOperation operation)
    (suffixSupported : ∀ operation ∈ suffix, GenericStateOps.ScalarOperation operation) :
    ∀ operation ∈ before ++ suffix, GenericStateOps.ScalarOperation operation := by
  intro operation member
  rcases List.mem_append.mp member with old | added
  · exact previous operation old
  · exact suffixSupported operation added

/-- An accepted plain Map read appends exactly the scalar key lookup and
destination projection represented by its key and value witnesses. -/
theorem append_read_map_scalar_supported (state : List StateDecl)
    (before after : Impact.Plan) (name destination : String)
    (keyTy valueTy : Ty) (key : Expr keyTy)
    (keyScalar : ScalarCellType keyTy) (valueScalar : ScalarCellType valueTy)
    (accepted : Impact.appendEffect state
      (.readMap name destination keyTy valueTy key) before = .ok after)
    (previous : ∀ operation ∈ before.operations,
      GenericStateOps.ScalarOperation operation) :
    ∃ slot, after.operations = before.operations ++
      [.dup,
        .mapIndex slot (.field (scalarCellWriteExpression keyScalar key)),
        .popeq (.field (scalarCellReadExpression valueScalar destination))] ∧
      (∀ operation ∈ after.operations, GenericStateOps.ScalarOperation operation) := by
  simp only [Impact.appendEffect, bind_ok] at accepted
  rcases accepted with ⟨slot, slotAccepted, alignedKey, keyAccepted,
    stored, storedAccepted, resultAccepted⟩
  have keyShape : alignedKey = .field (scalarCellWriteExpression keyScalar key) := by
    cases keyScalar with
    | native =>
      change (Except.ok (.field key) : Except String Impact.Aligned) = .ok alignedKey
        at keyAccepted
      exact (Except.ok.inj keyAccepted).symm
    | bool =>
      change (Except.ok (.field (.select key (.native 1) (.native 0))) :
        Except String Impact.Aligned) = .ok alignedKey at keyAccepted
      exact (Except.ok.inj keyAccepted).symm
    | uint maximum valid =>
      change (Except.ok (.field (.cast .native key)) : Except String Impact.Aligned) =
        .ok alignedKey at keyAccepted
      exact (Except.ok.inj keyAccepted).symm
  have storedShape : stored =
      .popeq (.field (scalarCellReadExpression valueScalar destination)) := by
    cases valueScalar with
    | native =>
      change (Except.ok (.popeq (.field (.ref destination))) :
        Except String Impact.Op) = .ok stored at storedAccepted
      exact (Except.ok.inj storedAccepted).symm
    | bool =>
      change (Except.ok (.popeq
        (.field (.cast .native (.ref destination : Expr .bool))) : Impact.Op) :
        Except String Impact.Op) = .ok stored at storedAccepted
      exact (Except.ok.inj storedAccepted).symm
    | uint maximum valid =>
      change (Except.ok (.popeq
        (.field (.cast .native (.ref destination : Expr (.uint maximum)))) : Impact.Op) :
        Except String Impact.Op) = .ok stored at storedAccepted
      exact (Except.ok.inj storedAccepted).symm
  have operationsShape : after.operations = before.operations ++
      [.dup,
        .mapIndex slot (.field (scalarCellWriteExpression keyScalar key)),
        .popeq (.field (scalarCellReadExpression valueScalar destination))] := by
    rw [keyShape, storedShape] at resultAccepted
    change (Except.ok ({before with
      operations := before.operations ++
        [.dup,
          .mapIndex slot (.field (scalarCellWriteExpression keyScalar key)),
          .popeq (.field (scalarCellReadExpression valueScalar destination))]
      reads := before.reads ++ [{name := destination, ty := valueTy}]} : Impact.Plan)) =
        .ok after at resultAccepted
    cases resultAccepted
    rfl
  have suffixSupported : ∀ operation ∈
      [.dup,
        .mapIndex slot (.field (scalarCellWriteExpression keyScalar key)),
        .popeq (.field (scalarCellReadExpression valueScalar destination))],
      GenericStateOps.ScalarOperation operation := by
    intro operation member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with first | second | third
    · cases first
      simp [GenericStateOps.ScalarOperation]
    · cases second
      simp [GenericStateOps.ScalarOperation]
    · cases third
      simp [GenericStateOps.ScalarOperation, GenericStateOps.ScalarAligned]
  refine ⟨slot, operationsShape, ?_⟩
  rw [operationsShape]
  exact append_suffix_supported before.operations _ previous suffixSupported

/-- An accepted plain Map write appends its scalar key, scalar value, and
insertion operations in source order. -/
theorem append_write_map_scalar_supported (state : List StateDecl)
    (before after : Impact.Plan) (name : String)
    (keyTy valueTy : Ty) (key : Expr keyTy) (value : Expr valueTy)
    (keyScalar : ScalarCellType keyTy) (valueScalar : ScalarCellType valueTy)
    (accepted : Impact.appendEffect state
      (.writeMap name keyTy valueTy key value) before = .ok after)
    (previous : ∀ operation ∈ before.operations,
      GenericStateOps.ScalarOperation operation) :
    ∃ slot, after.operations = before.operations ++
      [.index slot true,
        .push (.field (scalarCellWriteExpression keyScalar key)) false,
        .push (.field (scalarCellWriteExpression valueScalar value)) true,
        .insert 2] ∧
      (∀ operation ∈ after.operations, GenericStateOps.ScalarOperation operation) := by
  simp only [Impact.appendEffect, bind_ok] at accepted
  rcases accepted with ⟨slot, slotAccepted, alignedKey, keyAccepted,
    stored, storedAccepted, resultAccepted⟩
  have alignedKeyShape : alignedKey =
      .field (scalarCellWriteExpression keyScalar key) := by
    cases keyScalar with
    | native =>
      change (Except.ok (.field key) : Except String Impact.Aligned) =
        .ok alignedKey at keyAccepted
      exact (Except.ok.inj keyAccepted).symm
    | bool =>
      change (Except.ok (.field (.select key (.native 1) (.native 0))) :
        Except String Impact.Aligned) = .ok alignedKey at keyAccepted
      exact (Except.ok.inj keyAccepted).symm
    | uint maximum valid =>
      change (Except.ok (.field (.cast .native key)) : Except String Impact.Aligned) =
        .ok alignedKey at keyAccepted
      exact (Except.ok.inj keyAccepted).symm
  have storedShape : stored =
      .push (.field (scalarCellWriteExpression valueScalar value)) true := by
    cases valueScalar with
    | native =>
      change (Except.ok (.push (.field value) true) : Except String Impact.Op) =
        .ok stored at storedAccepted
      exact (Except.ok.inj storedAccepted).symm
    | bool =>
      change (Except.ok (.push
        (.field (.select value (.native 1) (.native 0))) true) : Except String Impact.Op) =
        .ok stored at storedAccepted
      exact (Except.ok.inj storedAccepted).symm
    | uint maximum valid =>
      change (Except.ok (.push (.field (.cast .native value)) true) :
        Except String Impact.Op) = .ok stored at storedAccepted
      exact (Except.ok.inj storedAccepted).symm
  have operationsShape : after.operations = before.operations ++
      [.index slot true,
        .push (.field (scalarCellWriteExpression keyScalar key)) false,
        .push (.field (scalarCellWriteExpression valueScalar value)) true,
        .insert 2] := by
    rw [alignedKeyShape, storedShape] at resultAccepted
    change (Except.ok ({before with operations := before.operations ++
      [.index slot true,
        .push (.field (scalarCellWriteExpression keyScalar key)) false,
        .push (.field (scalarCellWriteExpression valueScalar value)) true,
        .insert 2]} : Impact.Plan)) = .ok after at resultAccepted
    cases resultAccepted
    rfl
  have suffixSupported : ∀ operation ∈
      [.index slot true,
        .push (.field (scalarCellWriteExpression keyScalar key)) false,
        .push (.field (scalarCellWriteExpression valueScalar value)) true,
        .insert 2], GenericStateOps.ScalarOperation operation := by
    intro operation member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with first | second | third | fourth
    · cases first
      simp [GenericStateOps.ScalarOperation]
    · cases second
      simp [GenericStateOps.ScalarOperation, GenericStateOps.ScalarAligned]
    · cases third
      simp [GenericStateOps.ScalarOperation, GenericStateOps.ScalarAligned]
    · cases fourth
      simp [GenericStateOps.ScalarOperation]
  refine ⟨slot, operationsShape, ?_⟩
  rw [operationsShape]
  exact append_suffix_supported before.operations _ previous suffixSupported

private theorem appendEffectWithActivity_none_raw (state : List StateDecl)
    (effect : Effect) (before after : Impact.Plan)
    (accepted : Impact.appendEffectWithActivity state effect none before = .ok after) :
    ∃ raw, Impact.appendEffect state effect before = .ok raw ∧
      after.operations = raw.operations := by
  unfold Impact.appendEffectWithActivity at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨lowered, loweredAccepted, raw, appended, wrapped⟩
  have loweredShape : lowered = effect := by
    simp only [Pure.pure, Except.pure] at loweredAccepted
    exact (Except.ok.inj loweredAccepted).symm
  subst lowered
  have sameOperations : after.operations = raw.operations := by
    have projected := congrArg (Except.map Impact.Plan.operations) wrapped
    simp only [Pure.pure, Except.pure, Except.map] at projected
    by_cases guardsEmpty : before.activityGuards.isEmpty
    · simp [guardsEmpty] at projected
      exact projected.symm
    · simp [guardsEmpty] at projected
      exact projected.symm
  exact ⟨raw, appended, sameOperations⟩

/-- Accepted guarded and unguarded plain Map reads retain the scalar operation
fragment. Guarded reads use Impact's accepted totalized key append. -/
theorem append_read_map_with_activity_scalar_supported (state : List StateDecl)
    (before after : Impact.Plan) (name destination : String)
    (keyTy valueTy : Ty) (key : Expr keyTy) (guard : Option (Expr .bool))
    (keyScalar : ScalarCellType keyTy) (valueScalar : ScalarCellType valueTy)
    (accepted : Impact.appendEffectWithActivity state
      (.readMap name destination keyTy valueTy key) guard before = .ok after)
    (previous : ∀ operation ∈ before.operations,
      GenericStateOps.ScalarOperation operation) :
    ∀ operation ∈ after.operations, GenericStateOps.ScalarOperation operation := by
  cases guard with
  | none =>
    obtain ⟨raw, appended, sameOperations⟩ := appendEffectWithActivity_none_raw state
      (.readMap name destination keyTy valueTy key) before after accepted
    obtain ⟨_, _, supported⟩ := append_read_map_scalar_supported state before raw
      name destination keyTy valueTy key keyScalar valueScalar appended previous
    rw [sameOperations]
    exact supported
  | some condition =>
    have keyNonForeign : ∀ kind, keyTy ≠ .foreign kind := by
      cases keyScalar <;> simp
    obtain ⟨binder, _, raw, appended, sameOperations⟩ :=
      Impact.appendEffectWithActivity_readMap_key state name destination keyTy valueTy
        key condition before after keyNonForeign accepted
    let emittedKey : Expr keyTy :=
      .letE binder condition (Noctium.GuardedExpression.totalize (.ref binder) key)
    obtain ⟨_, _, supported⟩ := append_read_map_scalar_supported state before raw
      name destination keyTy valueTy emittedKey keyScalar valueScalar appended previous
    rw [sameOperations]
    exact supported

/-- Accepted guarded and unguarded plain Map writes retain the scalar operation
fragment. Guarded writes use Impact's accepted totalized key and value append. -/
theorem append_write_map_with_activity_scalar_supported (state : List StateDecl)
    (before after : Impact.Plan) (name : String)
    (keyTy valueTy : Ty) (key : Expr keyTy) (value : Expr valueTy)
    (guard : Option (Expr .bool))
    (keyScalar : ScalarCellType keyTy) (valueScalar : ScalarCellType valueTy)
    (accepted : Impact.appendEffectWithActivity state
      (.writeMap name keyTy valueTy key value) guard before = .ok after)
    (previous : ∀ operation ∈ before.operations,
      GenericStateOps.ScalarOperation operation) :
    ∀ operation ∈ after.operations, GenericStateOps.ScalarOperation operation := by
  cases guard with
  | none =>
    obtain ⟨raw, appended, sameOperations⟩ := appendEffectWithActivity_none_raw state
      (.writeMap name keyTy valueTy key value) before after accepted
    obtain ⟨_, _, supported⟩ := append_write_map_scalar_supported state before raw
      name keyTy valueTy key value keyScalar valueScalar appended previous
    rw [sameOperations]
    exact supported
  | some condition =>
    have keyNonForeign : ∀ kind, keyTy ≠ .foreign kind := by
      cases keyScalar <;> simp
    obtain ⟨keyBinder, _, valueBinder, _, raw, appended, sameOperations⟩ :=
      Impact.appendEffectWithActivity_writeMap_key_value state name keyTy valueTy
        key value condition before after keyNonForeign accepted
    let emittedKey : Expr keyTy :=
      .letE keyBinder condition
        (Noctium.GuardedExpression.totalize (.ref keyBinder) key)
    let emittedValue : Expr valueTy :=
      .letE valueBinder condition
        (Noctium.GuardedExpression.totalize (.ref valueBinder) value)
    obtain ⟨_, _, supported⟩ := append_write_map_scalar_supported state before raw
      name keyTy valueTy emittedKey emittedValue keyScalar valueScalar appended previous
    rw [sameOperations]
    exact supported

end Noctium.Verification.GenericStateMapOperations
