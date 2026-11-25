import Noctium.Verification.GenericStateOps
import Noctium.Verification.GenericStateAdmissionPrefix

namespace Noctium.Verification.GenericStateCellAdmission
open Backend

/-- Native, Bool and bounded UInt Cells lower to scalar VM operations. -/
inductive ScalarCellType : Ty → Type where
  | native : ScalarCellType .native
  | bool : ScalarCellType .bool
  | uint (maximum : Nat) (valid : maximum ≤ ScalarPolicy.maxUint) :
      ScalarCellType (.uint maximum)

/-- The state entry selected by `appendEffect` must be the exact unaligned Cell
declaration named by the source effect. -/
abbrev ScalarCellDeclaration := Impact.UnalignedCellDeclaration

theorem bytes32_cell_excluded : ScalarCellType (.bytes 32) → False := by
  intro cellType
  cases cellType

inductive ScalarCellEffect (state : List StateDecl) : Effect → Prop where
  | readCell (name destination : String) (ty : Ty) :
      ScalarCellType ty → ScalarCellDeclaration state name ty →
      ScalarCellEffect state (.readCell name destination ty)
  | writeCell (name : String) (ty : Ty) (value : Expr ty) :
      ScalarCellType ty → ScalarCellDeclaration state name ty →
      ScalarCellEffect state (.writeCell name ty value)

def scalarCellReadExpression : {ty : Ty} → ScalarCellType ty →
    String → Expr .native
  | _, .native, destination => .ref destination
  | _, .bool, destination => .cast .native (.ref destination : Expr .bool)
  | _, .uint maximum _, destination =>
      .cast .native (.ref destination : Expr (.uint maximum))

def scalarCellWriteExpression : {ty : Ty} → ScalarCellType ty →
    Expr ty → Expr .native
  | _, .native, value => value
  | _, .bool, value => .select value (.native 1) (.native 0)
  | _, .uint _ _, value => .cast .native value

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem append_three_supported (before : List Impact.Op)
    (first second third : Impact.Op)
    (beforeSupported : ∀ operation ∈ before, GenericStateOps.ScalarOperation operation)
    (firstSupported : GenericStateOps.ScalarOperation first)
    (secondSupported : GenericStateOps.ScalarOperation second)
    (thirdSupported : GenericStateOps.ScalarOperation third) :
    ∀ operation ∈ before ++ [first, second, third],
      GenericStateOps.ScalarOperation operation := by
  intro operation member
  rcases List.mem_append.mp member with old | added
  · exact beforeSupported operation old
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at added
    rcases added with rfl | rfl | rfl
    · exact firstSupported
    · exact secondSupported
    · exact thirdSupported

theorem append_read_cell_scalar_supported
    (state : List StateDecl) (plan next : Impact.Plan)
    (name destination : String) (ty : Ty)
    (scalar : ScalarCellType ty)
    (declaration : ScalarCellDeclaration state name ty)
    (accepted : Impact.appendEffect state (.readCell name destination ty) plan = .ok next)
    (previous : ∀ operation ∈ plan.operations,
      GenericStateOps.ScalarOperation operation) :
    ∃ slot, next.operations = plan.operations ++
      [.dup, .index slot, Impact.Op.popeq (.field
        (scalarCellReadExpression scalar destination))] ∧
      (∀ operation ∈ next.operations, GenericStateOps.ScalarOperation operation) := by
  cases scalar with
  | native =>
      simp only [Impact.appendEffect, bind_ok] at accepted
      rcases accepted with ⟨slot, slotAccepted, value, valueAccepted, resultAccepted⟩
      have valueShape : value = .popeq (.field (.ref destination)) := by
        change (Except.ok (.popeq (.field (.ref destination))) :
          Except String Impact.Op) = .ok value at valueAccepted
        exact (Except.ok.inj valueAccepted).symm
      have operationsShape : next.operations = plan.operations ++
          [.dup, .index slot, .popeq (.field (.ref destination))] := by
        simpa [valueShape] using
          (congrArg Impact.Plan.operations (Except.ok.inj resultAccepted)).symm
      refine ⟨slot, ?_, ?_⟩
      · simpa [scalarCellReadExpression] using operationsShape
      · rw [operationsShape]
        exact append_three_supported plan.operations .dup (.index slot)
          (.popeq (.field (.ref destination))) previous
          (by simp [GenericStateOps.ScalarOperation])
          (by simp [GenericStateOps.ScalarOperation])
          (by simp [GenericStateOps.ScalarOperation, GenericStateOps.ScalarAligned])
  | bool =>
      simp only [Impact.appendEffect, bind_ok] at accepted
      rcases accepted with ⟨slot, slotAccepted, value, valueAccepted, resultAccepted⟩
      have valueShape : value = .popeq
          (.field (.cast .native (.ref destination : Expr .bool))) := by
        change (Except.ok (.popeq
          (.field (.cast .native (.ref destination : Expr .bool))) : Impact.Op) :
          Except String Impact.Op) = .ok value at valueAccepted
        exact (Except.ok.inj valueAccepted).symm
      have operationsShape : next.operations = plan.operations ++
          [.dup, .index slot, .popeq
            (.field (.cast .native (.ref destination : Expr .bool)))] := by
        simpa [valueShape] using
          (congrArg Impact.Plan.operations (Except.ok.inj resultAccepted)).symm
      refine ⟨slot, ?_, ?_⟩
      · simpa [scalarCellReadExpression] using operationsShape
      · rw [operationsShape]
        exact append_three_supported plan.operations .dup (.index slot)
          (.popeq (.field (.cast .native (.ref destination : Expr .bool)))) previous
          (by simp [GenericStateOps.ScalarOperation])
          (by simp [GenericStateOps.ScalarOperation])
          (by simp [GenericStateOps.ScalarOperation, GenericStateOps.ScalarAligned])
  | uint maximum valid =>
      obtain ⟨slot, operationsShape⟩ :=
        Impact.appendEffect_unalignedUIntCell_read_shape state name destination maximum
          declaration plan next accepted
      refine ⟨slot, ?_, ?_⟩
      · simpa [scalarCellReadExpression] using operationsShape
      · rw [operationsShape]
        exact append_three_supported plan.operations .dup (.index slot)
          (.popeq (.field
            (.cast .native (.ref destination : Expr (.uint maximum))))) previous
          (by simp [GenericStateOps.ScalarOperation])
          (by simp [GenericStateOps.ScalarOperation])
          (by simp [GenericStateOps.ScalarOperation, GenericStateOps.ScalarAligned])

theorem append_write_cell_scalar_supported
    (state : List StateDecl) (plan next : Impact.Plan)
    (name : String) (ty : Ty) (value : Expr ty)
    (scalar : ScalarCellType ty)
    (declaration : ScalarCellDeclaration state name ty)
    (accepted : Impact.appendEffect state (.writeCell name ty value) plan = .ok next)
    (previous : ∀ operation ∈ plan.operations,
      GenericStateOps.ScalarOperation operation) :
    ∃ slot, next.operations = plan.operations ++
      [.push (.field (.native slot)),
        .push (.field (scalarCellWriteExpression scalar value)) true,
        .insert 1] ∧
      (∀ operation ∈ next.operations, GenericStateOps.ScalarOperation operation) := by
  cases scalar with
  | native =>
      simp only [Impact.appendEffect, bind_ok] at accepted
      rcases accepted with ⟨slot, slotAccepted, stored, storedAccepted, resultAccepted⟩
      have storedShape : stored = .push (.field value) true := by
        change (Except.ok (.push (.field value) true) :
          Except String Impact.Op) = .ok stored at storedAccepted
        exact (Except.ok.inj storedAccepted).symm
      have operationsShape : next.operations = plan.operations ++
          [.push (.field (.native slot)), .push (.field value) true, .insert 1] := by
        simpa [storedShape] using
          (congrArg Impact.Plan.operations (Except.ok.inj resultAccepted)).symm
      refine ⟨slot, ?_, ?_⟩
      · simpa [scalarCellWriteExpression] using operationsShape
      · rw [operationsShape]
        exact append_three_supported plan.operations
          (.push (.field (.native slot))) (.push (.field value) true) (.insert 1)
          previous
          (by simp [GenericStateOps.ScalarOperation, GenericStateOps.ScalarAligned])
          (by simp [GenericStateOps.ScalarOperation, GenericStateOps.ScalarAligned])
          (by simp [GenericStateOps.ScalarOperation])
  | bool =>
      simp only [Impact.appendEffect, bind_ok] at accepted
      rcases accepted with ⟨slot, slotAccepted, stored, storedAccepted, resultAccepted⟩
      have storedShape : stored =
          .push (.field (.select value (.native 1) (.native 0))) true := by
        change (Except.ok
          (.push (.field (.select value (.native 1) (.native 0))) true) :
          Except String Impact.Op) = .ok stored at storedAccepted
        exact (Except.ok.inj storedAccepted).symm
      have operationsShape : next.operations = plan.operations ++
          [.push (.field (.native slot)),
            .push (.field (.select value (.native 1) (.native 0))) true,
            .insert 1] := by
        simpa [storedShape] using
          (congrArg Impact.Plan.operations (Except.ok.inj resultAccepted)).symm
      refine ⟨slot, ?_, ?_⟩
      · simpa [scalarCellWriteExpression] using operationsShape
      · rw [operationsShape]
        exact append_three_supported plan.operations
          (.push (.field (.native slot)))
          (.push (.field (.select value (.native 1) (.native 0))) true)
          (.insert 1) previous
          (by simp [GenericStateOps.ScalarOperation, GenericStateOps.ScalarAligned])
          (by simp [GenericStateOps.ScalarOperation, GenericStateOps.ScalarAligned])
          (by simp [GenericStateOps.ScalarOperation])
  | uint maximum valid =>
      obtain ⟨slot, operationsShape⟩ :=
        Impact.appendEffect_unalignedUIntCell_write_shape state name maximum value
          declaration plan next accepted
      refine ⟨slot, ?_, ?_⟩
      · simpa [scalarCellWriteExpression] using operationsShape
      · rw [operationsShape]
        exact append_three_supported plan.operations
          (.push (.field (.native slot)))
          (.push (.field (.cast .native value)) true)
          (.insert 1) previous
          (by simp [GenericStateOps.ScalarOperation, GenericStateOps.ScalarAligned])
          (by simp [GenericStateOps.ScalarOperation, GenericStateOps.ScalarAligned])
          (by simp [GenericStateOps.ScalarOperation])

/-- Admits one typed source Cell read or write from its accepted lowering.
The specialized theorems retain the exact operation suffix for each source
effect. No interpreter evaluation is needed for this admission step. -/
theorem append_cell_effect_scalar_supported
    (state : List StateDecl) (plan next : Impact.Plan)
    (effect : Effect) (source : ScalarCellEffect state effect)
    (accepted : Impact.appendEffect state effect plan = .ok next)
    (previous : ∀ operation ∈ plan.operations,
      GenericStateOps.ScalarOperation operation) :
    ∀ operation ∈ next.operations, GenericStateOps.ScalarOperation operation := by
  cases source with
  | readCell name destination ty scalar declaration =>
    obtain ⟨_, _, supported⟩ := append_read_cell_scalar_supported state plan next
      name destination ty scalar declaration accepted previous
    exact supported
  | writeCell name ty value scalar declaration =>
    obtain ⟨_, _, supported⟩ := append_write_cell_scalar_supported state plan next
      name ty value scalar declaration accepted previous
    exact supported

theorem append_cell_effect_with_activity_scalar_supported
    (state : List StateDecl) (plan next : Impact.Plan)
    (effect : Effect) (guard : Option (Expr .bool))
    (source : ScalarCellEffect state effect)
    (accepted : Impact.appendEffectWithActivity state effect guard plan = .ok next)
    (previous : ∀ operation ∈ plan.operations,
      GenericStateOps.ScalarOperation operation) :
    ∀ operation ∈ next.operations, GenericStateOps.ScalarOperation operation := by
  cases source with
  | readCell name destination ty scalar declaration =>
    cases guard with
    | none =>
      unfold Impact.appendEffectWithActivity at accepted
      simp only [bind_ok] at accepted
      rcases accepted with ⟨lowered, loweredAccepted, result, appended, wrapped⟩
      have loweredShape : lowered = .readCell name destination ty := by
        simp only [Pure.pure, Except.pure] at loweredAccepted
        exact (Except.ok.inj loweredAccepted).symm
      subst lowered
      obtain ⟨_, _, supported⟩ :=
        append_read_cell_scalar_supported state plan result name destination ty
          scalar declaration appended previous
      have wrappedOperations : next.operations = result.operations := by
        have projected := congrArg (Except.map Impact.Plan.operations) wrapped
        simp only [Pure.pure, Except.pure, Except.map] at projected
        by_cases guardsEmpty : plan.activityGuards.isEmpty
        · simp [guardsEmpty] at projected
          exact projected.symm
        · simp [guardsEmpty] at projected
          exact projected.symm
      rw [wrappedOperations]
      exact supported
    | some condition =>
      unfold Impact.appendEffectWithActivity at accepted
      simp only [bind_ok] at accepted
      rcases accepted with ⟨lowered, loweredAccepted, result, appended, wrapped⟩
      have loweredShape : lowered = .readCell name destination ty := by
        simp only [Pure.pure, Except.pure] at loweredAccepted
        exact (Except.ok.inj loweredAccepted).symm
      subst lowered
      obtain ⟨_, _, supported⟩ :=
        append_read_cell_scalar_supported state plan result name destination ty
          scalar declaration appended previous
      have wrappedOperations : next.operations = result.operations := by
        cases readFound : result.reads[plan.reads.length]? with
        | none => simp [readFound] at wrapped
        | some read =>
          have projected := congrArg (Except.map Impact.Plan.operations) wrapped
          simp only [readFound, Pure.pure, Except.pure, Except.map] at projected
          exact (Except.ok.inj projected).symm
      rw [wrappedOperations]
      exact supported
  | writeCell name ty value scalar declaration =>
    cases guard with
    | none =>
      unfold Impact.appendEffectWithActivity at accepted
      simp only [bind_ok] at accepted
      rcases accepted with ⟨lowered, loweredAccepted, result, appended, wrapped⟩
      have loweredShape : ∃ storedValue, lowered = .writeCell name ty storedValue := by
        simp only [Pure.pure, Except.pure] at loweredAccepted
        exact ⟨value, (Except.ok.inj loweredAccepted).symm⟩
      obtain ⟨storedValue, rfl⟩ := loweredShape
      obtain ⟨_, _, supported⟩ :=
        append_write_cell_scalar_supported state plan result name ty storedValue
          scalar declaration appended previous
      have wrappedOperations : next.operations = result.operations := by
        have projected := congrArg (Except.map Impact.Plan.operations) wrapped
        simp only [Pure.pure, Except.pure, Except.map] at projected
        by_cases guardsEmpty : plan.activityGuards.isEmpty
        · simp [guardsEmpty] at projected
          exact projected.symm
        · simp [guardsEmpty] at projected
          exact projected.symm
      rw [wrappedOperations]
      exact supported
    | some condition =>
      unfold Impact.appendEffectWithActivity at accepted
      simp only [bind_ok] at accepted
      rcases accepted with ⟨lowered, loweredAccepted, result, appended, wrapped⟩
      have loweredShape : ∃ storedValue, lowered = .writeCell name ty storedValue := by
        simp only [Pure.pure, Except.pure] at loweredAccepted
        exact ⟨_, (Except.ok.inj loweredAccepted).symm⟩
      obtain ⟨storedValue, rfl⟩ := loweredShape
      obtain ⟨_, _, supported⟩ :=
        append_write_cell_scalar_supported state plan result name ty storedValue
          scalar declaration appended previous
      have wrappedOperations : next.operations = result.operations := by
        have projected := congrArg (Except.map Impact.Plan.operations) wrapped
        simp only [Pure.pure, Except.pure, Except.map] at projected
        exact (Except.ok.inj projected).symm
      rw [wrappedOperations]
      exact supported

private theorem guarded_cell_trace_supported {state : List StateDecl}
    {guards : List (Option (Expr .bool))}
    {items : List (Effect × Nat)} {initial result : Impact.Plan} {offsets : List Nat}
    (trace : Impact.GuardedEffectTrace state guards items initial result offsets)
    (source : ∀ item ∈ items, ScalarCellEffect state item.1)
    (initialSupported : ∀ operation ∈ initial.operations,
      GenericStateOps.ScalarOperation operation) :
    ∀ operation ∈ result.operations, GenericStateOps.ScalarOperation operation := by
  induction trace with
  | nil plan => exact initialSupported
  | @cons item rest before next result offsets step tail ih =>
    have nextSupported := append_cell_effect_with_activity_scalar_supported
      state before next item.1 (guards[item.2]?.getD none) (source item (by simp))
      step initialSupported
    exact ih (fun remaining member => source remaining (List.mem_cons_of_mem item member))
      nextSupported

/-- The actual lowering of scalar public inputs and Native or Bool Cell
effects stays in the scalar operation fragment, including guarded accesses.
Admission follows from source and lowering before interpreter evaluation. -/
theorem lower_scalar_cell_operations_supported (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan)
    (lowered : Impact.lower state entry = .ok plan)
    (compatible : ∀ input ∈ entry.circuit.inputs, Impact.publicInputScalarCompatible input)
    (effects : ∀ effect ∈ entry.effects, ScalarCellEffect state effect) :
    ∀ operation ∈ plan.operations, GenericStateOps.ScalarOperation operation := by
  obtain ⟨_, inputPlan, _, inputAccepted, trace⟩ :=
    GenericStateAdmissionPrefix.lower_guarded_effect_trace state entry plan lowered
  apply guarded_cell_trace_supported trace
  · intro item member
    apply effects item.1
    rw [← List.zipIdx_map_fst 0 entry.effects]
    exact List.mem_map_of_mem member
  · exact GenericStateOps.publicInputPlan_scalar_supported entry.circuit.inputs {}
      inputPlan inputAccepted compatible (by simp)

end Noctium.Verification.GenericStateCellAdmission
