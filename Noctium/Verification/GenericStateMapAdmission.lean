import Noctium.Verification.GenericStateMapOperations

namespace Noctium.Verification.GenericStateMapAdmission

open Backend
open GenericStateCellAdmission (ScalarCellEffect ScalarCellType)

/-- Effects whose storage alignments have a representation in the scalar VM. -/
inductive ScalarCellOrMapEffect (state : List StateDecl) : Effect → Prop where
  | cell (effect : Effect) : ScalarCellEffect state effect →
      ScalarCellOrMapEffect state effect
  | readMap (name destination : String) (keyTy valueTy : Ty) (key : Expr keyTy) :
      ScalarCellType keyTy → ScalarCellType valueTy →
      ScalarCellOrMapEffect state (.readMap name destination keyTy valueTy key)
  | writeMap (name : String) (keyTy valueTy : Ty) (key : Expr keyTy) (value : Expr valueTy) :
      ScalarCellType keyTy → ScalarCellType valueTy →
      ScalarCellOrMapEffect state (.writeMap name keyTy valueTy key value)

private theorem append_scalar_effect_supported
    (state : List StateDecl) (before after : Impact.Plan) (effect : Effect)
    (guard : Option (Expr .bool)) (source : ScalarCellOrMapEffect state effect)
    (accepted : Impact.appendEffectWithActivity state effect guard before = .ok after)
    (previous : ∀ operation ∈ before.operations, GenericStateOps.ScalarOperation operation) :
    ∀ operation ∈ after.operations, GenericStateOps.ScalarOperation operation := by
  cases source with
  | cell effect cell =>
    exact GenericStateCellAdmission.append_cell_effect_with_activity_scalar_supported
      state before after effect guard cell accepted previous
  | readMap name destination keyTy valueTy key keyScalar valueScalar =>
    exact GenericStateMapOperations.append_read_map_with_activity_scalar_supported
      state before after name destination keyTy valueTy key guard keyScalar valueScalar
      accepted previous
  | writeMap name keyTy valueTy key value keyScalar valueScalar =>
    exact GenericStateMapOperations.append_write_map_with_activity_scalar_supported
      state before after name keyTy valueTy key value guard keyScalar valueScalar
      accepted previous

private theorem guarded_trace_supported {state : List StateDecl}
    {guards : List (Option (Expr .bool))} {items : List (Effect × Nat)}
    {initial final : Impact.Plan} {offsets : List Nat}
    (trace : Impact.GuardedEffectTrace state guards items initial final offsets)
    (source : ∀ item ∈ items, ScalarCellOrMapEffect state item.1)
    (initialSupported : ∀ operation ∈ initial.operations,
      GenericStateOps.ScalarOperation operation) :
    ∀ operation ∈ final.operations, GenericStateOps.ScalarOperation operation := by
  induction trace with
  | nil plan => exact initialSupported
  | @cons item rest before next final offsets step tail ih =>
    have nextSupported := append_scalar_effect_supported state before next item.1
      (guards[item.2]?.getD none) (source item (by simp)) step initialSupported
    exact ih (fun remaining member => source remaining (List.mem_cons_of_mem item member))
      nextSupported

/-- The checked production lowerer emits only scalar VM operations for this
Cell and plain Map fragment. This follows from the accepted public-input
prefix and each guarded effect step, before any interpreter evaluation. -/
theorem lower_scalar_cell_or_map_operations_supported (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan)
    (lowered : Impact.lower state entry = .ok plan)
    (compatible : ∀ input ∈ entry.circuit.inputs, Impact.publicInputScalarCompatible input)
    (effects : ∀ effect ∈ entry.effects, ScalarCellOrMapEffect state effect) :
    ∀ operation ∈ plan.operations, GenericStateOps.ScalarOperation operation := by
  obtain ⟨_, inputPlan, _, inputAccepted, trace⟩ :=
    GenericStateAdmissionPrefix.lower_guarded_effect_trace state entry plan lowered
  apply guarded_trace_supported trace
  · intro item member
    apply effects item.1
    rw [← List.zipIdx_map_fst 0 entry.effects]
    exact List.mem_map_of_mem member
  · exact GenericStateOps.publicInputPlan_scalar_supported entry.circuit.inputs {}
      inputPlan inputAccepted compatible (by simp)

end Noctium.Verification.GenericStateMapAdmission
