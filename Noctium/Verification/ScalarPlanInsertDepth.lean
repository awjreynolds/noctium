import Noctium.Verification.ScalarGuardedPlanAdmission
import Noctium.Verification.GuardedEffectPrefix
import Noctium.Verification.GuardedRequireSemantics

namespace Noctium.Verification.ScalarPlanInsertDepth

open Backend GenericStateCellAdmission GenericStateMapOperations
  ScalarGuardedPlanAdmission

private def InsertDepthBound (operations : List Impact.Op) : Prop :=
  ∀ depth, Impact.Op.insert depth ∈ operations → depth < 16

private def ScalarOpsSupported (operations : List Impact.Op) : Prop :=
  ∀ operation ∈ operations, GenericStateOps.ScalarOperation operation

private theorem append_bounded_suffix (before suffix : List Impact.Op)
    (beforeBound : InsertDepthBound before)
    (suffixBound : InsertDepthBound suffix) :
    InsertDepthBound (before ++ suffix) := by
  intro depth member
  rcases List.mem_append.mp member with old | added
  · exact beforeBound depth old
  · exact suffixBound depth added

private theorem append_scalar_supported (before suffix : List Impact.Op)
    (beforeSupported : ScalarOpsSupported before)
    (suffixSupported : ScalarOpsSupported suffix) :
    ScalarOpsSupported (before ++ suffix) := by
  intro operation member
  rcases List.mem_append.mp member with old | added
  · exact beforeSupported operation old
  · exact suffixSupported operation added

private theorem public_input_plan_insert_depth_bound (inputs : List Input)
    (plan : Impact.Plan)
    (accepted : Impact.publicInputPlan inputs {} = .ok plan)
    (compatible : ∀ input ∈ inputs, Impact.publicInputScalarCompatible input) :
    InsertDepthBound plan.operations := by
  obtain ⟨values, shape⟩ := GenericStateAdmissionPrefix.publicInputPlan_pairs
    inputs plan accepted compatible
  intro depth member
  rw [shape] at member
  simp only [List.mem_flatMap] at member
  obtain ⟨value, _, member⟩ := member
  simp at member

private theorem cell_read_insert_depth_bound (state : List StateDecl)
    (before after : Impact.Plan) (name destination : String) (ty : Ty)
    (scalar : ScalarCellType ty) (declaration : ScalarCellDeclaration state name ty)
    (guard : Option (Expr .bool))
    (accepted : Impact.appendEffectWithActivity state
      (.readCell name destination ty) guard before = .ok after)
    (beforeBound : InsertDepthBound before.operations)
    (beforeSupported : ScalarOpsSupported before.operations) :
    InsertDepthBound after.operations ∧ ScalarOpsSupported after.operations := by
  obtain ⟨raw, appended, sameOperations⟩ :
      ∃ raw, Impact.appendEffect state (.readCell name destination ty) before = .ok raw ∧
        after.operations = raw.operations := by
    cases guard with
    | none =>
      obtain ⟨raw, appended, operations, _⟩ :=
        GuardedEffectPrefix.appendEffectWithActivity_none_result state
          (.readCell name destination ty) before after accepted
      exact ⟨raw, appended, operations⟩
    | some condition =>
      exact ScalarGuardedCellOperationAdmission.appendEffectWithActivity_readCell_raw
        state name destination ty condition before after accepted
  obtain ⟨_, shape, supported⟩ := append_read_cell_scalar_supported state before raw
    name destination ty scalar declaration appended beforeSupported
  constructor
  · rw [sameOperations, shape]
    apply append_bounded_suffix before.operations _ beforeBound
    intro depth member
    simp at member
  · rwa [sameOperations]

private theorem cell_write_insert_depth_bound (state : List StateDecl)
    (before after : Impact.Plan) (name : String) (ty : Ty) (value : Expr ty)
    (scalar : ScalarCellType ty) (declaration : ScalarCellDeclaration state name ty)
    (guard : Option (Expr .bool))
    (accepted : Impact.appendEffectWithActivity state
      (.writeCell name ty value) guard before = .ok after)
    (beforeBound : InsertDepthBound before.operations)
    (beforeSupported : ScalarOpsSupported before.operations) :
    InsertDepthBound after.operations ∧ ScalarOpsSupported after.operations := by
  obtain ⟨stored, raw, appended, sameOperations⟩ :
      ∃ (stored : Expr ty) (raw : Impact.Plan),
        Impact.appendEffect state (.writeCell name ty stored) before = .ok raw ∧
          after.operations = raw.operations := by
    cases guard with
    | none =>
      obtain ⟨raw, appended, operations, _⟩ :=
        GuardedEffectPrefix.appendEffectWithActivity_none_result state
          (.writeCell name ty value) before after accepted
      exact ⟨value, raw, appended, operations⟩
    | some condition =>
      obtain ⟨_, _, raw, appended, operations⟩ :=
        Impact.appendEffectWithActivity_writeCell_value
          state name ty value condition before after accepted
      exact ⟨_, raw, appended, operations⟩
  obtain ⟨_, shape, supported⟩ := append_write_cell_scalar_supported state before raw
    name ty stored scalar declaration appended beforeSupported
  constructor
  · rw [sameOperations, shape]
    apply append_bounded_suffix before.operations _ beforeBound
    intro depth member
    simp at member
    omega
  · rwa [sameOperations]

private theorem map_read_insert_depth_bound (state : List StateDecl)
    (before after : Impact.Plan) (name destination : String)
    (keyTy valueTy : Ty) (key : Expr keyTy)
    (keyScalar : ScalarCellType keyTy) (valueScalar : ScalarCellType valueTy)
    (guard : Option (Expr .bool))
    (accepted : Impact.appendEffectWithActivity state
      (.readMap name destination keyTy valueTy key) guard before = .ok after)
    (beforeBound : InsertDepthBound before.operations)
    (beforeSupported : ScalarOpsSupported before.operations) :
    InsertDepthBound after.operations ∧ ScalarOpsSupported after.operations := by
  obtain ⟨selected, raw, appended, sameOperations⟩ :
      ∃ (selected : Expr keyTy) (raw : Impact.Plan), Impact.appendEffect state
        (.readMap name destination keyTy valueTy selected) before = .ok raw ∧
          after.operations = raw.operations := by
    cases guard with
    | none =>
      obtain ⟨raw, appended, operations, _⟩ :=
        GuardedEffectPrefix.appendEffectWithActivity_none_result state
          (.readMap name destination keyTy valueTy key) before after accepted
      exact ⟨key, raw, appended, operations⟩
    | some condition =>
      have nonForeign : ∀ kind, keyTy ≠ .foreign kind := by
        intro kind
        cases keyScalar <;> simp
      obtain ⟨_, _, raw, appended, operations⟩ :=
        Impact.appendEffectWithActivity_readMap_key state name destination keyTy valueTy
          key condition before after nonForeign accepted
      exact ⟨_, raw, appended, operations⟩
  obtain ⟨_, shape, supported⟩ := append_read_map_scalar_supported state before raw name
    destination keyTy valueTy selected keyScalar valueScalar appended beforeSupported
  constructor
  · rw [sameOperations, shape]
    apply append_bounded_suffix before.operations _ beforeBound
    intro depth member
    simp at member
  · rwa [sameOperations]

private theorem map_write_insert_depth_bound (state : List StateDecl)
    (before after : Impact.Plan) (name : String) (keyTy valueTy : Ty)
    (key : Expr keyTy) (value : Expr valueTy)
    (keyScalar : ScalarCellType keyTy) (valueScalar : ScalarCellType valueTy)
    (guard : Option (Expr .bool))
    (accepted : Impact.appendEffectWithActivity state
      (.writeMap name keyTy valueTy key value) guard before = .ok after)
    (beforeBound : InsertDepthBound before.operations)
    (beforeSupported : ScalarOpsSupported before.operations) :
    InsertDepthBound after.operations ∧ ScalarOpsSupported after.operations := by
  obtain ⟨selected, stored, raw, appended, sameOperations⟩ :
      ∃ (selected : Expr keyTy) (stored : Expr valueTy) (raw : Impact.Plan),
        Impact.appendEffect state (.writeMap name keyTy valueTy selected stored) before = .ok raw ∧
          after.operations = raw.operations := by
    cases guard with
    | none =>
      obtain ⟨raw, appended, operations, _⟩ :=
        GuardedEffectPrefix.appendEffectWithActivity_none_result state
          (.writeMap name keyTy valueTy key value) before after accepted
      exact ⟨key, value, raw, appended, operations⟩
    | some condition =>
      have nonForeign : ∀ kind, keyTy ≠ .foreign kind := by
        intro kind
        cases keyScalar <;> simp
      obtain ⟨_, _, _, _, raw, appended, operations⟩ :=
        Impact.appendEffectWithActivity_writeMap_key_value state name keyTy valueTy
          key value condition before after nonForeign accepted
      exact ⟨_, _, raw, appended, operations⟩
  obtain ⟨_, shape, supported⟩ := append_write_map_scalar_supported state before raw name
    keyTy valueTy selected stored keyScalar valueScalar appended beforeSupported
  constructor
  · rw [sameOperations, shape]
    apply append_bounded_suffix before.operations _ beforeBound
    intro depth member
    simp at member
    omega
  · rwa [sameOperations]

private theorem require_insert_depth_bound (state : List StateDecl)
    (before after : Impact.Plan) (condition : Expr .bool)
    (guard : Option (Expr .bool))
    (accepted : Impact.appendEffectWithActivity state (.require condition) guard before =
      .ok after)
    (beforeBound : InsertDepthBound before.operations)
    (beforeSupported : ScalarOpsSupported before.operations) :
    InsertDepthBound after.operations ∧ ScalarOpsSupported after.operations := by
  cases guard with
  | none =>
    obtain ⟨raw, appended, sameOperations, _⟩ :=
      GuardedEffectPrefix.appendEffectWithActivity_none_result state
        (.require condition) before after accepted
    have rawOperations : raw.operations = before.operations := by
      simp only [Impact.appendEffect] at appended
      cases appended
      rfl
    rw [sameOperations, rawOperations]
    exact ⟨beforeBound, beforeSupported⟩
  | some gate =>
    have shape := GuardedRequireSemantics.appendEffectWithActivity_require_shape
      state gate condition before after accepted
    have sameOperations : after.operations = before.operations := by
      rw [shape]
    rw [sameOperations]
    exact ⟨beforeBound, beforeSupported⟩

private theorem requireAbsent_insert_depth_bound (state : List StateDecl)
    (before after : Impact.Plan) (name : String) (keyTy : Ty)
    (key : Expr keyTy) (keyScalar : ScalarCellType keyTy)
    (guard : Option (Expr .bool))
    (accepted : Impact.appendEffectWithActivity state
      (.requireAbsent name keyTy key) guard before = .ok after)
    (beforeBound : InsertDepthBound before.operations)
    (beforeSupported : ScalarOpsSupported before.operations) :
    InsertDepthBound after.operations ∧ ScalarOpsSupported after.operations := by
  cases guard with
  | none =>
    obtain ⟨slot, shape⟩ := ScalarRequireOperationAdmission.append_require_absent_operation_suffix
      state before after name keyTy key keyScalar accepted
    let suffix : List Impact.Op :=
      [.dup, .index slot,
        .push (.field (scalarCellWriteExpression keyScalar key)) false,
        .member, .popeq (.bit false)]
    have suffixShape : after.operations = before.operations ++ suffix := by
      simpa [suffix] using shape
    have suffixBound : InsertDepthBound suffix := by
      intro depth member
      simp [suffix] at member
    have suffixSupported : ScalarOpsSupported suffix := by
      intro operation member
      simp only [suffix, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with h | h | h | h | h <;> subst operation <;> trivial
    rw [suffixShape]
    exact ⟨append_bounded_suffix before.operations suffix beforeBound suffixBound,
      append_scalar_supported before.operations suffix beforeSupported suffixSupported⟩
  | some gate =>
    exact False.elim
      (ScalarRequireOperationAdmission.append_requireAbsent_guarded_rejected
        state name keyTy key gate before after accepted)

private theorem append_scalar_effect_insert_depth_bound (state : List StateDecl)
    (before after : Impact.Plan) (effect : Effect) (guard : Option (Expr .bool))
    (source : ScalarEffect state effect)
    (accepted : Impact.appendEffectWithActivity state effect guard before = .ok after)
    (beforeBound : InsertDepthBound before.operations)
    (beforeSupported : ScalarOpsSupported before.operations) :
    InsertDepthBound after.operations ∧ ScalarOpsSupported after.operations := by
  cases source with
  | cell effect source _ =>
    cases source with
    | readCell name destination ty scalar declaration =>
      exact cell_read_insert_depth_bound state before after name destination ty scalar
        declaration guard accepted beforeBound beforeSupported
    | writeCell name ty value scalar declaration =>
      exact cell_write_insert_depth_bound state before after name ty value scalar
        declaration guard accepted beforeBound beforeSupported
  | readMap name destination keyTy valueTy key keyScalar valueScalar _ =>
    exact map_read_insert_depth_bound state before after name destination keyTy valueTy key
      keyScalar valueScalar guard accepted beforeBound beforeSupported
  | writeMap name keyTy valueTy key value keyScalar valueScalar _ _ =>
    exact map_write_insert_depth_bound state before after name keyTy valueTy key value
      keyScalar valueScalar guard accepted beforeBound beforeSupported
  | require condition _ =>
    exact require_insert_depth_bound state before after condition guard accepted beforeBound
      beforeSupported
  | requireAbsent name keyTy key keyScalar _ =>
    exact requireAbsent_insert_depth_bound state before after name keyTy key keyScalar guard
      accepted beforeBound beforeSupported

private theorem guarded_trace_insert_depth_bound {state : List StateDecl}
    {guards : List (Option (Expr .bool))} {items : List (Effect × Nat)}
    {initial final : Impact.Plan} {offsets : List Nat}
    (trace : Impact.GuardedEffectTrace state guards items initial final offsets)
    (effects : ∀ item ∈ items, ScalarEffect state item.1)
    (initialBound : InsertDepthBound initial.operations)
    (initialSupported : ScalarOpsSupported initial.operations) :
    InsertDepthBound final.operations ∧ ScalarOpsSupported final.operations := by
  induction trace with
  | nil plan => exact ⟨initialBound, initialSupported⟩
  | @cons item rest before next final offsets step tail ih =>
    have nextInvariant := append_scalar_effect_insert_depth_bound state before next item.1
      (guards[item.2]?.getD none) (effects item (by simp)) step initialBound initialSupported
    exact ih (fun remaining member =>
      effects remaining (List.mem_cons_of_mem item member)) nextInvariant.1 nextInvariant.2

/-- Every insert emitted by accepted guarded scalar lowering has the fixed
Cell or Map depth. The public-input prefix and each accepted effect append
remain tied to the exact production lowering result. -/
theorem lower_inserts_fit (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan) (lowered : Impact.lower state entry = .ok plan)
    (compatible : ∀ input ∈ entry.circuit.inputs,
      Impact.publicInputScalarCompatible input)
    (effects : ∀ effect ∈ entry.effects, ScalarEffect state effect) :
    ∀ depth, Impact.Op.insert depth ∈ plan.operations → depth < 16 := by
  obtain ⟨_, inputPlan, _, inputAccepted, trace⟩ :=
    GenericStateAdmissionPrefix.lower_guarded_effect_trace state entry plan lowered
  have inputBound := public_input_plan_insert_depth_bound entry.circuit.inputs inputPlan
    inputAccepted compatible
  have inputSupported := GenericStateOps.publicInputPlan_scalar_supported
    entry.circuit.inputs {} inputPlan inputAccepted compatible (by intro op member; simp at member)
  have traceEffects : ∀ item ∈ entry.effects.zipIdx, ScalarEffect state item.1 := by
    intro item member
    apply effects item.1
    rw [← List.zipIdx_map_fst 0 entry.effects]
    exact List.mem_map_of_mem member
  have finalInvariant := guarded_trace_insert_depth_bound trace traceEffects
    inputBound inputSupported
  exact finalInvariant.1

end Noctium.Verification.ScalarPlanInsertDepth
