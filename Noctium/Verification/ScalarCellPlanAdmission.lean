import Noctium.Verification.GenericStateAdmissionPrefix
import Noctium.Verification.GenericStateCellAdmission
import Noctium.Verification.GuardedEffectPrefix
import Noctium.Verification.ScalarAllocationOutputFrame
import Noctium.Verification.ScalarCellOperationAdmission
import Noctium.Verification.ScalarCellPlanScope
import Noctium.Verification.ScalarCellPublicAdmission

namespace Noctium.Verification.ScalarCellPlanAdmission

open Backend GenericStateCellAdmission GenericStateOps ScalarNormalization
open ScalarAllocationOutputFrame
open ScalarWitnessConstruction

private theorem guarded_cell_trace_operation_fields
    {state : List StateDecl} {guards : List (Option (Expr .bool))}
    {items : List (Effect × Nat)} {initial result : Impact.Plan} {offsets : List Nat}
    (guardsEmpty : guards = [])
    (source : ∀ item ∈ items, ScalarCellEffect state item.1)
    (operands : ∀ item ∈ items,
      ScalarCellSourceReads.ScalarCellOperand item.1)
    (trace : Impact.GuardedEffectTrace state guards items initial result offsets)
    (initialSupported : ∀ operation ∈ initial.operations, ScalarOperation operation)
    (initialFields : ∀ operation ∈ initial.operations, ∀ group ∈ operation.fieldGroups,
      ∀ field ∈ group, ScalarExpression field) :
    ∀ operation ∈ result.operations,
      ScalarOperation operation ∧
        ∀ group ∈ operation.fieldGroups, ∀ field ∈ group, ScalarExpression field := by
  induction trace with
  | nil plan =>
    intro operation member
    exact ⟨initialSupported operation member, initialFields operation member⟩
  | @cons item rest before next result offsets step tail ih =>
    have sourceHead : ScalarCellEffect state item.1 := source item (by simp)
    have operandHead : ScalarCellSourceReads.ScalarCellOperand item.1 :=
      operands item (by simp)
    have stepNone : Impact.appendEffectWithActivity state item.1 none before = .ok next := by
      simpa [guardsEmpty] using step
    obtain ⟨raw, rawAccepted, sameOperations, _⟩ :=
      GuardedEffectPrefix.appendEffectWithActivity_none_result
        state item.1 before next stepNone
    have rawSupported := append_cell_effect_scalar_supported state before raw item.1
      sourceHead rawAccepted initialSupported
    have rawFields := ScalarCellOperationAdmission.append_scalar_cell_fields_admitted
      state item.1 sourceHead operandHead before raw rawAccepted initialSupported initialFields
    have nextSupported : ∀ operation ∈ next.operations, ScalarOperation operation := by
      intro operation member
      rw [sameOperations] at member
      exact rawSupported operation member
    have nextFields : ∀ operation ∈ next.operations, ∀ group ∈ operation.fieldGroups,
        ∀ field ∈ group, ScalarExpression field := by
      intro operation member group groupMember field fieldMember
      rw [sameOperations] at member
      exact rawFields operation member group groupMember field fieldMember
    have tailSource : ∀ later ∈ rest, ScalarCellEffect state later.1 := by
      intro later member
      exact source later (List.mem_cons_of_mem item member)
    have tailOperands : ∀ later ∈ rest,
        ScalarCellSourceReads.ScalarCellOperand later.1 := by
      intro later member
      exact operands later (List.mem_cons_of_mem item member)
    exact ih tailSource tailOperands nextSupported nextFields

private theorem plain_scalar_read_no_defaults (read : Impact.Read)
    (plain : PlainScalarLedgerRead read) (scalarType : ScalarType read.ty) :
    read.inactiveDefaultConstraints = [] := by
  rcases read with ⟨name, ty, components, schema, guard, rootCellRead⟩
  rcases plain with ⟨componentsEmpty, unguarded⟩
  change components = [] at componentsEmpty
  change guard = none at unguarded
  subst components
  subst guard
  cases scalarType <;> rfl

/-- Accepted unguarded scalar-cell lowering produces every field admission
needed by the scalar ledger body. Public input compatibility admits the
prefix, admitted cell operands admit each source step, and returns stay explicit. -/
theorem lower_admission (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan)
    (accepted : Impact.lower state entry = .ok plan)
    (unguarded : entry.effectGuards = [])
    (compatible : ∀ input ∈ entry.circuit.inputs,
      Impact.publicInputScalarCompatible input)
    (cellEffects : ScalarCellSourceReads.ScalarCellEffects state entry.effects)
    (operands : ∀ effect ∈ entry.effects,
      ScalarCellSourceReads.ScalarCellOperand effect)
    (returns : ∀ output ∈ entry.returns,
      ∃ _scalarType : ScalarType output.ty, ScalarExpression output.value) :
    ScalarEntrypointPlanAdmission entry plan := by
  obtain ⟨_, inputPlan, _, inputAccepted, trace⟩ :=
    GenericStateAdmissionPrefix.lower_guarded_effect_trace state entry plan accepted
  have prefixSupported := GenericStateOps.publicInputPlan_scalar_supported
    entry.circuit.inputs {} inputPlan inputAccepted compatible (by simp)
  have prefixFields := ScalarCellPublicAdmission.publicInputPlan_fields_admitted
    entry.circuit.inputs inputPlan compatible inputAccepted
  have source : ∀ item ∈ entry.effects.zipIdx, ScalarCellEffect state item.1 := by
    intro item member
    apply cellEffects item.1
    rw [← List.zipIdx_map_fst 0 entry.effects]
    exact List.mem_map_of_mem member
  have sourceOperands : ∀ item ∈ entry.effects.zipIdx,
      ScalarCellSourceReads.ScalarCellOperand item.1 := by
    intro item member
    apply operands item.1
    rw [← List.zipIdx_map_fst 0 entry.effects]
    exact List.mem_map_of_mem member
  have planFields := guarded_cell_trace_operation_fields unguarded source sourceOperands
    trace prefixSupported prefixFields
  have planScope := ScalarCellPlanScope.lower_scope state entry plan accepted
    unguarded cellEffects
  have noSourceGuards := ScalarCellPlanScope.lower_guards_empty state entry plan
    accepted unguarded compatible cellEffects
  refine ⟨?_, ?_, ?_, ?_, ?_, returns⟩
  · intro read member scalarRead scalarMember guard selected
    have plain := planScope.2 read member
    have singleton : read.scalarReads = [read] := by
      simp [Impact.Read.scalarReads, plain.1.1]
    have same : scalarRead = read := by
      rw [singleton] at scalarMember
      exact List.mem_singleton.mp scalarMember
    subst scalarRead
    rw [plain.1.2] at selected
    cases selected
  · intro read member condition conditionMember
    obtain ⟨plain, ⟨scalarType⟩⟩ := planScope.2 read member
    have noDefaults := plain_scalar_read_no_defaults read plain scalarType
    rw [noDefaults] at conditionMember
    cases conditionMember
  · intro condition member
    exact False.elim (by rw [noSourceGuards] at member; cases member)
  · intro item member group groupMember field fieldMember
    exact (planFields item.1 (List.fst_mem_of_mem_zipIdx member)).2
      group groupMember field fieldMember
  · intro index guard selected
    have activity := planScope.1
    have present : some guard ∈ plan.activityGuards := List.mem_of_getElem? selected
    have noneSelected := (List.all_eq_true.mp activity) (some guard) present
    exact False.elim (by simp at noneSelected)

end Noctium.Verification.ScalarCellPlanAdmission
