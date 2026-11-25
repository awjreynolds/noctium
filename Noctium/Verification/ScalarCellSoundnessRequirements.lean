import Noctium.Verification.ScalarCellPlanScope
import Noctium.Verification.ScalarLedgerScalarSchema
import Noctium.Verification.ScalarWitnessCircuitInputs

namespace Noctium.Verification.ScalarCellSoundnessRequirements

open Backend Backend.Native ScalarNormalization
open ScalarWitnessConstruction

private theorem scalarInputRequirement_unguarded (input : Input)
    (supported : ScalarType input.ty) (requirement : InputRequirement)
    (member : requirement ∈ Input.requirements input) :
    requirement.activityGuard = none := by
  cases input with
  | mk name ty visibility span =>
    cases supported <;>
      simp only [Input.requirements, List.mem_singleton] at member <;>
      cases member <;> rfl

private theorem scalarSourceRequirements_unguarded (entry : Entrypoint)
    (plan : Impact.Plan)
    (scalarInputs : ∀ input ∈ entry.circuit.inputs, Nonempty (ScalarType input.ty))
    (scalarReads : ∀ read ∈
      plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
      PlainScalarLedgerRead read ∧ Nonempty (ScalarType read.ty)) :
    ∀ requirement ∈ GenericStateCircuitParts.expectedInputRequirementSources entry plan,
      requirement.activityGuard = none := by
  intro requirement member
  unfold GenericStateCircuitParts.expectedInputRequirementSources at member
  rcases List.mem_append.mp member with source | readSource
  · unfold GenericStateCircuitParts.sourceInitialInputRequirements at source
    obtain ⟨input, inputMember, requirementMember⟩ := List.mem_flatMap.mp source
    have circuitMember : input ∈ entry.circuit.inputs :=
      (List.mem_filter.mp inputMember).1
    obtain ⟨supported⟩ := scalarInputs input circuitMember
    exact scalarInputRequirement_unguarded input supported requirement requirementMember
  · unfold GenericStateCircuitParts.sourcePostReadRequirements at readSource
    obtain ⟨read, readMember, bindingMember⟩ := List.mem_flatMap.mp readSource
    obtain ⟨pair, pairMember, requirementEq⟩ := List.mem_map.mp bindingMember
    rcases pair with ⟨name, ty⟩
    subst requirement
    obtain ⟨plain, ⟨supported⟩⟩ := scalarReads read readMember
    rw [PlainScalarLedgerRead.bindings read plain supported] at pairMember
    simp only [List.mem_singleton] at pairMember
    rcases Prod.mk.inj pairMember with ⟨rfl, rfl⟩
    cases read with
    | mk readName readTy components schema guard rootCellRead =>
      cases supported <;> rfl

/-- Accepted scalar-cell plans produce unguarded public and private input
requirements in the exact Native expected-entrypoint metadata. -/
theorem accepted_scalar_cell_input_guards_none
    (state : List StateDecl) (entry : Entrypoint) (plan : Impact.Plan)
    (expected : Expected) (values : EvalEnv) (inputs : NativeRelation.Assignment)
    (planAccepted : Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan)
    (expectedAccepted : Native.expectedEntrypoint state
      (Passes.pruneEntrypoint entry) = .ok expected)
    (inputAdmission : CanonicalInputs entry.circuit values inputs)
    (unguarded : entry.effectGuards = [])
    (cellEffects : ScalarCellSourceReads.ScalarCellEffects state entry.effects) :
    ∀ requirement ∈ expected.inputs, requirement.activityGuard = none := by
  let ep := Passes.pruneEntrypoint entry
  have scalarInputs : ∀ input ∈ ep.circuit.inputs,
      Nonempty (ScalarType input.ty) := by
    intro input member
    have sourceMember : input ∈ entry.circuit.inputs := by
      simpa [ep, Passes.pruneEntrypoint, Passes.pruneCircuit] using member
    obtain ⟨value, _, canonical⟩ := inputAdmission.complete input sourceMember
    exact ⟨scalarTypeOfCanonicalInput canonical⟩
  obtain ⟨_, readFacts⟩ := ScalarCellPlanScope.lower_scope state ep plan
    planAccepted unguarded cellEffects
  have initialUnguarded := scalarSourceRequirements_unguarded ep plan
    scalarInputs readFacts
  have sources := GenericStateCircuitParts.expectedEntrypoint_inputs_of_unguarded_reads
    state ep expected plan expectedAccepted planAccepted
    (fun read member => (readFacts read member).1.2)
  intro requirement member
  rw [sources] at member
  exact initialUnguarded requirement member

/-- Scalar circuit input types and post-public scalar-cell reads satisfy the
nonforeign schema expected by strict ScalarCall validation. -/
theorem accepted_scalar_cell_nonforeign_input_schema
    (state : List StateDecl) (entry : Entrypoint) (plan : Impact.Plan)
    (expected : Expected) (values : EvalEnv) (inputs : NativeRelation.Assignment)
    (planAccepted : Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan)
    (expectedAccepted : Native.expectedEntrypoint state
      (Passes.pruneEntrypoint entry) = .ok expected)
    (inputAdmission : CanonicalInputs entry.circuit values inputs)
    (unguarded : entry.effectGuards = [])
    (cellEffects : ScalarCellSourceReads.ScalarCellEffects state entry.effects) :
    ∀ requirement ∈ expected.rawInputs ++ expected.inputs,
      requirement.ty.isForeign = false := by
  let ep := Passes.pruneEntrypoint entry
  have scalarInputs : ∀ input ∈ ep.circuit.inputs,
      Nonempty (ScalarType input.ty) := by
    intro input member
    have sourceMember : input ∈ entry.circuit.inputs := by
      simpa [ep, Passes.pruneEntrypoint, Passes.pruneCircuit] using member
    obtain ⟨value, _, canonical⟩ := inputAdmission.complete input sourceMember
    exact ⟨scalarTypeOfCanonicalInput canonical⟩
  obtain ⟨_, readFacts⟩ := ScalarCellPlanScope.lower_scope state ep plan
    planAccepted unguarded cellEffects
  have scalarReads : ∀ read ∈ plan.reads.drop
      (Impact.publicInputReadCount ep.circuit.inputs),
      ∀ name ty, (name, ty) ∈ read.bindings → Nonempty (ScalarType ty) := by
    intro read member name ty binding
    obtain ⟨plain, ⟨supported⟩⟩ := readFacts read member
    rw [PlainScalarLedgerRead.bindings read plain supported] at binding
    obtain ⟨sameName, sameType⟩ := Prod.mk.inj (List.mem_singleton.mp binding)
    subst ty
    exact ⟨supported⟩
  exact ScalarLedgerScalarSchema.accepted_nonforeign_input_schema state ep plan expected
    planAccepted expectedAccepted scalarInputs scalarReads

/-- Bundle the schema and input-guard requirements derived from the accepted
source inputs, scalar-cell effects, and exact Native lowering metadata. -/
theorem accepted_scalar_cell_soundness_requirements
    (state : List StateDecl) (entry : Entrypoint) (plan : Impact.Plan)
    (expected : Expected) (values : EvalEnv) (inputs : NativeRelation.Assignment)
    (planAccepted : Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan)
    (expectedAccepted : Native.expectedEntrypoint state
      (Passes.pruneEntrypoint entry) = .ok expected)
    (inputAdmission : CanonicalInputs entry.circuit values inputs)
    (unguarded : entry.effectGuards = [])
    (cellEffects : ScalarCellSourceReads.ScalarCellEffects state entry.effects) :
    (∀ requirement ∈ expected.rawInputs ++ expected.inputs,
      requirement.ty.isForeign = false) ∧
    (∀ requirement ∈ expected.inputs, requirement.activityGuard = none) := by
  exact ⟨accepted_scalar_cell_nonforeign_input_schema state entry plan expected values inputs
      planAccepted expectedAccepted inputAdmission unguarded cellEffects,
    accepted_scalar_cell_input_guards_none state entry plan expected values inputs
      planAccepted expectedAccepted inputAdmission unguarded cellEffects⟩

end Noctium.Verification.ScalarCellSoundnessRequirements
