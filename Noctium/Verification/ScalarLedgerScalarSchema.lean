import Noctium.Verification.GenericStateCircuitParts
import Noctium.Verification.ScalarNormalization

namespace Noctium.Verification.ScalarLedgerScalarSchema

open Backend Backend.Native ScalarNormalization

private theorem scalarType_nonforeign (ty : Ty) (supported : ScalarType ty) :
    ty.isForeign = false := by
  cases supported <;> rfl

private theorem scalarInputRequirement_type (input : Input)
    (supported : ScalarType input.ty) (requirement : InputRequirement)
    (member : requirement ∈ Input.requirements input) :
    requirement.ty = input.ty := by
  cases input with
  | mk name ty visibility span =>
    cases supported with
    | native =>
      simp only [Input.requirements] at member
      rw [List.mem_singleton.mp member]
    | bool =>
      simp only [Input.requirements] at member
      rw [List.mem_singleton.mp member]
    | uint width =>
      simp only [Input.requirements] at member
      rw [List.mem_singleton.mp member]

private theorem scalarCallArgumentRequirement_type (input : Input)
    (supported : ScalarType input.ty) (requirement : InputRequirement)
    (member : requirement ∈ Input.callArgumentRequirements input) :
    requirement.ty = input.ty := by
  cases input with
  | mk name ty visibility span =>
    cases supported with
    | native =>
      simp only [Input.callArgumentRequirements, Input.requirements] at member
      rw [List.mem_singleton.mp member]
    | bool =>
      simp only [Input.callArgumentRequirements, Input.requirements] at member
      rw [List.mem_singleton.mp member]
    | uint width =>
      simp only [Input.callArgumentRequirements, Input.requirements] at member
      rw [List.mem_singleton.mp member]

private theorem scalarPostReadDescriptor_nonforeign (name : String) (ty : Ty)
    (supported : ScalarType ty) :
    (match ty with
      | Ty.jubjubScalar =>
        ({identifier := "%input_" ++ name, visibility := .«public», ty := Ty.native,
          canonicalJubjubScalar := true} : InputRequirement)
      | Ty.opaqueBytes | Ty.opaqueString =>
        ({identifier := "%input_" ++ name, visibility := .«public», ty := Ty.native} : InputRequirement)
      | _ => ({identifier := "%input_" ++ name, visibility := .«public», ty} : InputRequirement)).ty.isForeign = false := by
  cases supported <;> rfl

/-- Accepted scalar circuit inputs and scalar post-public read bindings give
the exact nonforeign input schema required by scalar validation. -/
theorem accepted_nonforeign_input_schema (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan) (expected : Expected)
    (planAccepted : Impact.lower state entry = .ok plan)
    (expectedAccepted : Native.expectedEntrypoint state entry = .ok expected)
    (scalarInputs : ∀ input ∈ entry.circuit.inputs,
      Nonempty (ScalarType input.ty))
    (scalarReads : ∀ read ∈ plan.reads.drop
      (Impact.publicInputReadCount entry.circuit.inputs),
      ∀ name ty, (name, ty) ∈ read.bindings → Nonempty (ScalarType ty)) :
    ∀ requirement ∈ expected.rawInputs ++ expected.inputs,
      requirement.ty.isForeign = false := by
  intro requirement member
  rcases List.mem_append.mp member with rawMember | emittedMember
  · rw [GenericStateCircuitParts.expectedEntrypoint_rawInputs state entry expected
      expectedAccepted] at rawMember
    obtain ⟨input, argumentMember, requirementMember⟩ := List.mem_flatMap.mp rawMember
    unfold Entrypoint.callArguments at argumentMember
    obtain ⟨_, _, found⟩ := List.mem_filterMap.mp argumentMember
    have inputMember : input ∈ entry.circuit.inputs := List.mem_of_find?_eq_some found
    obtain ⟨supported⟩ := scalarInputs input inputMember
    have requirementType := scalarCallArgumentRequirement_type input supported
      requirement requirementMember
    rw [requirementType]
    exact scalarType_nonforeign input.ty supported
  · have coreMember : GenericStateCircuitParts.inputRequirementCore requirement ∈
        expected.inputs.map GenericStateCircuitParts.inputRequirementCore :=
      List.mem_map_of_mem emittedMember
    rw [GenericStateCircuitParts.expectedEntrypoint_inputRequirementCoreMap
      state entry expected plan expectedAccepted planAccepted] at coreMember
    obtain ⟨source, sourceMember, coreEq⟩ := List.mem_map.mp coreMember
    have requirementType : requirement.ty = source.ty := by
      have projection := congrArg
        (fun core : String × Visibility × Ty × Bool => core.2.2.1) coreEq
      simpa [GenericStateCircuitParts.inputRequirementCore] using projection.symm
    have sourceNonforeign : source.ty.isForeign = false := by
      unfold GenericStateCircuitParts.expectedInputRequirementSources at sourceMember
      rcases List.mem_append.mp sourceMember with circuitRequirement | readRequirement
      · unfold GenericStateCircuitParts.sourceInitialInputRequirements at circuitRequirement
        obtain ⟨input, filteredMember, requirementMember⟩ :=
          List.mem_flatMap.mp circuitRequirement
        have inputMember : input ∈ entry.circuit.inputs :=
          (List.mem_filter.mp filteredMember).1
        obtain ⟨supported⟩ := scalarInputs input inputMember
        have requirementType := scalarInputRequirement_type input supported
          source requirementMember
        rw [requirementType]
        exact scalarType_nonforeign input.ty supported
      · unfold GenericStateCircuitParts.sourcePostReadRequirements at readRequirement
        obtain ⟨read, readMember, bindingMember⟩ := List.mem_flatMap.mp readRequirement
        obtain ⟨pair, pairMember, sourceEq⟩ := List.mem_map.mp bindingMember
        rcases pair with ⟨name, ty⟩
        subst source
        obtain ⟨supported⟩ := scalarReads read readMember name ty pairMember
        exact scalarPostReadDescriptor_nonforeign name ty supported
    rw [requirementType]
    exact sourceNonforeign

end Noctium.Verification.ScalarLedgerScalarSchema
