import Noctium.Verification.GenericStateCircuitParts
import Noctium.Verification.GenericStateEffectValidation
import Noctium.Verification.GenericStateKeys
import Noctium.Verification.NativeRelationJson
import Noctium.Verification.ScalarNormalization

namespace Noctium.Verification.ScalarLedgerSourceIdentifiers

open Backend Backend.Native NativeRelationJson ScalarNormalization

private def scalarSourceInputRequirement (input : Input) : InputRequirement :=
  {identifier := "%input_" ++ input.name, visibility := input.visibility, ty := input.ty}

private theorem scalarSourceInputRequirement_members (input : Input)
    (scalarType : ScalarType input.ty) :
    scalarSourceInputRequirement input ∈ Input.requirements input ∧
      scalarSourceInputRequirement input ∈ Input.callArgumentRequirements input := by
  cases input with
  | mk name ty visibility span =>
    cases scalarType <;>
      simp [scalarSourceInputRequirement, Input.requirements, Input.callArgumentRequirements]

private theorem scalarInputRequirement_sourcePrefix (input : Input)
    (scalarType : ScalarType input.ty) (requirement : InputRequirement)
    (member : requirement ∈ Input.requirements input) :
    ∃ name, requirement.identifier = "%input_" ++ name := by
  cases input with
  | mk name ty visibility span =>
    cases scalarType with
    | native =>
      simp only [Input.requirements] at member
      rcases List.mem_singleton.mp member with rfl
      exact ⟨name, rfl⟩
    | bool =>
      simp only [Input.requirements] at member
      rcases List.mem_singleton.mp member with rfl
      exact ⟨name, rfl⟩
    | uint width =>
      simp only [Input.requirements] at member
      rcases List.mem_singleton.mp member with rfl
      exact ⟨name, rfl⟩

private theorem scalarCallArgumentRequirement_sourcePrefix (input : Input)
    (scalarType : ScalarType input.ty) (requirement : InputRequirement)
    (member : requirement ∈ Input.callArgumentRequirements input) :
    ∃ name, requirement.identifier = "%input_" ++ name := by
  cases input with
  | mk name ty visibility span =>
    cases scalarType with
    | native =>
      simp only [Input.callArgumentRequirements, Input.requirements] at member
      rcases List.mem_singleton.mp member with rfl
      exact ⟨name, rfl⟩
    | bool =>
      simp only [Input.callArgumentRequirements, Input.requirements] at member
      rcases List.mem_singleton.mp member with rfl
      exact ⟨name, rfl⟩
    | uint width =>
      simp only [Input.callArgumentRequirements, Input.requirements] at member
      rcases List.mem_singleton.mp member with rfl
      exact ⟨name, rfl⟩

private theorem find_input_of_nodupNames {inputs : List Input} (input : Input)
    (distinct : (inputs.map (·.name)).Nodup) (member : input ∈ inputs) :
    inputs.find? (·.name == input.name) = some input := by
  induction inputs with
  | nil => simp at member
  | cons head tail ih =>
    simp only [List.map_cons, List.nodup_cons] at distinct
    rcases List.mem_cons.mp member with equal | member
    · subst input
      simp
    · cases sameName : (head.name == input.name) with
      | true =>
        have nameEq : head.name = input.name := beq_iff_eq.mp sameName
        have inputNameMember : input.name ∈ tail.map (·.name) :=
          List.mem_map.mpr ⟨input, member, rfl⟩
        have headNameMember : head.name ∈ tail.map (·.name) := by
          simpa [nameEq] using inputNameMember
        exact False.elim (distinct.1 headNameMember)
      | false =>
        simp only [List.find?_cons, sameName]
        exact ih distinct.2 member

private theorem circuitInput_mem_callArguments (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan) (input : Input)
    (planAccepted : Impact.lower state entry = .ok plan)
    (inputMember : input ∈ entry.circuit.inputs)
    (callMember : input.name ∈ entry.callInputs) :
    input ∈ entry.callArguments := by
  have validated := GenericStateEffectValidation.lower_circuit_validated_source
    state entry plan planAccepted
  have namesUnique : uniqueNames (entry.circuit.inputs.map (·.name)) = true := by
    cases unique : uniqueNames (entry.circuit.inputs.map (·.name)) with
    | true => rfl
    | false => simp [Circuit.validate, unique, Bind.bind, Except.bind] at validated
  have namesNodup : (entry.circuit.inputs.map (·.name)).Nodup := by
    apply GenericStateKeys.nodup_of_eraseDups_length_eq
    apply beq_iff_eq.mp
    simpa [uniqueNames] using namesUnique
  have found : entry.circuit.inputs.find? (·.name == input.name) = some input :=
    find_input_of_nodupNames input namesNodup inputMember
  unfold Entrypoint.callArguments
  apply List.mem_filterMap.mpr
  exact ⟨input.name, callMember, found⟩

private theorem plainScalarRead_bindings (read : Impact.Read)
    (plain : read.components = [] ∧ read.guard = none)
    (scalarType : ScalarType read.ty) :
    read.bindings = [(read.name, read.ty)] := by
  rcases read with ⟨name, ty, components, schema, guard, rootCellRead⟩
  rcases plain with ⟨componentsEq, guardEq⟩
  change components = [] at componentsEq
  change guard = none at guardEq
  subst components
  subst guard
  cases scalarType <;> rfl

private theorem scalarType_supported (ty : Ty) (scalarType : ScalarType ty) :
    ty = .native ∨ ty = .bool ∨ ∃ width, ty = .uint width := by
  cases scalarType with
  | native => exact Or.inl rfl
  | bool => exact Or.inr (Or.inl rfl)
  | uint width => exact Or.inr (Or.inr ⟨width, rfl⟩)

/-- The accepted scalar call schedule admits every emitted source scalar
input name and every plain post-public scalar read name. -/
theorem accepted_source_identifiers (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan) (expected : Expected)
    (planAccepted : Impact.lower state entry = .ok plan)
    (expectedAccepted : Native.expectedEntrypoint state entry = .ok expected)
    (identifiers : ∀ requirement ∈ expected.rawInputs ++ expected.inputs,
      validIdentifier requirement.identifier = true) :
    (∀ input ∈ entry.circuit.inputs, ScalarType input.ty →
      validIdentifier ("%input_" ++ input.name) = true) ∧
    (∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
      read.components = [] → read.guard = none → ScalarType read.ty →
        validIdentifier ("%input_" ++ read.name) = true) := by
  have scalarRequirementMember := scalarSourceInputRequirement_members
  constructor
  · intro input inputMember scalarType
    have requirements := scalarRequirementMember input scalarType
    by_cases callMember : input.name ∈ entry.callInputs
    · have argumentMember := circuitInput_mem_callArguments state entry plan input
        planAccepted inputMember callMember
      have rawMember : scalarSourceInputRequirement input ∈ expected.rawInputs := by
        rw [GenericStateCircuitParts.expectedEntrypoint_rawInputs state entry expected
          expectedAccepted]
        exact List.mem_flatMap.mpr ⟨input, argumentMember, requirements.2⟩
      have allMember := List.mem_append_left expected.inputs rawMember
      have valid := identifiers (scalarSourceInputRequirement input) allMember
      simpa [scalarSourceInputRequirement] using valid
    · have filteredMember : input ∈ entry.circuit.inputs.filter
          (fun candidate => !entry.callInputs.contains candidate.name) := by
        apply List.mem_filter.mpr
        refine ⟨inputMember, ?_⟩
        simp [callMember]
      have initialMember : scalarSourceInputRequirement input ∈
          ((entry.circuit.inputs.filter
            (fun candidate => !entry.callInputs.contains candidate.name)).flatMap
            Input.requirements) :=
        List.mem_flatMap.mpr ⟨input, filteredMember, requirements.1⟩
      obtain ⟨emitted, emittedMember, coreEq⟩ :=
        GenericStateCircuitParts.expectedEntrypoint_initialInputCore state entry expected
          expectedAccepted (scalarSourceInputRequirement input) initialMember
      have allMember := List.mem_append_right expected.rawInputs emittedMember
      have emittedValid := identifiers emitted allMember
      have identifierEq : emitted.identifier = "%input_" ++ input.name := by
        have projection := congrArg
          (fun core : String × Visibility × Ty × Bool => core.1) coreEq
        simpa [GenericStateCircuitParts.inputRequirementCore,
          scalarSourceInputRequirement] using projection
      simpa [identifierEq] using emittedValid
  · intro read readMember componentsEmpty unguarded scalarType
    have plain : read.components = [] ∧ read.guard = none := ⟨componentsEmpty, unguarded⟩
    have singleton := plainScalarRead_bindings read plain scalarType
    have supported := scalarType_supported read.ty scalarType
    obtain ⟨requirement, requirementMember, coreEq⟩ :=
      GenericStateCircuitParts.expectedEntrypoint_scalarReadDescriptor state entry expected
        expectedAccepted plan planAccepted read read.name read.ty readMember singleton supported
    have allMember := List.mem_append_right expected.rawInputs requirementMember
    have valid := identifiers requirement allMember
    have identifierEq : requirement.identifier = "%input_" ++ read.name := by
      have projection := congrArg
        (fun core : String × Visibility × Ty × Bool => core.1) coreEq
      simpa [GenericStateCircuitParts.inputRequirementCore] using projection
    simpa [identifierEq] using valid

/-- Every raw or emitted scalar descriptor in an accepted scalar entrypoint
keeps the source input prefix. Post-read bindings already carry this prefix. -/
theorem accepted_scalar_requirement_source_names (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan) (expected : Expected)
    (planAccepted : Impact.lower state entry = .ok plan)
    (expectedAccepted : Native.expectedEntrypoint state entry = .ok expected)
    (scalarInputs : ∀ input ∈ entry.circuit.inputs,
      Nonempty (ScalarType input.ty))
    (required : InputRequirement)
    (member : required ∈ expected.rawInputs ++ expected.inputs) :
    ∃ name, required.identifier = "%input_" ++ name := by
  rcases List.mem_append.mp member with rawMember | inputMember
  · rw [GenericStateCircuitParts.expectedEntrypoint_rawInputs state entry expected
      expectedAccepted] at rawMember
    obtain ⟨input, argumentMember, requirementMember⟩ := List.mem_flatMap.mp rawMember
    unfold Entrypoint.callArguments at argumentMember
    obtain ⟨_, _, found⟩ := List.mem_filterMap.mp argumentMember
    have inputMember : input ∈ entry.circuit.inputs := List.mem_of_find?_eq_some found
    obtain ⟨scalarType⟩ := scalarInputs input inputMember
    exact scalarCallArgumentRequirement_sourcePrefix input scalarType required requirementMember
  · have coreMember : GenericStateCircuitParts.inputRequirementCore required ∈
        expected.inputs.map GenericStateCircuitParts.inputRequirementCore :=
      List.mem_map_of_mem inputMember
    rw [GenericStateCircuitParts.expectedEntrypoint_inputRequirementCoreMap
      state entry expected plan expectedAccepted planAccepted] at coreMember
    have sourcesMember : GenericStateCircuitParts.inputRequirementCore required ∈
        (GenericStateCircuitParts.expectedInputRequirementSources entry plan).map
          GenericStateCircuitParts.inputRequirementCore := coreMember
    obtain ⟨source, sourceMember, coreEq⟩ := List.mem_map.mp sourcesMember
    have identifierEq : required.identifier = source.identifier := by
      have projection := congrArg
        (fun core : String × Visibility × Ty × Bool => core.1) coreEq
      simpa [GenericStateCircuitParts.inputRequirementCore] using projection.symm
    have sourcePrefix : ∃ name, source.identifier = "%input_" ++ name := by
      unfold GenericStateCircuitParts.expectedInputRequirementSources
        GenericStateCircuitParts.sourceInitialInputRequirements
        GenericStateCircuitParts.sourcePostReadRequirements at sourceMember
      rcases List.mem_append.mp sourceMember with circuitRequirement | readRequirement
      · obtain ⟨input, filteredMember, requirementMember⟩ := List.mem_flatMap.mp circuitRequirement
        have inputMember : input ∈ entry.circuit.inputs :=
          (List.mem_filter.mp filteredMember).1
        obtain ⟨scalarType⟩ := scalarInputs input inputMember
        exact scalarInputRequirement_sourcePrefix input scalarType source requirementMember
      · obtain ⟨read, readMember, bindingMember⟩ := List.mem_flatMap.mp readRequirement
        obtain ⟨pair, _, requirementEq⟩ := List.mem_map.mp bindingMember
        rcases pair with ⟨name, ty⟩
        subst source
        cases ty <;> exact ⟨name, rfl⟩
    obtain ⟨name, sourceEq⟩ := sourcePrefix
    exact ⟨name, identifierEq.trans sourceEq⟩

end Noctium.Verification.ScalarLedgerSourceIdentifiers
