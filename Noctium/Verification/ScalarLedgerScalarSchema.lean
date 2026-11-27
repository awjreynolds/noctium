import Noctium.Verification.GenericStateCircuitParts
import Noctium.Verification.GenericStateSourceNames
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

private def scalarSourceInputRequirement (input : Input) : InputRequirement :=
  {identifier := "%input_" ++ input.name, visibility := input.visibility, ty := input.ty}

private theorem scalarSourceInputRequirement_members (input : Input)
    (supported : ScalarType input.ty) :
    scalarSourceInputRequirement input ∈ Input.requirements input ∧
      scalarSourceInputRequirement input ∈ Input.callArgumentRequirements input := by
  cases input with
  | mk name ty visibility span =>
    cases supported <;>
      simp [scalarSourceInputRequirement, Input.requirements,
        Input.callArgumentRequirements]

private theorem scalarSourceInput_find?_of_nodupNames {inputs : List Input}
    (input : Input) (distinct : (inputs.map (·.name)).Nodup)
    (member : input ∈ inputs) :
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

private theorem scalarSourceInput_mem_callArguments (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan) (input : Input)
    (planAccepted : Impact.lower state entry = .ok plan)
    (inputMember : input ∈ entry.circuit.inputs)
    (callMember : input.name ∈ entry.callInputs) :
    input ∈ entry.callArguments := by
  have namesNodup := GenericStateSourceNames.lower_input_names_unique
    state entry plan planAccepted
  have found : entry.circuit.inputs.find? (·.name == input.name) = some input :=
    scalarSourceInput_find?_of_nodupNames input namesNodup inputMember
  unfold Entrypoint.callArguments
  apply List.mem_filterMap.mpr
  exact ⟨input.name, callMember, found⟩

private theorem scalarType_supported (ty : Ty) (supported : ScalarType ty) :
    ty = .native ∨ ty = .bool ∨ ∃ width, ty = .uint width := by
  cases supported with
  | native => exact Or.inl rfl
  | bool => exact Or.inr (Or.inl rfl)
  | uint width => exact Or.inr (Or.inr ⟨width, rfl⟩)

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

/-- Every source circuit input and plain post-public scalar read name appears
in the accepted expected descriptor identifiers. -/
theorem accepted_source_input_identifier_membership (state : List StateDecl)
    (ep : Entrypoint) (plan : Impact.Plan) (shape : Expected)
    (planAccepted : Impact.lower state ep = .ok plan)
    (shapeAccepted : Native.expectedEntrypoint state ep = .ok shape)
    (scalarInputs : ∀ input ∈ ep.circuit.inputs,
      Nonempty (ScalarType input.ty))
    (plainScalarReads : ∀ read ∈ plan.reads.drop
      (Impact.publicInputReadCount ep.circuit.inputs),
      read.bindings = [(read.name, read.ty)] ∧ Nonempty (ScalarType read.ty)) :
    ∀ name ∈ ep.circuit.inputs.map (·.name) ++
      (plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs)).map (·.name),
      "%input_" ++ name ∈ (shape.rawInputs ++ shape.inputs).map (·.identifier) := by
  intro name sourceMember
  have lane (requirement : InputRequirement)
      (present : requirement ∈ shape.rawInputs ++ shape.inputs)
      (same : requirement.identifier = "%input_" ++ name) :
      "%input_" ++ name ∈ (shape.rawInputs ++ shape.inputs).map (·.identifier) :=
    List.mem_map.mpr ⟨requirement, present, same⟩
  rcases List.mem_append.mp sourceMember with circuitMember | readMember
  · obtain ⟨input, inputMember, nameEq⟩ := List.mem_map.mp circuitMember
    obtain ⟨supported⟩ := scalarInputs input inputMember
    have requirements := scalarSourceInputRequirement_members input supported
    by_cases callMember : input.name ∈ ep.callInputs
    · have argumentMember := scalarSourceInput_mem_callArguments state ep plan input
        planAccepted inputMember callMember
      have rawMember : scalarSourceInputRequirement input ∈ shape.rawInputs := by
        rw [GenericStateCircuitParts.expectedEntrypoint_rawInputs state ep shape shapeAccepted]
        exact List.mem_flatMap.mpr ⟨input, argumentMember, requirements.2⟩
      exact lane (scalarSourceInputRequirement input)
        (List.mem_append_left _ rawMember) (by simp [scalarSourceInputRequirement, nameEq])
    · have filteredMember : input ∈ ep.circuit.inputs.filter
          (fun candidate => !ep.callInputs.contains candidate.name) := by
        apply List.mem_filter.mpr
        refine ⟨inputMember, ?_⟩
        simp [callMember]
      have initialMember : scalarSourceInputRequirement input ∈
          ((ep.circuit.inputs.filter
            (fun candidate => !ep.callInputs.contains candidate.name)).flatMap
            Input.requirements) :=
        List.mem_flatMap.mpr ⟨input, filteredMember, requirements.1⟩
      obtain ⟨emitted, emittedMember, coreEq⟩ :=
        GenericStateCircuitParts.expectedEntrypoint_initialInputCore state ep shape
          shapeAccepted (scalarSourceInputRequirement input) initialMember
      have identifierEq : emitted.identifier = "%input_" ++ input.name := by
        have projection := congrArg
          (fun core : String × Visibility × Ty × Bool => core.1) coreEq
        simpa [GenericStateCircuitParts.inputRequirementCore,
          scalarSourceInputRequirement] using projection
      exact lane emitted (List.mem_append_right _ emittedMember)
        (identifierEq.trans (congrArg (fun found => "%input_" ++ found) nameEq))
  · obtain ⟨read, readPresent, nameEq⟩ := List.mem_map.mp readMember
    obtain ⟨singleton, ⟨supported⟩⟩ := plainScalarReads read readPresent
    have supportedKinds := scalarType_supported read.ty supported
    obtain ⟨requirement, requirementMember, coreEq⟩ :=
      GenericStateCircuitParts.expectedEntrypoint_scalarReadDescriptor state ep shape
        shapeAccepted plan planAccepted read read.name read.ty readPresent singleton
        supportedKinds
    have identifierEq : requirement.identifier = "%input_" ++ read.name := by
      have projection := congrArg
        (fun core : String × Visibility × Ty × Bool => core.1) coreEq
      simpa [GenericStateCircuitParts.inputRequirementCore] using projection
    exact lane requirement (List.mem_append_right _ requirementMember)
      (identifierEq.trans (congrArg (fun found => "%input_" ++ found) nameEq))

end Noctium.Verification.ScalarLedgerScalarSchema
