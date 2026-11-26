import Noctium.Verification.ScalarValidatedProgram
import Noctium.Verification.ScalarCircuit
import Noctium.Verification.ScalarAdmission

namespace Noctium.Verification.ScalarTranslationSoundness

open Lean Backend NativeRelation NativeRelationJson
open Backend.Native
open ScalarNormalization (interpret)
open ScalarValidationOpcodeProfile (checkedScalarOpcodeProfile)

/-- The instruction rows produced by the default standalone circuit lowerer. -/
def defaultLoweredRows (circuit : Circuit) : Array Json :=
  ((Zkir.lowerBody (Passes.pruneCircuit circuit)).run {}).2.instructions

private def scalarInputRequirement (input : Input) : InputRequirement :=
  {identifier := "%input_" ++ input.name, visibility := input.visibility, ty := input.ty}

private def scalarType_of_canonical {ty : Ty} {value : ty.Denote}
    (canonical : ScalarNormalization.Canonical ty value) :
    ScalarNormalization.ScalarType ty := by
  cases ty with
  | native => exact .native
  | bool => exact .bool
  | uint maximum => exact .uint maximum
  | bytes length => simp [ScalarNormalization.Canonical, ScalarNormalization.sourceNumber?] at canonical
  | opaqueBytes => simp [ScalarNormalization.Canonical, ScalarNormalization.sourceNumber?] at canonical
  | opaqueString => simp [ScalarNormalization.Canonical, ScalarNormalization.sourceNumber?] at canonical
  | jubjubScalar => simp [ScalarNormalization.Canonical, ScalarNormalization.sourceNumber?] at canonical
  | jubjubPoint => simp [ScalarNormalization.Canonical, ScalarNormalization.sourceNumber?] at canonical
  | foreign kind => simp [ScalarNormalization.Canonical, ScalarNormalization.sourceNumber?] at canonical

private theorem scalarType_notForeign {ty : Ty}
    (supported : ScalarNormalization.ScalarType ty) : ty.isForeign = false := by
  cases supported <;> rfl

private theorem scalarInputRequirements (input : Input)
    (supported : ScalarNormalization.ScalarType input.ty) :
    Input.requirements input = [scalarInputRequirement input] := by
  cases input with
  | mk name ty visibility span => cases supported <;> rfl

private theorem scalarInputRequirements_map (inputs : List Input)
    (supported : ∀ input ∈ inputs, ScalarNormalization.ScalarType input.ty) :
    inputs.flatMap Input.requirements = inputs.map scalarInputRequirement := by
  induction inputs with
  | nil => rfl
  | cons input rest ih =>
    simp only [List.flatMap_cons, List.map_cons]
    rw [scalarInputRequirements input (supported input (by simp))]
    rw [ih (fun item member => supported item (List.mem_cons_of_mem _ member))]
    rfl

private theorem canonicalInputRequirements (circuit : Circuit) {values : EvalEnv}
    {assignment : Assignment} (admitted : ScalarNormalization.CanonicalInputs circuit values assignment)
    {expected : Expected}
    (expectedAccepted : Native.expectedCircuit (Passes.pruneCircuit circuit) = .ok expected) :
    expected.inputs = circuit.inputs.map scalarInputRequirement ∧
      (∀ requirement ∈ expected.inputs, requirement.ty.isForeign = false) ∧
      (∀ requirement ∈ expected.inputs, requirement.activityGuard = none) := by
  have inputTypes : ∀ input ∈ circuit.inputs, Nonempty (ScalarNormalization.ScalarType input.ty) := by
    intro input member
    obtain ⟨_, _, canonical⟩ := admitted.complete input member
    exact ⟨scalarType_of_canonical canonical⟩
  obtain ⟨_, _, _, _, _, _, _, _, shape, _⟩ :=
    ScalarNormalization.expectedCircuit_parts (Passes.pruneCircuit circuit) expected expectedAccepted
  have requirements : expected.inputs = circuit.inputs.map scalarInputRequirement := by
    rw [shape]
    change circuit.inputs.flatMap Input.requirements = _
    exact scalarInputRequirements_map circuit.inputs
      (fun input member => Classical.choice (inputTypes input member))
  refine ⟨requirements, ?_, ?_⟩
  · intro requirement member
    rw [requirements] at member
    obtain ⟨input, inputMember, requirementEqual⟩ := List.mem_map.mp member
    rw [← congrArg InputRequirement.ty requirementEqual]
    obtain ⟨supported⟩ := inputTypes input inputMember
    exact scalarType_notForeign supported
  · intro requirement member
    rw [requirements] at member
    obtain ⟨input, _, requirementEqual⟩ := List.mem_map.mp member
    rw [← congrArg InputRequirement.activityGuard requirementEqual]
    rfl

private theorem scalarInputValuesMap (inputs : List Input)
    (visibility : Visibility) (witness : Assignment) :
    ((inputs.map scalarInputRequirement).filterMap fun requirement =>
      if requirement.visibility == visibility then some (witness requirement.identifier) else none) =
    (inputs.filter (·.visibility == visibility)).map
      (fun input => witness ("%input_" ++ input.name)) := by
  induction inputs with
  | nil => rfl
  | cons input rest ih =>
    simp only [List.map_cons, List.filterMap_cons, List.filter_cons]
    simp only [List.filterMap_map, Function.comp_def, scalarInputRequirement, beq_iff_eq] at ih
    by_cases visible : input.visibility = visibility
    · simpa [scalarInputRequirement, visible, Function.comp_def] using ih
    · simpa [scalarInputRequirement, visible, Function.comp_def] using ih

private theorem scalarInputValues (expected : Expected) (inputs : List Input)
    (inputShape : expected.inputs = inputs.map scalarInputRequirement)
    (visibility : Visibility) (witness : Assignment) :
    ScalarValidatedProgram.inputValues expected visibility witness =
      (inputs.filter (·.visibility == visibility)).map
        (fun input => witness ("%input_" ++ input.name)) := by
  unfold ScalarValidatedProgram.inputValues
  rw [inputShape]
  exact scalarInputValuesMap inputs visibility witness

private theorem mapSomeInjective {left right : List Scalar}
    (equal : left.map some = right.map some) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp at equal ⊢
  | cons head tail ih =>
    cases right with
    | nil => simp at equal
    | cons otherHead otherTail =>
      simp only [List.map_cons, List.cons.injEq] at equal
      obtain ⟨headEqual, tailEqual⟩ := equal
      have headEqual : head = otherHead := Option.some.inj headEqual
      have tailEqual : tail = otherTail := ih tailEqual
      simp [headEqual, tailEqual]

private theorem mapGroupsSomeInjective {left right : List (List Scalar)}
    (equal : left.map (List.map some) = right.map (List.map some)) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp at equal ⊢
  | cons head tail ih =>
    cases right with
    | nil => simp at equal
    | cons otherHead otherTail =>
      simp only [List.map_cons, List.cons.injEq] at equal
      obtain ⟨headEqual, tailEqual⟩ := equal
      have headEqual : head = otherHead := mapSomeInjective headEqual
      have tailEqual : tail = otherTail := ih tailEqual
      simp [headEqual, tailEqual]

/-- A satisfying assignment for the checked output of the default standalone
lowerer executes the original Lean circuit. Its returns, ordered public Impact
groups, input streams, and scalar input bounds match the source circuit. -/
theorem lowerCircuit_sound (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (circuit : Circuit) (values : EvalEnv)
    (json : Json) (relation : Program) (streams : InputStreams)
    (witness : Assignment) (publicGroups : List (List Scalar))
    (admitted : ScalarNormalization.CanonicalInputs circuit values witness)
    (scalarAdmission : ScalarNormalization.ScalarCircuitAdmission circuit)
    (lowered : Zkir.lowerCircuit circuit = .ok json)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (profile : checkedScalarOpcodeProfile
      (defaultLoweredRows circuit).toList.zipIdx relation.instructions = true)
    (satisfies : CircuitSatisfies hash relation streams witness publicGroups) :
    ∃ result, circuit.run ctx values = .ok result ∧
      result.map Prod.fst = circuit.outputs.map (·.name) ∧
      relation.returns witness = result.map (fun pair =>
        scalar (ScalarNormalization.valueNumber pair.2)) ∧
      streams.publicValues = (circuit.inputs.filter (·.visibility == .«public»)).map
        (fun input => witness ("%input_" ++ input.name)) ∧
      streams.privateValues = (circuit.inputs.filter (·.visibility == .private)).map
        (fun input => witness ("%input_" ++ input.name)) ∧
      publicGroups = (circuit.inputs.filter (·.visibility == .«public»)).map
        (fun input => [witness ("%input_" ++ input.name)]) ++
          (if result.isEmpty then [] else
            [result.map (fun pair => scalar (ScalarNormalization.valueNumber pair.2))]) ∧
      (result ≠ [] → relation.returns witness = publicGroups.getLastD []) ∧
      (∀ input ∈ circuit.inputs,
        (witness ("%input_" ++ input.name)).val ≤ Native.sourceMaximum input.ty) := by
  let pruned := Passes.pruneCircuit circuit
  obtain ⟨expected, expectedAccepted, nativeAccepted⟩ :=
    Zkir.lowerCircuit_validated circuit json lowered
  have rowsParsed : Native.arrayField json "instructions" = .ok (defaultLoweredRows circuit) := by
    simpa only [defaultLoweredRows] using Zkir.lowerCircuit_instructions circuit json lowered
  obtain ⟨expectedInputShape, inputSchema, inputGuards⟩ :=
    canonicalInputRequirements circuit admitted expectedAccepted
  have prunedInputs :
      ScalarNormalization.CanonicalInputs pruned values witness :=
    ⟨admitted.unique, admitted.declared, admitted.complete, admitted.binding⟩
  have validated := ScalarValidatedProgram.validate_sound nativeAccepted decoded
    rowsParsed profile inputSchema inputGuards satisfies
  have source := ScalarNormalization.expectedCircuit_sound ctx hash implementation witness pruned
    values expected prunedInputs expectedAccepted validated.bounds validated.assertions
    (ScalarNormalization.ScalarCircuitAdmission.pruneCircuit circuit scalarAdmission)
  obtain ⟨result, sourceRun, names, sourceReturns, sourceGroups⟩ := source
  have sourceRunOriginal : circuit.run ctx values = .ok result := by
    rw [← Passes.pruneCircuit_run ctx values circuit]
    exact sourceRun
  have returnEquality :
      (relation.returns witness).map some =
        (result.map (fun pair => scalar (ScalarNormalization.valueNumber pair.2))).map some := by
    simpa only [List.map_map, Function.comp_def] using
      validated.returns.trans sourceReturns.symm
  have returnValues : relation.returns witness = result.map (fun pair =>
      scalar (ScalarNormalization.valueNumber pair.2)) :=
    mapSomeInjective returnEquality
  let sourceGroupsValues : List (List Scalar) :=
    ((pruned.inputs.filter (·.visibility == .«public»)).map
      (fun input => [witness ("%input_" ++ input.name)])) ++
      (if result.isEmpty then [] else
        [result.map (fun pair => scalar (ScalarNormalization.valueNumber pair.2))])
  have groupsWithOptions :
      publicGroups.map (List.map some) = sourceGroupsValues.map (List.map some) := by
    calc
      _ = expected.groups.map (List.map (interpret hash witness)) := validated.impact
      _ = _ := sourceGroups
      _ = _ := by
        simp only [sourceGroupsValues, List.map_append]
        by_cases empty : result.isEmpty = true
        · simp [empty]
        · have nonempty : result.isEmpty = false := by cases h : result.isEmpty <;> simp_all
          simp [nonempty, List.map_map, Function.comp_def]
  have groupValues :
      publicGroups =
        sourceGroupsValues :=
    mapGroupsSomeInjective groupsWithOptions
  have publicInputs : streams.publicValues =
      (circuit.inputs.filter (·.visibility == .«public»)).map
        (fun input => witness ("%input_" ++ input.name)) := by
    rw [validated.publicInputs]
    simpa [pruned, Passes.pruneCircuit] using
      scalarInputValues expected pruned.inputs expectedInputShape .«public» witness
  have privateInputs : streams.privateValues =
      (circuit.inputs.filter (·.visibility == .private)).map
        (fun input => witness ("%input_" ++ input.name)) := by
    rw [validated.privateInputs]
    simpa [pruned, Passes.pruneCircuit] using
      scalarInputValues expected pruned.inputs expectedInputShape .private witness
  have sourceGroupsOriginal :
      publicGroups =
        (circuit.inputs.filter (·.visibility == .«public»)).map
          (fun input => [witness ("%input_" ++ input.name)]) ++
          (if result.isEmpty then [] else
            [result.map (fun pair => scalar (ScalarNormalization.valueNumber pair.2))]) := by
    simpa [sourceGroupsValues, pruned, Passes.pruneCircuit] using groupValues
  have inputBounds : ∀ input ∈ circuit.inputs,
      (witness ("%input_" ++ input.name)).val ≤ Native.sourceMaximum input.ty := by
    intro input member
    have prunedMember : input ∈ pruned.inputs := by
      simpa [pruned, Passes.pruneCircuit] using member
    have requirementMember : scalarInputRequirement input ∈ expected.inputs := by
      rw [expectedInputShape]
      exact List.mem_map.mpr ⟨input, prunedMember, rfl⟩
    simpa [scalarInputRequirement] using
      validated.inputBounds (scalarInputRequirement input) requirementMember rfl
  refine ⟨result, sourceRunOriginal, names, returnValues, publicInputs, privateInputs,
    sourceGroupsOriginal, ?_, inputBounds⟩
  · intro nonempty
    rw [returnValues, sourceGroupsOriginal]
    have resultNonempty : result.isEmpty = false := by
      cases result <;> simp_all
    rw [resultNonempty]
    simp only [Bool.false_eq_true, ↓reduceIte, List.getLastD_concat]

/-- Witness construction uses the source input names and numeric SSA capacity
of the exact validated and decoded compiler output. The row limit and the
number of generated names are distinct bounds. -/
theorem lowerCircuit_witness_preflight (circuit : Circuit) {values : EvalEnv}
    {inputs : Assignment} {json : Json} {relation : Program}
    (admitted : ScalarNormalization.CanonicalInputs circuit values inputs)
    (lowered : Zkir.lowerCircuit circuit = .ok json)
    (decoded : NativeRelationJson.decode json = .ok relation) :
    (∀ input ∈ circuit.inputs, validIdentifier ("%input_" ++ input.name) = true) ∧
      ((Zkir.lowerBody (Passes.pruneCircuit circuit)).run {}).2.next ≤
        Native.maxInstructions * Native.maxVectorLength ∧
      (defaultLoweredRows circuit).toList.mapM NativeRelationJson.decodeInstruction =
        .ok relation.instructions ∧
      relation.instructions.length ≤ Native.maxInstructions := by
  obtain ⟨expected, expectedAccepted, nativeAccepted⟩ :=
    Zkir.lowerCircuit_validated circuit json lowered
  obtain ⟨shape, _, _⟩ := canonicalInputRequirements circuit admitted expectedAccepted
  have rowsParsed : Native.arrayField json "instructions" = .ok (defaultLoweredRows circuit) :=
    Zkir.lowerCircuit_instructions circuit json lowered
  have identifiers := ScalarAdmission.input_identifiers nativeAccepted decoded
  obtain ⟨decodedRows, decodedParsed, decoding⟩ :=
    NativeRelationInstructionProjection.decode_instructionProjection decoded
  cases Except.ok.inj (decodedParsed.symm.trans rowsParsed)
  refine ⟨?_, ScalarAdmission.lowerBody_budget circuit json lowered, decoding,
    ScalarAdmission.instruction_bound nativeAccepted decoded⟩
  intro input member
  apply identifiers (scalarInputRequirement input)
  rw [shape]
  exact List.mem_map.mpr ⟨input, member, rfl⟩

/-- Once the constructors extend the given input assignment and satisfy each
emitted instruction, the checked relation determines all public and private
streams, ordered Impact groups, and returns of the successful source run. -/
theorem lowerCircuit_complete_of_witness (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (circuit : Circuit) (values result : EvalEnv)
    (json : Json) (relation : Program) (inputs witness : Assignment)
    (admitted : ScalarNormalization.CanonicalInputs circuit values inputs)
    (scalarAdmission : ScalarNormalization.ScalarCircuitAdmission circuit)
    (lowered : Zkir.lowerCircuit circuit = .ok json)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (profile : checkedScalarOpcodeProfile
      (defaultLoweredRows circuit).toList.zipIdx relation.instructions = true)
    (success : circuit.run ctx values = .ok result)
    (frame : ∀ name, witness ("%input_" ++ name) = inputs ("%input_" ++ name))
    (holds : ∀ instruction ∈ relation.instructions, instruction.Holds hash witness) :
    Satisfies hash relation
      {publicValues := (circuit.inputs.filter (·.visibility == .«public»)).map
        (fun input => inputs ("%input_" ++ input.name)),
       privateValues := (circuit.inputs.filter (·.visibility == .private)).map
        (fun input => inputs ("%input_" ++ input.name))}
      witness
      ((circuit.inputs.filter (·.visibility == .«public»)).map
        (fun input => [inputs ("%input_" ++ input.name)]) ++
        (if result.isEmpty then [] else
          [result.map (fun pair => scalar (ScalarNormalization.valueNumber pair.2))]))
      (result.map (fun pair => scalar (ScalarNormalization.valueNumber pair.2))) := by
  have witnessInputs : ScalarNormalization.CanonicalInputs circuit values witness :=
    ⟨admitted.unique, admitted.declared, admitted.complete,
      fun input member value lookup canonical =>
        (frame input.name).trans (admitted.binding input member value lookup canonical)⟩
  let streams : InputStreams :=
    {publicValues := relation.inputValues .«public» witness,
     privateValues := relation.inputValues .private witness}
  have satisfies : CircuitSatisfies hash relation streams witness (relation.groups witness) :=
    ⟨holds, rfl, rfl, rfl⟩
  obtain ⟨observed, observedRun, _, returns, publicInputs, privateInputs, groups, _, _⟩ :=
    lowerCircuit_sound ctx hash implementation circuit values json relation streams witness
      (relation.groups witness) witnessInputs scalarAdmission lowered decoded profile satisfies
  have same := Except.ok.inj (observedRun.symm.trans success)
  subst observed
  refine ⟨holds, ?_, ?_, ?_, returns⟩
  · simpa only [streams, frame] using publicInputs
  · simpa only [streams, frame] using privateInputs
  · simpa only [frame] using groups

end Noctium.Verification.ScalarTranslationSoundness
