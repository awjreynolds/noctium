import Noctium.Verification.NativeInputOrdinalTrace
import Noctium.Verification.RangeDedupAcceptedArray
import Noctium.Verification.ScalarValidationRawSeedMeaning

namespace Noctium.Verification.ScalarValidatedProgram

open Lean Backend NativeRelation NativeRelationJson
open Backend.Native
open ScalarNormalization (interpret)
open RangeDedupAcceptedArray ScalarValidationMeaning ScalarValidationOpcodeProfile
open ScalarValidationRawSeedMeaning
open ScalarValidationNativeDefinitions (SupportedScalarOpcode NativeDefinitionTrace)
open NativeInputOrdinalTrace NativeRelationInstructionProjection

/-- Every satisfying assignment of the checked, accepted rows establishes
the source assertion schedule and its scalar bounds. -/
theorem sourceRequirements
    {expected : Expected} {json : Json} {program : Program} {rows : Array Json}
    (accepted : Native.validate expected json = .ok ())
    (rowsParsed : Native.arrayField json "instructions" = .ok rows)
    (decodedRows : rows.toList.mapM NativeRelationJson.decodeInstruction =
      .ok program.instructions)
    (profile : checkedScalarOpcodeProfile rows.toList.zipIdx program.instructions = true)
    (schema : ∀ requirement ∈ expected.rawInputs ++ expected.inputs,
      requirement.ty.isForeign = false) :
    ∀ {hash streams witness groups}, CircuitSatisfies hash program streams witness groups →
      (∀ term ∈ expected.assertions, interpret hash witness term = some one) ∧
      (∀ requirement ∈ expected.bounds,
        ∃ value, interpret hash witness requirement.1 = some value ∧
          value.val ≤ requirement.2) ∧
      (∀ requirement ∈ expected.rawInputs ++ expected.inputs,
        requirement.ty.isForeign = false →
        requirement.canonicalJubjubScalar = false →
        (witness requirement.identifier).val ≤ Native.sourceMaximum requirement.ty) := by
  obtain ⟨instructions, rawInputs, seed, final, driver⟩ :=
    ScalarValidationProjection.validate_driver_result accepted
  have instructionsEq : instructions = rows :=
    Except.ok.inj (driver.instructionsParsed.symm.trans rowsParsed)
  have indexedDecoded :
      ((rows.toList.zipIdx).map Prod.fst).mapM NativeRelationJson.decodeInstruction =
        .ok program.instructions := by
    simpa only [List.zipIdx_map_fst] using decodedRows
  have driverTrace :
      Native.validateInstructionLoop expected (rows.toList.zipIdx) seed = .ok final := by
    rw [← instructionsEq]
    exact driver.instructionTrace
  intro hash streams witness groups satisfies
  have rawSchema : ∀ requirement ∈ expected.rawInputs,
      requirement.ty.isForeign = false := by
    intro requirement member
    exact schema requirement (List.mem_append_left expected.inputs member)
  have inputSchema : ∀ requirement ∈ expected.inputs,
      requirement.ty.isForeign = false := by
    intro requirement member
    exact schema requirement (List.mem_append_right expected.rawInputs member)
  obtain ⟨seedMeaning, seedDefinitions⟩ :=
    seedRawInputs_meaning_and_nativeDefinitions rawSchema (fun _ _ => rfl)
      driver.seededRawInputs
  have seedAssertionCount := seedRawInputs_assertionCount rawSchema driver.seededRawInputs
  have initialAssertions :
      RangeDedupAssertMeaning.CheckedAssertions hash witness expected seed.assertionCount := by
    simp [RangeDedupAssertMeaning.CheckedAssertions, seedAssertionCount]
  have acceptedSteps := checkedScalarOpcodeProfile_acceptedMeaningSteps
    indexedDecoded profile satisfies.instructions
  obtain ⟨finalMeaning, _, preserveAssertions, _⟩ :=
    accepted_loop_meaning_assertions_at_steps seedMeaning seedDefinitions inputSchema
      (fun _ _ => rfl) acceptedSteps driverTrace
  have assertions : ∀ term ∈ expected.assertions,
      interpret hash witness term = some one := by
    have checked := preserveAssertions initialAssertions
    simpa only [driver.assertionCount, RangeDedupAssertMeaning.CheckedAssertions,
      List.take_length] using checked
  have bounds := driver.rangeRequirements finalMeaning
  have inputBounds : ∀ requirement ∈ expected.rawInputs ++ expected.inputs,
      requirement.ty.isForeign = false →
      requirement.canonicalJubjubScalar = false →
      (witness requirement.identifier).val ≤ Native.sourceMaximum requirement.ty := by
    intro requirement member nonforeign ordinary
    exact driver.inputBound finalMeaning member nonforeign ordinary
  exact ⟨assertions, bounds, inputBounds⟩

private def outputOperands : Instruction → Option (List Operand)
  | .output values => some values
  | _ => none

private theorem raw_output_test {raw : Json} {instruction : Instruction}
    (supported : SupportedScalarOpcode raw instruction) :
    (Native.opcode raw == "output") = (outputOperands instruction).isSome := by
  cases supported <;> rename_i opcodeParsed <;> simp [Native.opcode, Except.toOption, opcodeParsed, outputOperands]

private theorem decoded_output_count {items : List (Json × Nat)} {instructions : List Instruction}
    (trace : NativeDefinitionTrace items instructions) :
    (items.map (Native.opcode ∘ Prod.fst)).count "output" =
      (instructions.filterMap outputOperands).length := by
  induction trace with
  | nil => rfl
  | @cons raw index instruction rest tail row trace ih =>
    have test := raw_output_test row.supported
    simp only [List.map_cons, Function.comp_apply, List.count_cons, List.filterMap_cons, test]
    cases outputOperands instruction <;> simp [ih]

private theorem decoded_output_member {items : List (Json × Nat)} {instructions : List Instruction}
    (trace : NativeDefinitionTrace items instructions) {values : List Operand}
    (member : values ∈ instructions.filterMap outputOperands) :
    ∃ raw index, (raw, index) ∈ items ∧ Native.stringField raw "op" = .ok "output" ∧
      NativeRelationJson.decodeInstruction raw = .ok (.output values) := by
  induction trace with
  | nil => simp at member
  | @cons raw index instruction rest tail row trace ih =>
    simp only [List.filterMap_cons] at member
    cases out : outputOperands instruction with
    | none =>
      obtain ⟨source, offset, present, opcode, decoded⟩ := ih (by simpa [out] using member)
      exact ⟨source, offset, List.mem_cons_of_mem _ present, opcode, decoded⟩
    | some head =>
      have occurs : values ∈ head :: tail.filterMap outputOperands := by simpa [out] using member
      rcases List.mem_cons.mp occurs with rfl | later
      · have output : instruction = .output values := by
          cases instruction <;> simp_all [outputOperands]
        subst instruction
        exact ⟨raw, index, by simp, by cases row.supported; assumption, row.decoded⟩
      · obtain ⟨source, offset, present, opcode, decoded⟩ := ih later
        exact ⟨source, offset, List.mem_cons_of_mem _ present, opcode, decoded⟩

private theorem program_returns_eq {program : Program} {witness : Assignment} :
    program.returns witness =
      (program.instructions.filterMap outputOperands).flatMap (List.map (·.read witness)) := by
  unfold Program.returns
  induction program.instructions with
  | nil => rfl
  | cons head tail ih => cases head <;> simp [List.filterMap_cons, outputOperands, ih]

/-- The accepted final Output row observes exactly the ordered source return
terms in the scalar model. -/
theorem returnValues
    {expected : Expected} {json : Json} {program : Program} {rows : Array Json}
    (accepted : Native.validate expected json = .ok ())
    (rowsParsed : Native.arrayField json "instructions" = .ok rows)
    (decodedRows : rows.toList.mapM NativeRelationJson.decodeInstruction =
      .ok program.instructions)
    (profile : checkedScalarOpcodeProfile rows.toList.zipIdx program.instructions = true)
    (schema : ∀ requirement ∈ expected.rawInputs ++ expected.inputs,
      requirement.ty.isForeign = false)
    {hash : Hash} {streams : InputStreams} {witness : Assignment} {groups : List (List Scalar)}
    (satisfies : CircuitSatisfies hash program streams witness groups) :
    expected.returns.map (interpret hash witness) = (program.returns witness).map some := by
  obtain ⟨instructions, _, seed, final, driver⟩ :=
    ScalarValidationProjection.validate_driver_result accepted
  have sameRows : instructions = rows :=
    Except.ok.inj (driver.instructionsParsed.symm.trans rowsParsed)
  subst instructions
  have indexedDecoded :
      ((rows.toList.zipIdx).map Prod.fst).mapM NativeRelationJson.decodeInstruction =
        .ok program.instructions := by
    simpa only [List.zipIdx_map_fst] using decodedRows
  have trace := NativeDefinitionTrace.ofDecodedCheckedProfile indexedDecoded profile
  have rawSchema : ∀ requirement ∈ expected.rawInputs, requirement.ty.isForeign = false :=
    fun requirement member => schema requirement (List.mem_append_left _ member)
  have inputSchema : ∀ requirement ∈ expected.inputs, requirement.ty.isForeign = false :=
    fun requirement member => schema requirement (List.mem_append_right _ member)
  obtain ⟨seedMeaning, seedDefinitions⟩ :=
    seedRawInputs_meaning_and_nativeDefinitions (hash := hash) (inputs := witness)
      (witness := witness) rawSchema (fun _ _ => rfl) driver.seededRawInputs
  have acceptedSteps := nativeDefinitionTrace_acceptedMeaningSteps trace satisfies.instructions
  obtain ⟨_, _, visits⟩ := accepted_loop_meaning_at_steps seedMeaning seedDefinitions
    inputSchema (fun _ _ => rfl) acceptedSteps driver.instructionTrace
  have shape := (Native.final_output_required rows.toList).mp driver.finalOutput
  simp only [Native.finalOutputShape, Bool.and_eq_true, beq_iff_eq] at shape
  have rawCount : (rows.toList.map Native.opcode).count "output" = 1 := shape.1.2
  have decodedCount := decoded_output_count trace
  rw [← List.map_map, List.zipIdx_map_fst, rawCount] at decodedCount
  obtain ⟨values, singleton⟩ := List.length_eq_one_iff.mp decodedCount.symm
  obtain ⟨raw, index, member, opcode, decoded⟩ :=
    decoded_output_member trace (values := values) (by rw [singleton]; simp)
  obtain ⟨_, _, meaning, _, checked, _, _⟩ := visits raw index member
  rw [program_returns_eq, singleton]
  simpa using (ScalarValidationOutputMeaning.accepted_output_meaning meaning checked opcode decoded).2

/-- The accepted scalar model preserves all ordered, active Impact payloads. -/
theorem impactPayloads
    {expected : Expected} {json : Json} {program : Program} {rows : Array Json}
    {hash : Hash} {streams : InputStreams} {witness : Assignment} {groups : List (List Scalar)}
    (accepted : Native.validate expected json = .ok ())
    (rowsParsed : Native.arrayField json "instructions" = .ok rows)
    (decodedRows : rows.toList.mapM NativeRelationJson.decodeInstruction = .ok program.instructions)
    (profile : checkedScalarOpcodeProfile rows.toList.zipIdx program.instructions = true)
    (schema : ∀ requirement ∈ expected.rawInputs ++ expected.inputs,
      requirement.ty.isForeign = false)
    (inputGuards : ∀ requirement ∈ expected.inputs, requirement.activityGuard = none)
    (satisfies : CircuitSatisfies hash program streams witness groups) :
    expected.groups.map (List.map (interpret hash witness)) = groups.map (List.map some) := by
  obtain ⟨instructions, _, seed, final, driver⟩ :=
    ScalarValidationProjection.validate_driver_result accepted
  have sameRows : instructions = rows :=
    Except.ok.inj (driver.instructionsParsed.symm.trans rowsParsed)
  subst instructions
  have indexedDecoded :
      ((rows.toList.zipIdx).map Prod.fst).mapM NativeRelationJson.decodeInstruction =
        .ok program.instructions := by
    simpa only [List.zipIdx_map_fst] using decodedRows
  have instructionsTrace := NativeDefinitionTrace.ofDecodedCheckedProfile indexedDecoded profile
  have rawSchema : ∀ requirement ∈ expected.rawInputs, requirement.ty.isForeign = false :=
    fun requirement member => schema requirement (List.mem_append_left _ member)
  have inputSchema : ∀ requirement ∈ expected.inputs, requirement.ty.isForeign = false :=
    fun requirement member => schema requirement (List.mem_append_right _ member)
  obtain ⟨seedMeaning, seedDefinitions⟩ :=
    seedRawInputs_meaning_and_nativeDefinitions (hash := hash) (inputs := witness)
      (witness := witness) rawSchema (fun _ _ => rfl) driver.seededRawInputs
  have seedCount := seedRawInputs_groupCount rawSchema driver.seededRawInputs
  have ordered := acceptedProfileOrderedImpactPayloads instructionsTrace seedMeaning
    seedDefinitions inputSchema inputGuards (fun _ _ => rfl)
    satisfies.instructions driver.instructionTrace
  rw [driver.groupCount, seedCount] at ordered
  have sameGroups : (Program.mk program.instructions 0 false).groups witness =
      groups := satisfies.groups
  simpa only [List.take_length, List.take_zero, List.map_nil, List.nil_append,
    sameGroups] using ordered

/-- The scalar model's ordered input streams use exactly the selected
producer requirements and their assigned values. -/
def inputValues (expected : Expected) (visibility : Visibility)
    (witness : Assignment) : List Scalar :=
  expected.inputs.filterMap fun requirement =>
    if requirement.visibility == visibility then some (witness requirement.identifier) else none

/-- The validated descriptor order fixes the ordered input values. -/
theorem inputValues_of_descriptors {program : Program} {expected : Expected}
    (descriptors : program.instructions.flatMap strictInstructionInputDescriptors =
      expected.inputs.map expectedInputDescriptor)
    (visibility : Visibility) (witness : Assignment) :
    program.inputValues visibility witness = inputValues expected visibility witness := by
  let read := fun (input : Visibility × String) =>
    if input.1 == visibility then some (witness input.2) else none
  have fromDescriptors :
      program.inputValues visibility witness =
        (program.instructions.flatMap strictInstructionInputDescriptors).filterMap read := by
    unfold Program.inputValues
    induction program.instructions with
    | nil => rfl
    | cons instruction tail ih =>
      cases instruction <;>
        simp only [List.flatMap_cons, strictInstructionInputDescriptors, List.nil_append,
          List.cons_append, List.filterMap_cons, ih, read]
  rw [fromDescriptors, descriptors]
  rw [List.filterMap_map]
  rfl

/-- Evidence about the exact accepted scalar program for an arbitrary
satisfying assignment. Undefined source interpretations stay uninhabited.
The returns are host observations. The ordered Impact groups carry public
binding in the scalar circuit model. -/
structure Sound (hash : Hash) (witness : Assignment) (expected : Expected)
    (program : Program) (streams : InputStreams) (groups : List (List Scalar)) : Prop where
  assertions : ∀ term ∈ expected.assertions, interpret hash witness term = some one
  bounds : ∀ requirement ∈ expected.bounds,
    ∃ value, interpret hash witness requirement.1 = some value ∧ value.val ≤ requirement.2
  inputBounds : ∀ requirement ∈ expected.inputs,
    requirement.canonicalJubjubScalar = false →
    (witness requirement.identifier).val ≤ Native.sourceMaximum requirement.ty
  publicInputs : streams.publicValues = inputValues expected .public witness
  privateInputs : streams.privateValues = inputValues expected .private witness
  impact : groups.map (List.map some) = expected.groups.map (List.map (interpret hash witness))
  returns : (program.returns witness).map some = expected.returns.map (interpret hash witness)

/-- Restore the whole checked scalar-validator result. The actual producer
fold and strict decoder agree on the same instruction rows. The opcode profile,
source input types and unguarded stream premises delimit the scalar model. -/
theorem validate_sound {expected : Expected} {json : Json} {program : Program}
    {rows : Array Json}
    (accepted : Native.validate expected json = .ok ())
    (decoded : NativeRelationJson.decode json = .ok program)
    (rowsParsed : Native.arrayField json "instructions" = .ok rows)
    (profile : checkedScalarOpcodeProfile rows.toList.zipIdx program.instructions = true)
    (inputSchema : ∀ requirement ∈ expected.inputs, requirement.ty.isForeign = false)
    (inputGuards : ∀ requirement ∈ expected.inputs, requirement.activityGuard = none)
    {hash : Hash} {streams : InputStreams} {witness : Assignment} {groups : List (List Scalar)}
    (satisfies : CircuitSatisfies hash program streams witness groups) :
    Sound hash witness expected program streams groups := by
  obtain ⟨decodedRows, header, rowsEq, decoding⟩ := decode_headerAndInstructions decoded
  cases Except.ok.inj (rowsEq.symm.trans rowsParsed)
  obtain ⟨noRaw, _, _, _⟩ :=
    ScalarValidationProjection.validate_driver_result_empty_header accepted header
  have schema : ∀ requirement ∈ expected.rawInputs ++ expected.inputs,
      requirement.ty.isForeign = false := by
    simpa only [noRaw, List.nil_append] using inputSchema
  have descriptors := validate_decoded_input_descriptors_of_checkedScalarProfile
    accepted decoded rowsParsed profile inputSchema
  obtain ⟨assertions, bounds, inputBounds⟩ :=
    sourceRequirements accepted rowsParsed decoding profile schema satisfies
  exact {
    assertions
    bounds
    inputBounds := fun requirement member ordinary =>
      inputBounds requirement (List.mem_append_right _ member) (inputSchema requirement member) ordinary
    publicInputs := satisfies.publicInputs.symm.trans (inputValues_of_descriptors descriptors _ _)
    privateInputs := satisfies.privateInputs.symm.trans (inputValues_of_descriptors descriptors _ _)
    impact := (impactPayloads accepted rowsParsed decoding profile schema inputGuards satisfies).symm
    returns := (returnValues accepted rowsParsed decoding profile schema satisfies).symm
  }

end Noctium.Verification.ScalarValidatedProgram
