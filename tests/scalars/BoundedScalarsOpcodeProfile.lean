import Lean
import examples.BoundedScalars
import Noctium.Verification.NativeInputOrdinalTrace
import Noctium.Verification.NativeRelationInstructionProjection
import Noctium.Verification.NativeRelationJson
import Noctium.Verification.RangeDedupAcceptedEntrypoint
import Noctium.Verification.ScalarAllocationOutputFrame
import Noctium.Verification.ScalarValidationOpcodeProfile
import Noctium.Verification.ScalarValidationProjection

namespace BoundedScalarsOpcodeProfile

open Noctium
open Lean
open Noctium.Backend
open Noctium.Backend.Native
open Noctium.Verification.NativeInputOrdinalTrace
open Noctium.Verification.NativeRelation
open Noctium.Verification.NativeRelationJson
open Noctium.Verification.RangeDedupAcceptedArray
open Noctium.Verification.ScalarValidationArithmeticLoop (NativeDefinitions)
open Noctium.Verification.ScalarValidationMeaning (StateMeaning)
open Noctium.Verification.ScalarValidationOpcodeProfile
open Noctium.Verification.ScalarValidationNativeDefinitions

/-- Select the source entrypoint compiled from `BoundedScalars.apply`. -/
def selectedEntrypoint : Entrypoint :=
  (BoundedScalars.entrypoints.find? (·.name == "apply")).getD {name := "", circuit := {name := ""}}

def loweredResult := Zkir.lowerEntrypoint BoundedScalars.state selectedEntrypoint

def emittedProgram : Json := loweredResult.toOption.getD Json.null

def emittedInstructions : Array Json :=
  (Noctium.Backend.Native.arrayField emittedProgram "instructions").toOption.getD #[]

def emittedItems : List (Json × Nat) := emittedInstructions.toList.zipIdx

def decodedProgram : Program :=
  (Noctium.Verification.NativeRelationJson.decode emittedProgram).toOption.getD
    (Noctium.Verification.NativeRelation.Program.mk [] 0 Bool.false)

def boundedApplyImpactPlan : Impact.Plan :=
  (Impact.lower BoundedScalars.state (Passes.pruneEntrypoint selectedEntrypoint)).toOption.getD {}

def decodedImpactGroupWidths (program : Program) : List Nat :=
  program.instructions.filterMap fun instruction =>
    match instruction with
    | .impact _ values => some values.length
    | _ => none

def impactPlanGroupWidths (plan : Impact.Plan) : List Nat :=
  plan.fieldGroups.map List.length

-- Keep this closed compiler-output check in the fixture. The general profile
-- and validation theorems build without trusting native reduction.
#guard selectedEntrypoint.name == "apply"
#guard !emittedItems.isEmpty

/-- Evaluate the actual entrypoint lowering, strict relation decoder, and
opcode-shape profile for the closed BoundedScalars source program. -/
theorem boundedApply_profileEvidence :
    loweredResult.isOk = Bool.true ∧
    (Noctium.Verification.NativeRelationJson.decode emittedProgram).isOk = Bool.true ∧
    (Noctium.Backend.Native.arrayField emittedProgram "instructions").isOk = Bool.true ∧
    checkedScalarOpcodeProfile emittedItems decodedProgram.instructions = Bool.true := by
  native_decide

theorem boundedApply_lowered :
    loweredResult = .ok emittedProgram := by
  have successful := boundedApply_profileEvidence.1
  cases lowered : loweredResult with
  | error message => simp [lowered, Except.isOk, Except.toBool] at successful
  | ok program => simp [emittedProgram, lowered, Except.toOption]

theorem boundedApply_decoded :
    Noctium.Verification.NativeRelationJson.decode emittedProgram = .ok decodedProgram := by
  have successful := boundedApply_profileEvidence.2.1
  cases parsed : Noctium.Verification.NativeRelationJson.decode emittedProgram with
  | error message => simp [parsed, Except.isOk, Except.toBool] at successful
  | ok program => simp [decodedProgram, parsed, Except.toOption]

theorem boundedApply_instructionsParsed :
    Noctium.Backend.Native.arrayField emittedProgram "instructions" = .ok emittedInstructions := by
  have successful := boundedApply_profileEvidence.2.2.1
  cases parsed : Noctium.Backend.Native.arrayField emittedProgram "instructions" with
  | error message => simp [parsed, Except.isOk, Except.toBool] at successful
  | ok instructions => simp [emittedInstructions, parsed, Except.toOption]

/-- This profile covers the raw instructions emitted for BoundedScalars.apply. -/
theorem boundedApply_checkedScalarOpcodeProfile :
    checkedScalarOpcodeProfile emittedItems decodedProgram.instructions = Bool.true :=
  boundedApply_profileEvidence.2.2.2

/-- The lowerer connects this exact JSON to the mandatory native producer
validation and the instructions emitted by its source plan. -/
theorem boundedApply_nativeAdmission :
    ∃ plan expected,
      Impact.lower BoundedScalars.state (Passes.pruneEntrypoint selectedEntrypoint) = .ok plan ∧
      Noctium.Backend.Native.expectedEntrypoint BoundedScalars.state
        (Passes.pruneEntrypoint selectedEntrypoint) = .ok expected ∧
      Noctium.Backend.Native.validate expected emittedProgram = .ok () ∧
      Noctium.Backend.Native.arrayField emittedProgram "instructions" =
        .ok ((Zkir.lowerEntrypointBody (Passes.pruneEntrypoint selectedEntrypoint) plan).run {}).2.instructions :=
  by
    obtain ⟨plan, expected, _, impact, schedule, validated, parsed, emitted, _⟩ :=
      Noctium.Verification.NativeRelationInstructionProjection.lowerEntrypoint_instructionProjection
        BoundedScalars.state selectedEntrypoint emittedProgram decodedProgram
        boundedApply_lowered boundedApply_decoded
    exact ⟨plan, expected, impact, schedule, validated, emitted ▸ parsed⟩

theorem boundedApply_instructionsDecode :
    (emittedItems.map Prod.fst).mapM Noctium.Verification.NativeRelationJson.decodeInstruction =
      .ok decodedProgram.instructions := by
  obtain ⟨instructions, parsed, decoded⟩ :=
    Noctium.Verification.NativeRelationInstructionProjection.decode_instructionProjection
      boundedApply_decoded
  have same : instructions = emittedInstructions :=
    Except.ok.inj (parsed.symm.trans boundedApply_instructionsParsed)
  subst instructions
  simpa [emittedItems, List.zipIdx_map_fst] using decoded

theorem boundedApply_decodedInstructionBudget :
    decodedProgram.instructions.length ≤ Native.maxInstructions := by
  obtain ⟨_, _, _, _, _, _, _, _, _, budget⟩ :=
    Noctium.Verification.NativeRelationInstructionProjection.lowerEntrypoint_decodedInstructionBudget
      BoundedScalars.state selectedEntrypoint emittedProgram decodedProgram
      boundedApply_lowered boundedApply_decoded
  exact budget

theorem boundedApply_aliasFrame :
    Zkir.PreservesOutputCapacityFrame
      (Zkir.lowerEntrypointAliases (Passes.pruneEntrypoint selectedEntrypoint)) := by
  apply Zkir.lowerEntrypointAliases_preservesOutputCapacityFrame
  intro aliased ha
  change aliased ∈ [boundedRelation.outputs[0]'(by decide)] at ha
  rw [List.mem_singleton.mp ha]
  exact Noctium.Verification.ScalarAllocationOutputFrame.lowerExpr_admitted_preservesOutputCapacityFrame
    _ (.ref _ (.uint _))

/-- The actual default ledger body stays within the decoder's identifier budget.
The kernel evaluates the concrete allocation frame. Producer acceptance supplies
the separate limit on emitted output slots. -/
theorem boundedApply_emittedNameBudget (program : Json)
    (accepted : loweredResult = .ok program) :
    ∃ plan, Impact.lower BoundedScalars.state (Passes.pruneEntrypoint selectedEntrypoint) = .ok plan ∧
      let next := ((Zkir.lowerEntrypointBody (Passes.pruneEntrypoint selectedEntrypoint) plan).run {}).2.next
      next ≤ Native.maxInstructions * Native.maxVectorLength ∧
        ∀ index, index < next →
          Noctium.Verification.NativeRelationJson.validIdentifier s!"%v{index}" = Bool.true := by
  apply Noctium.Verification.ScalarAllocationOutputFrame.lowerEntrypoint_name_budget_of_frame
    BoundedScalars.state selectedEntrypoint program accepted
  intro plan lowered
  have canonical : plan = boundedApplyImpactPlan := by
    rw [boundedApplyImpactPlan, lowered]
    rfl
  subst plan
  constructor <;> decide +kernel

/-- The exact decoded BoundedScalars.apply vector now yields the native trace
without a caller-authored opcode trace or profile premise. -/
theorem boundedApply_nativeDefinitionTrace :
    NativeDefinitionTrace emittedItems decodedProgram.instructions :=
  NativeDefinitionTrace.ofDecodedCheckedProfile boundedApply_instructionsDecode
    boundedApply_checkedScalarOpcodeProfile

/-- The closed profile trace is the indexed instruction vector consumed by the
real `Native.validate` driver. The generic projection theorem supplies the
producer fold and its final state from the validator's successful result. -/
theorem boundedApply_nativeValidationTrace :
    ∃ plan expected rawInputs seed final,
      Impact.lower BoundedScalars.state (Passes.pruneEntrypoint selectedEntrypoint) = .ok plan ∧
      Noctium.Backend.Native.expectedEntrypoint BoundedScalars.state
        (Passes.pruneEntrypoint selectedEntrypoint) = .ok expected ∧
      Noctium.Backend.Native.validate expected emittedProgram = .ok () ∧
      Noctium.Verification.ScalarValidationProjection.NativeValidationDriverFacts
        expected emittedProgram emittedInstructions rawInputs seed final ∧
      NativeDefinitionTrace emittedItems decodedProgram.instructions := by
  obtain ⟨plan, expected, lowered, expectedParsed, validated, _⟩ :=
    boundedApply_nativeAdmission
  obtain ⟨instructions, rawInputs, seed, final, driverFacts⟩ :=
    Noctium.Verification.ScalarValidationProjection.validate_driver_result validated
  have instructionsMatch : instructions = emittedInstructions :=
    Except.ok.inj (driverFacts.instructionsParsed.symm.trans boundedApply_instructionsParsed)
  subst instructions
  exact ⟨plan, expected, rawInputs, seed, final, lowered, expectedParsed, validated,
    driverFacts, boundedApply_nativeDefinitionTrace⟩

private def isOldRead (requirement : Native.InputRequirement) : _root_.Bool :=
  requirement.identifier == "%input_old" && decide (requirement.ty = .uint 510) &&
    decide (requirement.canonicalJubjubScalar = Bool.false)

private def boundedApplyScalarInputs : _root_.Bool :=
  match Native.expectedEntrypoint BoundedScalars.state (Passes.pruneEntrypoint selectedEntrypoint) with
  | .ok expected =>
    expected.rawInputs.isEmpty && expected.inputs.all (fun item => !item.ty.isForeign) &&
      expected.inputs.any isOldRead
  | .error _ => Bool.false

private theorem boundedApplyScalarInputs_checked : boundedApplyScalarInputs = Bool.true := by
  decide +kernel

open Noctium.Verification.ScalarNormalization (interpret) in
/-- The final producer checks give the ledger-read bound and each range
requirement in the exact typed schedule of the emitted fixture. -/
theorem boundedApply_checkedRanges {hash : Hash} {assignment : Assignment}
    (holds : ∀ instruction ∈ decodedProgram.instructions, Instruction.Holds hash assignment instruction) :
    (assignment "%input_old").val ≤ 510 ∧
      ∃ expected, Native.expectedEntrypoint BoundedScalars.state
        (Passes.pruneEntrypoint selectedEntrypoint) = .ok expected ∧
        ∀ requirement ∈ expected.bounds,
          ∃ value, interpret hash assignment requirement.1 = some value ∧
            value.val ≤ requirement.2 := by
  obtain ⟨_, expected, _, seed, final, _, schedule, _, driver, trace⟩ :=
    boundedApply_nativeValidationTrace
  have checked := boundedApplyScalarInputs_checked
  simp only [boundedApplyScalarInputs, schedule, Bool.and_eq_true] at checked
  obtain ⟨⟨emptyHeader, scalarInputs⟩, readFound⟩ := checked
  have empty : expected.rawInputs = [] := List.isEmpty_iff.mp emptyHeader
  cases driver.emptyRawSeed empty
  have schema : ∀ requirement ∈ expected.inputs, requirement.ty.isForeign = Bool.false := by
    intro requirement inList
    simpa using List.all_eq_true.mp scalarInputs requirement inList
  obtain ⟨meaning, _, _⟩ := accepted_loop_meaning_at_steps
    (Noctium.Verification.ScalarValidationMeaning.empty_meaning hash assignment assignment)
    empty_nativeDefinitions schema (fun _ _ => rfl)
    (nativeDefinitionTrace_acceptedMeaningSteps trace holds) driver.instructionTrace
  obtain ⟨requirement, inList, fieldChecks⟩ := List.any_eq_true.mp readFound
  simp only [isOldRead, Bool.and_eq_true, decide_eq_true_eq] at fieldChecks
  obtain ⟨⟨name, ty⟩, ordinary⟩ := fieldChecks
  have bound := driver.inputBound meaning (List.mem_append_right _ inList)
    (schema requirement inList) ordinary
  refine ⟨?_, expected, schedule, driver.rangeRequirements meaning⟩
  simpa [eq_of_beq name, ty, Native.sourceMaximum] using bound

open Noctium.Verification.ScalarNormalization (interpret) in
/-- Every satisfying assignment of the emitted relation satisfies every
assertion in the corresponding validated source schedule. -/
theorem boundedApply_checkedAssertions {hash : Hash} {assignment : Assignment}
    {streams : InputStreams} {groups : List (List Scalar)}
    (satisfies : CircuitSatisfies hash decodedProgram streams assignment groups) :
    ∃ expected, Native.expectedEntrypoint BoundedScalars.state
      (Passes.pruneEntrypoint selectedEntrypoint) = .ok expected ∧
      ∀ term ∈ expected.assertions, interpret hash assignment term = some one := by
  have schema : ∀ expected,
      Native.expectedEntrypoint BoundedScalars.state
        (Passes.pruneEntrypoint selectedEntrypoint) = .ok expected →
      ∀ requirement ∈ expected.inputs, requirement.ty.isForeign = Bool.false := by
    intro expected schedule requirement inList
    have checked := boundedApplyScalarInputs_checked
    simp only [boundedApplyScalarInputs, schedule, Bool.and_eq_true] at checked
    simpa using List.all_eq_true.mp checked.1.2 requirement inList
  obtain ⟨expected, schedule, assertions⟩ :=
    Noctium.Verification.RangeDedupAcceptedEntrypoint.lowerEntrypoint_satisfies_sourceAssertions
      BoundedScalars.state selectedEntrypoint .disabled boundedApply_lowered boundedApply_decoded
      boundedApply_instructionsParsed boundedApply_checkedScalarOpcodeProfile schema
  exact ⟨expected, schedule, assertions satisfies⟩

theorem boundedApply_oldReadBound {hash : Hash} {assignment : Assignment}
    (holds : ∀ instruction ∈ decodedProgram.instructions, Instruction.Holds hash assignment instruction) :
    (assignment "%input_old").val ≤ 510 :=
  (boundedApply_checkedRanges holds).1

/-- The decoded input rows of the accepted fixture preserve source visibility,
names and order for the strict scalar input fragment. Its empty producer seed
is derived from the emitted header. -/
theorem boundedApply_decodedInputDescriptors
    (inputSchema : ∀ expected,
      Native.expectedEntrypoint BoundedScalars.state
        (Passes.pruneEntrypoint selectedEntrypoint) = .ok expected →
      ∀ requirement ∈ expected.inputs, requirement.ty.isForeign = Bool.false) :
    ∃ expected,
      Native.expectedEntrypoint BoundedScalars.state
        (Passes.pruneEntrypoint selectedEntrypoint) = .ok expected ∧
      expected.rawInputs = [] ∧
      decodedProgram.instructions.flatMap strictInstructionInputDescriptors =
        expected.inputs.map expectedInputDescriptor :=
  lowerEntrypoint_inputDescriptors_of_checkedScalarProfile .disabled BoundedScalars.state
    selectedEntrypoint emittedProgram decodedProgram boundedApply_lowered boundedApply_decoded
    inputSchema ⟨emittedInstructions, boundedApply_instructionsParsed,
      boundedApply_checkedScalarOpcodeProfile⟩

private def boundedApply_rangeInputDescriptorsMatch : _root_.Bool :=
  match Zkir.lowerEntrypoint BoundedScalars.state selectedEntrypoint .rangeAndAssertions,
      Native.expectedEntrypoint BoundedScalars.state (Passes.pruneEntrypoint selectedEntrypoint) with
  | .ok artifact, .ok expected =>
    match Noctium.Verification.NativeRelationJson.decode artifact,
        Native.arrayField artifact "instructions" with
    | .ok relation, .ok instructions =>
      checkedScalarOpcodeProfile instructions.toList.zipIdx relation.instructions &&
        expected.rawInputs.isEmpty &&
        relation.instructions.flatMap strictInstructionInputDescriptors ==
          expected.inputs.map expectedInputDescriptor
    | _, _ => Bool.false
  | _, _ => Bool.false

#guard boundedApply_rangeInputDescriptorsMatch

/-- Exact decoding of production `BoundedScalars.apply` preserves each ordered
Impact group boundary and width from its actual Impact plan. This is the first
structural join between the optimized ZKIR target and ledger schedule; values
and their witness semantics remain separate obligations. -/
theorem boundedApply_decodedImpactGroupWidths :
    loweredResult = .ok emittedProgram ∧
    Noctium.Verification.NativeRelationJson.decode emittedProgram = .ok decodedProgram ∧
    Impact.lower BoundedScalars.state (Passes.pruneEntrypoint selectedEntrypoint) =
      .ok boundedApplyImpactPlan ∧
    decodedImpactGroupWidths decodedProgram = impactPlanGroupWidths boundedApplyImpactPlan := by
  refine ⟨boundedApply_lowered, boundedApply_decoded, ?_, ?_⟩
  · obtain ⟨plan, _, lowered, _, _, _⟩ := boundedApply_nativeAdmission
    rw [lowered]
    apply congrArg Except.ok
    change plan = (Impact.lower BoundedScalars.state
      (Passes.pruneEntrypoint selectedEntrypoint)).toOption.getD {}
    rw [lowered]
    rfl
  · native_decide

/-- The full ordered public Impact payload of the emitted BoundedScalars.apply
relation agrees with the source schedule under the admitted input schema,
source assignment agreement and satisfaction of the decoded circuit. -/
theorem boundedApply_acceptedImpactPayloads :
    ∃ expected seed final,
      Native.expectedEntrypoint BoundedScalars.state
        (Passes.pruneEntrypoint selectedEntrypoint) = .ok expected ∧
      Native.validateInstructionLoop expected emittedItems seed = .ok final ∧
      ∀ (hash : Hash) (inputs assignment : Assignment) (streams : InputStreams)
        (groups : List (List Scalar)),
        expected.rawInputs = [] →
        (∀ requirement ∈ expected.inputs, requirement.ty.isForeign = Bool.false) →
        (∀ requirement ∈ expected.inputs, requirement.activityGuard = none) →
        (∀ requirement ∈ expected.inputs,
          assignment requirement.identifier = inputs requirement.identifier) →
        CircuitSatisfies hash decodedProgram streams assignment groups →
        expected.groups.map (List.map
          (Noctium.Verification.ScalarNormalization.interpret hash inputs)) =
          groups.map (List.map some) := by
  obtain ⟨_, expected, _, seed, final, _, source, _, driver, trace⟩ :=
    boundedApply_nativeValidationTrace
  refine ⟨expected, seed, final, source, driver.instructionTrace, ?_⟩
  intro hash inputs assignment streams groups noRawInputs inputSchema inputGuards inputAgreement sat
  have seedEmpty := driver.emptyRawSeed noRawInputs
  have meaning : StateMeaning hash inputs assignment seed := by
    rw [seedEmpty]
    intro name fact factMember
    simp at factMember
  have definitions : NativeDefinitions seed := by
    rw [seedEmpty]
    intro name fact factMember
    simp at factMember
  have ordered := acceptedProfileOrderedImpactPayloads trace meaning definitions inputSchema
    inputGuards inputAgreement sat.instructions driver.instructionTrace
  rw [driver.groupCount, seedEmpty] at ordered
  have decodedGroups : (Program.mk decodedProgram.instructions 0 Bool.false).groups assignment =
      decodedProgram.groups assignment := rfl
  simpa only [List.take_length, Native.State.groupCount, List.take_zero,
    List.map_nil, List.nil_append, decodedGroups, sat.groups] using ordered

end BoundedScalarsOpcodeProfile
