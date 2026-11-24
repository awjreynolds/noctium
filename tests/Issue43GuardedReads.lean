import Noctium.Backend.Impact
import Noctium.Backend.NativeExpected
import Noctium.Backend.Zkir
import Noctium.Frontend
import Noctium.Verification.GenericStateCircuitParts
import Noctium.Verification.GuardedImpactObservation
import Noctium.Verification.GuardedScalarInput
import Noctium.Verification.RangeDedupAcceptedArray
import Noctium.Verification.ScalarValidationProjection
import Noctium.Verification.ScalarValidationOpcodeProfile

open scoped Noctium
open Lean Noctium

noctium_circuit issue43GuardedReads where
  public account : Native
  public enabled : Bool
end

noctium_contract Issue43GuardedReads where
  cell marker : Native
  map balances : Native => Native
  entry update uses issue43GuardedReads where
    member balances[account] as existed
    when existed read marker as skippedCell
    when existed read balances[account] as missingValue
    when eq(existed, false) insert balances[account] := 99
    when eq(existed, false) member balances[account] as initialized
    when initialized read balances[account] as currentValue
    when enabled read marker as markerValue
  end
end

private def issue43GuardedEntry : Entrypoint :=
  match Issue43GuardedReads.entrypoints with
  | ep :: _ => ep
  | _ => {name := "missing", circuit := {name := "missing"}}

private def issue43GuardedInputs : EvalEnv := [
  ("account", .native 7), ("enabled", .bool Bool.true)]

private def issue43GuardedState : LedgerState := {
  cells := [("marker", .native 23)]
  maps := [("balances", [])]
}

private def issue43GuardedContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by this fixture"
}

private def issue43ExpectedInputFactsCheck : _root_.Bool :=
  match Backend.Native.expectedEntrypoint Issue43GuardedReads.state
      (Passes.pruneEntrypoint issue43GuardedEntry) with
  | .error _ => Bool.false
  | .ok expected => expected.inputs.all fun requirement =>
      !requirement.ty.isForeign &&
        (requirement.identifier != "%input_skippedCell" ||
          requirement.activityGuard == some (.input "%input_existed"))

private theorem issue43ExpectedInputFactsCheck_passes :
    issue43ExpectedInputFactsCheck = Bool.true := by
  decide +kernel

/-- The actual lowered Issue 43 producer trace proves meaning through the
five strict prefix rows, then validates the exact guarded public input. -/
private theorem acceptedIssue43SkippedCellSuffix
    {hash : Verification.NativeRelation.Hash}
    {inputs : Verification.NativeRelation.Assignment} {assignment : Verification.NativeRelation.Assignment}
    (program : Json)
    (lowered : Backend.Zkir.lowerEntrypoint Issue43GuardedReads.state
      issue43GuardedEntry = .ok program)
    (header : Backend.Native.arrayField program "inputs" = .ok #[])
    (inputAgreement : ∀ expected,
      Backend.Native.expectedEntrypoint Issue43GuardedReads.state
        (Passes.pruneEntrypoint issue43GuardedEntry) = .ok expected →
      ∀ requirement, requirement ∈ expected.inputs →
        assignment requirement.identifier = inputs requirement.identifier)
    {prelude rest : List Json} {raw : Json}
    {prefixInstructions : List Verification.NativeRelation.Instruction}
    (split : ∃ instructions : Array Json,
      Backend.Native.arrayField program "instructions" = .ok instructions ∧
      instructions.toList = prelude ++ raw :: rest)
    (decoded : (prelude.zipIdx.map Prod.fst).mapM
      Verification.NativeRelationJson.decodeInstruction = .ok prefixInstructions)
    (profile : Verification.ScalarValidationOpcodeProfile.checkedScalarOpcodeProfile
      prelude.zipIdx prefixInstructions = Bool.true)
    (holds : ∀ instruction ∈ prefixInstructions,
      Verification.NativeRelation.Instruction.Holds hash assignment instruction)
    (targetOpcode : Backend.Native.stringField raw "op" = .ok "public_input")
    (targetOutput : Backend.Native.stringField raw "output" = .ok "%input_skippedCell")
    (targetGuard : Verification.NativeRelationJson.decodeOperandField raw "guard" =
      .ok (.reference "%input_existed"))
    (stream : List Verification.NativeRelation.Scalar) :
    ∃ (expected : Backend.Native.Expected) (before after : Backend.Native.State)
      (requirement : Backend.Native.InputRequirement),
      Backend.Native.validateInstruction expected before raw = .ok after ∧
      requirement.identifier = "%input_skippedCell" ∧
      requirement.activityGuard = some (.input "%input_existed") ∧
      Verification.ScalarValidationMeaning.StateMeaning hash inputs assignment before ∧
      Verification.ScalarValidationArithmeticLoop.NativeDefinitions before ∧
      Verification.ScalarValidationMeaning.StateMeaning hash inputs assignment after ∧
      Verification.ScalarValidationArithmeticLoop.NativeDefinitions after ∧
      ((Verification.ScalarNormalization.interpret hash inputs (.input "%input_existed") =
          some Verification.NativeRelation.zero ∧
        Verification.GuardedScalarInput.consume
          (Verification.NativeRelation.Operand.reference "%input_existed" |>.read assignment) stream =
            some (Verification.NativeRelation.zero, stream)) ∨
       (Verification.ScalarNormalization.interpret hash inputs (.input "%input_existed") =
          some Verification.NativeRelation.one ∧
        Verification.GuardedScalarInput.consume
          (Verification.NativeRelation.Operand.reference "%input_existed" |>.read assignment) stream =
            match stream with
            | value :: rest => some (value, rest)
            | [] => none)) := by
  obtain ⟨_, expected, _, expectedAccepted, validated, _⟩ :=
    Backend.Zkir.lowerEntrypoint_validation_and_instructions
      Issue43GuardedReads.state issue43GuardedEntry program lowered
  obtain ⟨_, instructions, final, driver⟩ :=
    Verification.ScalarValidationProjection.validate_driver_result_empty_header
      validated header
  rcases split with ⟨sourceRows, sourceParsed, splitRows⟩
  have sourceEqualsDriver : sourceRows = instructions :=
    Except.ok.inj (sourceParsed.symm.trans driver.instructionsParsed)
  cases sourceEqualsDriver
  have check : expected.inputs.all (fun requirement =>
      !requirement.ty.isForeign &&
        (requirement.identifier != "%input_skippedCell" ||
          requirement.activityGuard == some (.input "%input_existed"))) = Bool.true := by
    have h := issue43ExpectedInputFactsCheck_passes
    unfold issue43ExpectedInputFactsCheck at h
    rw [expectedAccepted] at h
    exact h
  have checkedRow := List.all_eq_true.mp check
  have schema : ∀ requirement, requirement ∈ expected.inputs →
      requirement.ty.isForeign = Bool.false := by
    intro requirement inputMember
    have row := checkedRow requirement inputMember
    have notForeign := (Bool.and_eq_true_iff.mp row).1
    cases foreign : requirement.ty.isForeign <;> simp [foreign] at notForeign ⊢
  have skippedGuard : ∀ requirement, requirement ∈ expected.inputs →
      requirement.identifier = "%input_skippedCell" →
      requirement.activityGuard = some (.input "%input_existed") := by
    intro requirement inputMember identifier
    have row := checkedRow requirement inputMember
    have guardMatches := (Bool.and_eq_true_iff.mp row).2
    rw [identifier] at guardMatches
    simp at guardMatches
    exact guardMatches
  have agreement := inputAgreement expected expectedAccepted
  have steps := Verification.RangeDedupAcceptedArray.checkedScalarOpcodeProfile_acceptedMeaningSteps
    decoded profile holds
  obtain ⟨before, after, prefixAccepted, rowAccepted, beforeMeaning, beforeDefinitions⟩ :=
    Verification.RangeDedupAcceptedArray.accepted_prefix_meaning
      (Verification.ScalarValidationMeaning.empty_meaning hash inputs assignment)
      Verification.ScalarValidationNativeDefinitions.empty_nativeDefinitions
      schema agreement steps driver.instructionTrace splitRows
  obtain ⟨requirement, selected⟩ :=
    Verification.ScalarValidationNativeLoop.accepted_input_requirement_selected
      (visibility := .«public») targetOpcode rowAccepted
  have inputMember := List.mem_of_getElem? selected
  have nonforeign := schema requirement inputMember
  have outputDescriptor := Verification.NativeInputOrdinal.accepted_input_output_descriptor
    (visibility := .«public») selected nonforeign targetOpcode rowAccepted
  have requirementId : requirement.identifier = "%input_skippedCell" :=
    Except.ok.inj (outputDescriptor.1.symm.trans targetOutput)
  have guarded := skippedGuard requirement inputMember requirementId
  obtain ⟨afterMeaning, afterDefinitions⟩ :=
    Verification.RangeDedupAcceptedArray.accepted_guarded_public_input_preserves
      beforeMeaning beforeDefinitions selected nonforeign guarded
      (agreement requirement inputMember) targetOpcode rowAccepted
  have transcript := Verification.GuardedScalarInput.consume_accepted_public_read
    stream beforeMeaning selected nonforeign guarded targetOpcode rowAccepted targetGuard
  exact ⟨expected, before, after, requirement, rowAccepted, requirementId, guarded,
    beforeMeaning, beforeDefinitions, afterMeaning, afterDefinitions, transcript⟩


#guard match issue43GuardedEntry.run issue43GuardedContext issue43GuardedInputs issue43GuardedState with
  | .ok (outputs, after) => outputs.isEmpty &&
      after.cells.lookup "marker" == some (.native 23) &&
      after.maps.lookup "balances" == some [(.native 7, .native 99)]
  | .error _ => Bool.false

private def replaceJsonField (value : Json) (name : String) (replacement : Json) : Json :=
  match value.getObj? with
  | .error _ => value
  | .ok object => Json.mkObj ((object.toList.filter (·.1 != name)) ++ [(name, replacement)])

private def guardedReadMutationRejected (change : List Json → List Json) : _root_.Bool :=
  match Backend.Native.expectedEntrypoint Issue43GuardedReads.state issue43GuardedEntry,
      Backend.Zkir.lowerEntrypoint Issue43GuardedReads.state issue43GuardedEntry with
  | .ok expected, .ok program =>
    let instructions := (program.getObjValD "instructions").getArr?.toOption.getD #[]
    let changed := replaceJsonField program "instructions" (toJson (change instructions.toList))
    !(Backend.Native.validate expected changed).isOk
  | _, _ => Bool.false

private def removeFirstAssert : List Json → List Json
  | [] => []
  | instruction :: rest =>
    if (instruction.getObjValD "op").getStr?.toOption == some "assert" then rest
    else instruction :: removeFirstAssert rest

#guard guardedReadMutationRejected (fun instructions => instructions.map fun instruction =>
  if (instruction.getObjValD "op").getStr?.toOption == some "public_input" &&
      (instruction.getObjValD "output").getStr?.toOption == some "%input_skippedCell" then
    replaceJsonField instruction "guard" Json.null
  else instruction)

#guard guardedReadMutationRejected removeFirstAssert

private def emittedMarkerGuardMatches : Except String _root_.Bool := do
  let pruned := Passes.pruneEntrypoint issue43GuardedEntry
  let expected ← (Backend.Native.expectedEntrypoint Issue43GuardedReads.state pruned).mapError (·.message)
  let artifact ← (Backend.Zkir.lowerEntrypoint Issue43GuardedReads.state
    issue43GuardedEntry).mapError (·.message)
  let rawInputs ← Backend.Native.arrayField artifact "inputs"
  unless rawInputs.isEmpty do
    throw "fixture has raw inputs before the instruction trace"
  let instructions ← Backend.Native.arrayField artifact "instructions"
  let (prelude, rest) := instructions.toList.span fun row =>
    Backend.Native.opcode row != "public_input" ||
      (Backend.Native.stringField row "output").toOption != some "%input_markerValue"
  let raw :: _ := rest | throw "missing guarded marker read"
  let before ← Backend.Native.validateInstructionLoop expected prelude.zipIdx {}
  let _ ← Backend.Native.validateInstruction expected before raw
  let operand ← Verification.NativeRelationJson.decodeOperandField raw "guard"
  let some requirement := expected.inputs[before.inputCount]? | throw "missing source input row"
  let inactive : Verification.NativeRelation.Assignment := fun _ => Verification.NativeRelation.zero
  let active : Verification.NativeRelation.Assignment := fun _ => Verification.NativeRelation.one
  let observed := [Verification.NativeRelation.scalar 23]
  return requirement.identifier == "%input_markerValue" &&
    requirement.activityGuard == some (.input "%input_enabled") &&
    decide (operand = .reference "%input_enabled" ∧
      Verification.GuardedScalarInput.consume (operand.read inactive) observed =
        some (Verification.NativeRelation.zero, observed) ∧
      Verification.GuardedScalarInput.consume (operand.read active) observed =
        some (Verification.NativeRelation.scalar 23, []) ∧
      Verification.GuardedScalarInput.consume (operand.read active) [] = none)

#guard emittedMarkerGuardMatches.toOption == some Bool.true

private def emittedSkippedCellPrefixMatches : Except String _root_.Bool := do
  let pruned := Passes.pruneEntrypoint issue43GuardedEntry
  let expected ← (Backend.Native.expectedEntrypoint Issue43GuardedReads.state pruned).mapError (·.message)
  let artifact ← (Backend.Zkir.lowerEntrypoint Issue43GuardedReads.state
    issue43GuardedEntry).mapError (·.message)
  let instructions ← Backend.Native.arrayField artifact "instructions"
  let (prelude, rest) := instructions.toList.span fun row =>
    Backend.Native.opcode row != "public_input" ||
      (Backend.Native.stringField row "output").toOption != some "%input_skippedCell"
  let raw :: _ := rest | throw "missing guarded skippedCell read"
  let before ← Backend.Native.validateInstructionLoop expected prelude.zipIdx {}
  let _ ← Backend.Native.validateInstruction expected before raw
  let decoded ← prelude.mapM Verification.NativeRelationJson.decodeInstruction
  let profile := Verification.ScalarValidationOpcodeProfile.checkedScalarOpcodeProfile
    prelude.zipIdx decoded
  let some requirement := expected.inputs[before.inputCount]? | throw "missing skippedCell input"
  return profile && prelude.map Backend.Native.opcode == ["public_input", "public_input",
      "constrain_to_boolean", "public_input", "constrain_to_boolean"] &&
    requirement.identifier == "%input_skippedCell" &&
    requirement.activityGuard == some (.input "%input_existed")

#guard emittedSkippedCellPrefixMatches.toOption == some Bool.true

private def emittedGuardedImpactMatches : Except String _root_.Bool := do
  let pruned := Passes.pruneEntrypoint issue43GuardedEntry
  let expected ← (Backend.Native.expectedEntrypoint Issue43GuardedReads.state pruned).mapError (·.message)
  let plan ← (Backend.Impact.lower Issue43GuardedReads.state pruned).mapError (·.message)
  let artifact ← (Backend.Zkir.lowerEntrypoint Issue43GuardedReads.state
    issue43GuardedEntry).mapError (·.message)
  let rawInputs ← Backend.Native.arrayField artifact "inputs"
  unless rawInputs.isEmpty do
    throw "fixture has raw inputs before the instruction trace"
  let instructions ← Backend.Native.arrayField artifact "instructions"
  let (prelude, rest) := instructions.toList.span fun row =>
    Backend.Native.opcode row != "impact" ||
      (Backend.Native.stringField row "guard").toOption != some "%input_enabled" ||
      !((Backend.Native.arrayField row "inputs").toOption.getD #[]).any
        (·.getStr?.toOption == some "%input_markerValue")
  let raw :: _ := rest | throw "missing guarded marker Impact payload"
  let before ← Backend.Native.validateInstructionLoop expected prelude.zipIdx {}
  let after ← Backend.Native.validateInstruction expected before raw
  let sourceGuards := Verification.GenericStateCircuitParts.activityGuardSources plan
  let some (some (.ref sourceName)) := sourceGuards[before.groupCount]?
    | throw "missing source Impact condition"
  let guard ← Verification.NativeRelationJson.decodeOperandField raw "guard"
  let operands ← Verification.NativeRelationJson.decodeOperands (← raw.getObjVal? "inputs")
  let some guardTerm := Verification.ScalarValidationOutputMeaning.sourceImpactGuard expected before
    | throw "missing source Impact guard"
  let some group := expected.groups[before.groupCount]? | throw "missing source Impact group"
  let inactive : Verification.NativeRelation.Assignment := fun name =>
    if name == "%input_enabled" then Verification.NativeRelation.zero
    else Verification.NativeRelation.scalar 23
  let active : Verification.NativeRelation.Assignment := fun name =>
    if name == "%input_enabled" then Verification.NativeRelation.one
    else Verification.NativeRelation.scalar 23
  let masked := Verification.GuardedImpactObservation.observeImpact
    (guard.read inactive) (operands.map (·.read inactive))
  let payload := operands.map (·.read active)
  let observed := Verification.GuardedImpactObservation.observeImpact
    (guard.read active) payload
  let unusedHash : Verification.NativeRelation.Hash := fun _ => Verification.NativeRelation.zero
  let suffix := [Verification.NativeRelation.scalar 99]
  let stepObservation := fun (row : Option Verification.GuardedImpactObservation.Observation)
      transcript => row >>= (Verification.GuardedImpactObservation.consume · transcript)
  let changed := replaceJsonField raw "guard" (toJson ("0x01" : String))
  return after.groupCount == before.groupCount + 1 &&
    sourceName == "enabled" &&
    guardTerm == .input "%input_enabled" &&
    group.length == operands.length &&
    !(Backend.Native.validateInstruction expected before changed).isOk &&
    decide (Verification.GuardedImpactObservation.sourceObservation unusedHash inactive guardTerm group =
      masked ∧ Verification.GuardedImpactObservation.sourceObservation unusedHash active guardTerm group =
      observed ∧ masked = some ⟨Bool.false, List.replicate group.length Verification.NativeRelation.zero⟩ ∧
      observed = some ⟨Bool.true, payload⟩ ∧
      stepObservation masked suffix = some suffix ∧
      stepObservation observed (payload ++ suffix) = some suffix ∧
      stepObservation observed payload.dropLast = none ∧
      stepObservation observed (Verification.NativeRelation.zero :: payload.drop 1) = none)

#guard emittedGuardedImpactMatches.toOption == some Bool.true
