import Noctium.Verification.GuardedImpactTranscript
import Noctium.Verification.GuardedPublicInputMeaning
import Noctium.Verification.GuardedScalarInput

namespace Noctium.Verification.GuardedInputTranscript

open Lean Backend NativeRelation GuardedScalarRows GuardedImpactTranscript
open GuardedPublicInputMeaning GuardedScalarInput RangeDedupAcceptedArray
open ScalarValidationMeaning ScalarValidationRawSeedMeaning
open ScalarValidationArithmeticLoop (NativeDefinitions)
open ScalarValidationNativeLoop (inputOpcode)
open NativeInputOrdinal (accepted_input_row_step accepted_input_output_descriptor)

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private def inputSlot (witness : Assignment) : Row → Option (Option ReadObservation)
  | .publicInput output guard =>
    some (some ⟨(guard.map (Operand.read witness)).getD one, witness output⟩)
  | .strict (.input .private _) => some none
  | _ => none

/-- Public read observations of the decoded rows, in static order. -/
def emittedPublicReads (witness : Assignment) (rows : List Row) : List ReadObservation :=
  (rows.filterMap (inputSlot witness)).filterMap id

/-- Interpret one source input requirement as its transcript slot. A private
input contributes an empty slot, distinct from a missing or uninterpretable
source requirement. -/
def requirementObservation (hash : Hash) (inputs witness : Assignment)
    (requirement : Native.InputRequirement) : Option (Option ReadObservation) := do
  match requirement.visibility with
  | .private => pure none
  | .«public» =>
    let guard ← sourceReadGuard hash inputs requirement
    pure (some ⟨guard, witness requirement.identifier⟩)

/-- Every body input ordinal occupies a slot. -/
def expectedInputAt (hash : Hash) (inputs witness : Assignment) (expected : Native.Expected)
    (ordinal : Nat) : Option (Option ReadObservation) := do
  let requirement ← expected.inputs[ordinal]?
  requirementObservation hash inputs witness requirement

/-- Recover the source public read schedule by walking body input ordinals, then
remove the private input slots. Raw call arguments seed meaning separately. -/
def expectedPublicReads (hash : Hash) (inputs witness : Assignment) (expected : Native.Expected) :
    Option (List ReadObservation) :=
  ((List.range expected.inputs.length).mapM (expectedInputAt hash inputs witness expected)).map
    (List.filterMap id)

/-- Enumerating body input ordinals yields the same observations as traversing
the requirement list directly. -/
theorem expectedPublicReads_eq_requirements
    (hash : Hash) (inputs witness : Assignment) (expected : Native.Expected) :
    expectedPublicReads hash inputs witness expected =
      (expected.inputs.mapM (requirementObservation hash inputs witness)).map
        (List.filterMap id) := by
  have enumerate (requirements : List Native.InputRequirement)
      (observe : Native.InputRequirement → Option (Option ReadObservation)) :
      (List.range requirements.length).mapM
          (fun ordinal => (requirements[ordinal]?).bind observe) = requirements.mapM observe := by
    induction requirements with
    | nil => simp
    | cons requirement requirements ih =>
      simp [List.range_succ_eq_map, List.getElem?_cons_succ, Function.comp_def, ih]
  unfold expectedPublicReads
  change (((List.range expected.inputs.length).mapM
      (fun ordinal => (expected.inputs[ordinal]?).bind
        (requirementObservation hash inputs witness))).map (List.filterMap id)) = _
  rw [enumerate]

/-- The accepted producer assigns each decoded input the next static source
ordinal, independently of whether its guard consumes a transcript value. -/
theorem checked_public_read_schedule
    {hash : Hash} {inputs witness : Assignment} {expected : Native.Expected}
    {items : List (Json × Nat)} {rows : List Row} {initial final : Native.State}
    (decoded : (items.map Prod.fst).mapM decodeRow = .ok rows)
    (holds : ∀ row ∈ rows, ordinaryHolds hash witness row)
    (meaning : StateMeaning hash inputs witness initial)
    (definitions : NativeDefinitions initial)
    (inputSchema : ∀ requirement ∈ expected.inputs, requirement.ty.isForeign = false)
    (inputAgreement : ∀ requirement ∈ expected.inputs,
      witness requirement.identifier = inputs requirement.identifier)
    (accepted : Native.validateInstructionLoop expected items initial = .ok final) :
    let slots := rows.filterMap (inputSlot witness)
    final.inputCount = initial.inputCount + slots.length ∧
      (List.range' initial.inputCount slots.length).mapM
        (expectedInputAt hash inputs witness expected) = some slots := by
  induction items generalizing initial final rows with
  | nil =>
    change Except.ok [] = Except.ok rows at decoded
    cases decoded
    have same : initial = final := by injection accepted
    subst final
    exact ⟨by simp, rfl⟩
  | cons item rest ih =>
    rcases item with ⟨raw, index⟩
    simp only [List.map_cons, List.mapM_cons, bind_ok] at decoded
    obtain ⟨row, rowDecoded, tail, tailDecoded, sameRows⟩ := decoded
    cases sameRows
    rw [Native.validateInstructionLoop, List.forIn_cons] at accepted
    cases checked : Native.validateInstruction expected initial raw with
    | error message => simp [checked, Bind.bind, Except.bind] at accepted
    | ok next =>
      simp only [checked, bind_pure_comp] at accepted
      have step := classify_decoded_row rowDecoded (holds row (by simp))
      have ⟨nextMeaning, nextDefinitions, _⟩ := acceptedMeaningStep_preserves
        meaning definitions inputSchema inputAgreement step checked
      have ⟨tailCount, tailInputs⟩ := ih tailDecoded
        (fun item member => holds item (List.mem_cons_of_mem _ member))
        nextMeaning nextDefinitions accepted
      have count := acceptedMeaningStep_inputCount_step definitions inputSchema step checked
      have unchanged (slot : inputSlot witness row = none) (isInput : inputOpcodeRow raw = false) :
          let slots := (row :: tail).filterMap (inputSlot witness)
          final.inputCount = initial.inputCount + slots.length ∧
            (List.range' initial.inputCount slots.length).mapM
              (expectedInputAt hash inputs witness expected) = some slots := by
        have same : next.inputCount = initial.inputCount := by simpa [isInput] using count
        simp only [List.filterMap_cons, slot]
        rw [same] at tailCount tailInputs
        exact ⟨tailCount, tailInputs⟩
      have advanced {value : Option ReadObservation} (slot : inputSlot witness row = some value)
          (isInput : inputOpcodeRow raw = true)
          (source : expectedInputAt hash inputs witness expected initial.inputCount = some value) :
          let slots := (row :: tail).filterMap (inputSlot witness)
          final.inputCount = initial.inputCount + slots.length ∧
            (List.range' initial.inputCount slots.length).mapM
              (expectedInputAt hash inputs witness expected) = some slots := by
        have nextOrdinal : next.inputCount = initial.inputCount + 1 := by
          simpa [isInput] using count
        simp only [List.filterMap_cons, slot, List.length_cons]
        constructor
        · omega
        · rw [List.range'_succ, ← nextOrdinal]
          simp [List.mapM_cons, source, tailInputs]
      cases row with
      | publicInput output guard =>
        have opcode := (decodeRow_publicInput_fields rowDecoded).1
        obtain ⟨requirement, selected, visibility, outputEq, guardMeaning, _⟩ :=
          accepted_publicInput_meaning meaning inputSchema rowDecoded checked
        apply advanced rfl (by simp [inputOpcodeRow, opcode, inputOpcode])
        simp [expectedInputAt, requirementObservation, selected, visibility, guardMeaning, outputEq]
      | impact guard values =>
        have opcode := (decodeRow_impact_fields rowDecoded).1
        exact unchanged rfl (by simp [inputOpcodeRow, opcode, inputOpcode])
      | strict instruction =>
        have ordinary := (decodeRow_strict rowDecoded).1
        cases ordinary.supported with
        | publicInput _ opcode =>
          exact False.elim (decodeRow_strict_not_publicInput rowDecoded opcode)
        | privateInput output opcode =>
          have tagged : Native.stringField raw "op" = .ok (inputOpcode .private) := opcode
          obtain ⟨requirement, selected, _⟩ := accepted_input_row_step inputSchema tagged checked
          have nonforeign := inputSchema requirement (List.mem_of_getElem? selected)
          have visibility := (accepted_input_output_descriptor selected nonforeign tagged checked).2
          apply advanced rfl (by simp [inputOpcodeRow, opcode, inputOpcode])
          simp [expectedInputAt, requirementObservation, selected, visibility]
        | _ =>
          exact unchanged rfl (by simp_all [inputOpcodeRow, inputOpcode])

/-- Tie the whole guarded public input transcript to the actual emitted rows
and the compiler's expected input schedule. Successful consumption requires
zero witness values at inactive reads and consumes no fields for them. Raw
call arguments stay in the header. -/
theorem lowerEntrypoint_guardedInputTranscript
    {state : List StateDecl} {entry : Entrypoint} (rewrites : Zkir.Rewrites)
    {json : Json} {instructions : Array Json} {rows : List Row}
    (lowered : Zkir.lowerEntrypoint state entry rewrites = .ok json)
    (instructionsParsed : Native.arrayField json "instructions" = .ok instructions)
    (decoded : instructions.toList.mapM decodeRow = .ok rows)
    (schema : ∀ expected,
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected →
        ∀ requirement ∈ expected.rawInputs ++ expected.inputs,
          requirement.ty.isForeign = false) :
    ∃ plan expected,
      Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected ∧
      ∀ {hash witness}, (∀ row ∈ rows, ordinaryHolds hash witness row) →
        let reads := emittedPublicReads witness rows
        expectedPublicReads hash witness witness expected = some reads ∧
        ∀ transcript remaining,
          consumeReads (reads.map ReadObservation.guard) transcript =
            some (reads.map ReadObservation.value, remaining) ↔
          transcript = activeReadValues reads ++ remaining ∧
            ∀ read ∈ reads, read.guard = one ∨ (read.guard = zero ∧ read.value = zero) := by
  obtain ⟨plan, expected, planAccepted, expectedAccepted, validated, _⟩ :=
    Zkir.lowerEntrypoint_validation_and_instructions_with_rewrites
      state entry rewrites json lowered
  let optimized := Zkir.optimizedExpected rewrites expected
  obtain ⟨actualInstructions, _, seed, final, driver⟩ :=
    ScalarValidationProjection.validate_driver_result (expected := optimized) validated
  have sameRows := Except.ok.inj (driver.instructionsParsed.symm.trans instructionsParsed)
  subst actualInstructions
  have indexedDecoded : (instructions.toList.zipIdx.map Prod.fst).mapM decodeRow = .ok rows := by
    simpa only [List.zipIdx_map_fst] using decoded
  have inputsUnchanged :
      optimized.rawInputs ++ optimized.inputs = expected.rawInputs ++ expected.inputs := by
    cases rewrites <;> rfl
  have schemaOptimized : ∀ requirement ∈ optimized.rawInputs ++ optimized.inputs,
      requirement.ty.isForeign = false := by
    simpa only [inputsUnchanged] using schema expected expectedAccepted
  have rawSchema : ∀ requirement ∈ optimized.rawInputs, requirement.ty.isForeign = false :=
    fun requirement member => schemaOptimized requirement (List.mem_append_left _ member)
  have inputSchema : ∀ requirement ∈ optimized.inputs, requirement.ty.isForeign = false :=
    fun requirement member => schemaOptimized requirement (List.mem_append_right _ member)
  refine ⟨plan, expected, planAccepted, expectedAccepted, ?_⟩
  intro hash witness holds
  obtain ⟨seedMeaning, seedDefinitions⟩ :=
    seedRawInputs_meaning_and_nativeDefinitions (hash := hash) (inputs := witness)
      (witness := witness) rawSchema (fun _ _ => rfl) driver.seededRawInputs
  have ⟨count, source⟩ := checked_public_read_schedule indexedDecoded holds seedMeaning
    seedDefinitions inputSchema (fun _ _ => rfl) driver.instructionTrace
  have countExact : optimized.inputs.length = (rows.filterMap (inputSlot witness)).length := by
    simpa only [driver.inputCount, driver.seedInputCount, Nat.zero_add] using count
  have slots :
      (List.range optimized.inputs.length).mapM
        (expectedInputAt hash witness witness optimized) = some (rows.filterMap (inputSlot witness)) := by
    simpa only [driver.seedInputCount, ← List.range_eq_range', ← countExact] using source
  have preserved :
      expectedPublicReads hash witness witness optimized =
        expectedPublicReads hash witness witness expected := by cases rewrites <;> rfl
  have expectedReads : expectedPublicReads hash witness witness expected =
      some (emittedPublicReads witness rows) := by
    rw [← preserved]
    simp [expectedPublicReads, emittedPublicReads, slots]
  exact ⟨expectedReads, fun transcript remaining =>
    consumeReads_iff (emittedPublicReads witness rows) transcript remaining⟩

end Noctium.Verification.GuardedInputTranscript
