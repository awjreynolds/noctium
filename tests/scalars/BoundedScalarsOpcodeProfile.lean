import Lean
import examples.BoundedScalars
import Noctium.Verification.NativeRelationJson
import Noctium.Verification.ScalarValidationOpcodeProfile
import Noctium.Verification.ScalarValidationProjection

namespace BoundedScalarsOpcodeProfile

open Noctium
open Lean
open Noctium.Backend
open Noctium.Backend.Native
open Noctium.Verification.NativeRelation
open Noctium.Verification.NativeRelationJson
open Noctium.Verification.ScalarValidationOpcodeProfile
open Noctium.Verification.ScalarValidationNativeDefinitions

private theorem bind_ok {α β : Type} {value : Except String α} {next : α → Except String β}
    {result : β} : (value >>= next) = .ok result ↔
      ∃ found, value = .ok found ∧ next found = .ok result := by
  cases value <;> simp [Bind.bind, Except.bind]

/-- Recover the actual instruction vector parsed by the checked relation
decoder, without importing the broader unfinished scalar validator proof. -/
private theorem decode_result {program : Json} {relation : Program}
    (decoded : Noctium.Verification.NativeRelationJson.decode program = .ok relation) :
    ∃ instructions : Array Json,
      Noctium.Backend.Native.arrayField program "instructions" = .ok instructions ∧
      instructions.toList.mapM Noctium.Verification.NativeRelationJson.decodeInstruction =
        .ok relation.instructions := by
  unfold Noctium.Verification.NativeRelationJson.decode at decoded
  simp only [bind_ok] at decoded
  rcases decoded with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, instructions, parsed, decodedInstructions, decodedParsed, result⟩
  cases result
  exact ⟨instructions, parsed, decodedParsed⟩

private theorem zipIdx_values {α : Type} (items : List α) (offset : Nat) :
    (items.zipIdx offset).map Prod.fst = items := by
  induction items generalizing offset with
  | nil => rfl
  | cons head tail ih => simp only [List.zipIdx_cons, List.map_cons, ih]

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
  Zkir.lowerEntrypoint_validation_and_instructions BoundedScalars.state
    selectedEntrypoint emittedProgram boundedApply_lowered

theorem boundedApply_instructionsDecode :
    (emittedItems.map Prod.fst).mapM Noctium.Verification.NativeRelationJson.decodeInstruction =
      .ok decodedProgram.instructions := by
  obtain ⟨instructions, parsed, decoded⟩ := decode_result boundedApply_decoded
  have same : instructions = emittedInstructions :=
    Except.ok.inj (parsed.symm.trans boundedApply_instructionsParsed)
  subst instructions
  simpa [emittedItems, zipIdx_values] using decoded

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

end BoundedScalarsOpcodeProfile
