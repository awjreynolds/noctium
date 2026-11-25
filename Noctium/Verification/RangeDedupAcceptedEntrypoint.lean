import Noctium.Verification.NativeRelationInstructionProjection
import Noctium.Verification.RangeDedupAcceptedArray
import Noctium.Verification.ScalarCallInstructionProjection
import Noctium.Verification.ScalarValidationProjection
import Noctium.Verification.ScalarValidationRawSeedMeaning

namespace Noctium.Verification.RangeDedupAcceptedEntrypoint

open Lean Backend NativeRelation NativeRelationInstructionProjection
open Backend.Native NativeRelationJson
open ScalarNormalization (interpret)
open RangeDedupAcceptedArray ScalarValidationMeaning ScalarValidationOpcodeProfile
open ScalarValidationArithmeticLoop (NativeDefinitions)
open ScalarValidationRawSeedMeaning

open ScalarNormalization (interpret) in
/-- The production lowerer and strict decoder identify the exact assertion
schedule and instruction trace. Every satisfying assignment in the checked
scalar profile proves the source schedule, including any duplicate assertions
removed by an enabled rewrite. -/
theorem lowerEntrypoint_satisfies_sourceAssertions
    (state : List StateDecl) (entry : Entrypoint) (rewrites : Zkir.Rewrites)
    {json : Json} {program : Program} {rows : Array Json}
    (lowered : Zkir.lowerEntrypoint state entry rewrites = .ok json)
    (decoded : NativeRelationJson.decode json = .ok program)
    (rowsParsed : Native.arrayField json "instructions" = .ok rows)
    (profile : checkedScalarOpcodeProfile rows.toList.zipIdx program.instructions = true)
    (inputSchema : ∀ expected,
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected →
        ∀ requirement ∈ expected.inputs, requirement.ty.isForeign = false) :
    ∃ expected,
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected ∧
      ∀ {hash streams witness groups}, CircuitSatisfies hash program streams witness groups →
        ∀ term ∈ expected.assertions, interpret hash witness term = some one := by
  obtain ⟨_, expected, _, schedule, accepted, _⟩ :=
    Zkir.lowerEntrypoint_validation_and_instructions_with_rewrites state entry rewrites json lowered
  obtain ⟨decodedRows, header, parsed, decodedTrace⟩ := decode_headerAndInstructions decoded
  cases Except.ok.inj (parsed.symm.trans rowsParsed)
  obtain ⟨_, driverRows, final, driver⟩ :=
    ScalarValidationProjection.validate_driver_result_empty_header accepted header
  cases Except.ok.inj (driver.instructionsParsed.symm.trans rowsParsed)
  refine ⟨expected, schedule, ?_⟩
  intro hash streams witness groups satisfies term member
  have schema : ∀ requirement ∈ (Zkir.optimizedExpected rewrites expected).inputs,
      requirement.ty.isForeign = false := by
    simpa [Zkir.optimizedExpected, apply_ite] using inputSchema expected schedule
  have definitions : NativeDefinitions ({} : Native.State) := by
    intro name fact member
    simp at member
  have indexedDecoded :
      ((rows.toList.zipIdx).map Prod.fst).mapM NativeRelationJson.decodeInstruction = .ok program.instructions := by
    simpa only [List.zipIdx_map_fst] using decodedTrace
  have asserts := accepted_driver_assertion_schedule driver
    (empty_meaning hash witness witness) definitions schema (fun _ _ => rfl)
    (checkedScalarOpcodeProfile_acceptedMeaningSteps indexedDecoded profile satisfies.instructions)
    (by simp [RangeDedupAssertMeaning.CheckedAssertions])
  apply asserts term
  by_cases strict : rewrites == .disabled <;>
    simp [Zkir.optimizedExpected, strict, List.mem_eraseDups, member]

private theorem validated_scalarSourceRequirements
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

/-- A decoded scalar call exposes source assertions, checked source ranges,
and ordinary scalar input bounds for any satisfying body witness. Rewrites
may deduplicate assertions, so the result refers to the original expected
schedule. The combined input schema covers raw call headers and body inputs. -/
theorem lowerEntrypoint_scalarCall_sourceRequirements
    {state : List StateDecl} {entry : Entrypoint} (rewrites : Zkir.Rewrites)
    {json : Json} {call : ScalarCall} {rows : Array Json}
    (lowered : Zkir.lowerEntrypoint state entry rewrites = .ok json)
    (decoded : NativeRelationJson.decodeScalarCall json = .ok call)
    (rowsParsed : Native.arrayField json "instructions" = .ok rows)
    (profile : checkedScalarOpcodeProfile rows.toList.zipIdx call.body.instructions = true)
    (schema : ∀ expected,
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected →
        ∀ requirement ∈ expected.rawInputs ++ expected.inputs,
          requirement.ty.isForeign = false) :
    ∃ expected,
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected ∧
      ∀ {hash streams witness groups},
        CircuitSatisfies hash call.body streams witness groups →
          (∀ term ∈ expected.assertions, interpret hash witness term = some one) ∧
          (∀ requirement ∈ expected.bounds,
            ∃ value, interpret hash witness requirement.1 = some value ∧
              value.val ≤ requirement.2) ∧
          (∀ requirement ∈ expected.rawInputs ++ expected.inputs,
            requirement.ty.isForeign = false →
            requirement.canonicalJubjubScalar = false →
            (witness requirement.identifier).val ≤ Native.sourceMaximum requirement.ty) := by
  obtain ⟨_, expected, _, expectedAccepted, accepted, _⟩ :=
    Zkir.lowerEntrypoint_validation_and_instructions_with_rewrites
      state entry rewrites json lowered
  obtain ⟨fields, fieldsParsed, fieldsWF⟩ :=
    ScalarCallInstructionProjection.lowerEntrypoint_root_fields_wf rewrites lowered
  obtain ⟨decodedRows, parsedRows, bodyRows⟩ :=
    ScalarCallInstructionProjection.decodeScalarCall_instructionProjection_of_wf
      decoded fields fieldsParsed fieldsWF
  have rowsEq : decodedRows = rows := Except.ok.inj (parsedRows.symm.trans rowsParsed)
  cases rowsEq
  let optimized := Zkir.optimizedExpected rewrites expected
  have inputsUnchanged : optimized.inputs = expected.inputs := by
    cases rewrites <;> rfl
  have rawInputsUnchanged : optimized.rawInputs = expected.rawInputs := by
    cases rewrites <;> rfl
  have schemaOptimized : ∀ requirement ∈ optimized.rawInputs ++ optimized.inputs,
      requirement.ty.isForeign = false := by
    intro requirement member
    rw [rawInputsUnchanged, inputsUnchanged] at member
    exact schema expected expectedAccepted requirement member
  have boundsUnchanged : optimized.bounds = expected.bounds := by
    cases rewrites <;> rfl
  refine ⟨expected, expectedAccepted, ?_⟩
  intro hash streams witness groups satisfies
  have observations := validated_scalarSourceRequirements
    (expected := optimized) (json := json) (program := call.body) (rows := rows)
    accepted rowsParsed bodyRows profile schemaOptimized
    (hash := hash) (streams := streams) (witness := witness) (groups := groups) satisfies
  obtain ⟨optimizedAssertions, optimizedBounds, optimizedInputBounds⟩ := observations
  have assertions : ∀ term ∈ expected.assertions,
      interpret hash witness term = some one := by
    intro term member
    apply optimizedAssertions term
    by_cases strict : rewrites == .disabled <;>
      simp [optimized, Zkir.optimizedExpected, strict, List.mem_eraseDups, member]
  have bounds : ∀ requirement ∈ expected.bounds,
      ∃ value, interpret hash witness requirement.1 = some value ∧
        value.val ≤ requirement.2 := by
    intro requirement member
    apply optimizedBounds requirement
    rw [boundsUnchanged]
    exact member
  have inputBounds : ∀ requirement ∈ expected.rawInputs ++ expected.inputs,
      requirement.ty.isForeign = false →
      requirement.canonicalJubjubScalar = false →
      (witness requirement.identifier).val ≤ Native.sourceMaximum requirement.ty := by
    intro requirement member nonforeign ordinary
    apply optimizedInputBounds requirement
    · rw [rawInputsUnchanged, inputsUnchanged]
      exact member
    · exact nonforeign
    · exact ordinary
  exact ⟨assertions, bounds, inputBounds⟩

/-- The comparison rewrite preserves arbitrary-witness satisfaction for the
two actual emitted ledger relations in the checked scalar opcode profile.
The producer gate supplies the original trace, and the strict decoder's
empty call header supplies its initial state. -/
theorem lowerEntrypoint_comparison_preserves_scalar_kernel
    (state : List StateDecl) (entry : Entrypoint)
    {rangeJson comparisonJson : Json} {rangeProgram comparisonProgram : Program}
    {rows : Array Json}
    (rangeAccepted : Zkir.lowerEntrypoint state entry .rangeAndAssertions = .ok rangeJson)
    (comparisonAccepted :
      Zkir.lowerEntrypoint state entry .includingComparisons = .ok comparisonJson)
    (rangeDecoded : NativeRelationJson.decode rangeJson = .ok rangeProgram)
    (comparisonDecoded : NativeRelationJson.decode comparisonJson = .ok comparisonProgram)
    (rowsParsed : Native.arrayField rangeJson "instructions" = .ok rows)
    (profile : checkedScalarOpcodeProfile rows.toList.zipIdx rangeProgram.instructions = true)
    (inputSchema : ∀ expected,
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected →
        ∀ requirement ∈ expected.inputs, requirement.ty.isForeign = false) :
    ∀ hash streams witness groups returns,
      Satisfies hash rangeProgram streams witness groups returns ↔
        Satisfies hash comparisonProgram streams witness groups returns := by
  obtain ⟨_, expected, emittedRows, _, schedule, rangeValid, _, sourceArray, rewrittenArray⟩ :=
    Zkir.lowerEntrypoint_comparison_instructions_reuse_range_instructions state entry
      rangeJson comparisonJson rangeAccepted comparisonAccepted
  have emittedEq := Except.ok.inj (sourceArray.symm.trans rowsParsed)
  subst emittedRows
  obtain ⟨decodedRows, header, parsed, sourceDecoded⟩ := decode_headerAndInstructions rangeDecoded
  have decodedEq := Except.ok.inj (parsed.symm.trans rowsParsed)
  subst decodedRows
  obtain ⟨optimizedRows, optimizedParsed, runDecoded⟩ := decode_instructionProjection comparisonDecoded
  have optimizedEq := Except.ok.inj (optimizedParsed.symm.trans rewrittenArray)
  subst optimizedRows
  obtain ⟨_, driverRows, final, driver⟩ :=
    ScalarValidationProjection.validate_driver_result_empty_header rangeValid header
  have trace := driver.instructionTrace
  rw [Except.ok.inj (driver.instructionsParsed.symm.trans rowsParsed)] at trace
  have definitions : NativeDefinitions ({} : Native.State) := by
    intro name fact member
    simp at member
  exact acceptedArrayReusePreservesKernel
    (expected := {expected with assertions := expected.assertions.eraseDups})
    (fun hash witness => empty_meaning hash witness witness)
    definitions (inputSchema expected schedule)
    (supportsMeaning_of_checkedScalarOpcodeProfile rows sourceDecoded profile)
    sourceDecoded runDecoded trace

end Noctium.Verification.RangeDedupAcceptedEntrypoint
