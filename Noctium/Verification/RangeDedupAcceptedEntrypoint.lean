import Noctium.Verification.NativeRelationInstructionProjection
import Noctium.Verification.ScalarValidatedProgram
import Noctium.Verification.ScalarCallHeaderProjection
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

private theorem scalarCall_decoded_rows
    {state : List StateDecl} {entry : Entrypoint} (rewrites : Zkir.Rewrites)
    {json : Json} {call : ScalarCall} {rows : Array Json}
    (lowered : Zkir.lowerEntrypoint state entry rewrites = .ok json)
    (decoded : NativeRelationJson.decodeScalarCall json = .ok call)
    (rowsParsed : Native.arrayField json "instructions" = .ok rows) :
    rows.toList.mapM NativeRelationJson.decodeInstruction = .ok call.body.instructions := by
  obtain ⟨fields, fieldsParsed, fieldsWF⟩ :=
    ScalarCallInstructionProjection.lowerEntrypoint_root_fields_wf rewrites lowered
  obtain ⟨decodedRows, parsedRows, bodyRows⟩ :=
    ScalarCallInstructionProjection.decodeScalarCall_instructionProjection_of_wf
      decoded fields fieldsParsed fieldsWF
  have rowsEq : decodedRows = rows := Except.ok.inj (parsedRows.symm.trans rowsParsed)
  simpa only [rowsEq] using bodyRows

/-- The sole validated Output row observes the exact ordered return terms.
This applies to native raw argument headers and every current compiler rewrite.
Standalone Output has the host observation semantics of `Program.returns`. -/
theorem lowerEntrypoint_scalarCall_returnValues
    {state : List StateDecl} {entry : Entrypoint} (rewrites : Zkir.Rewrites)
    {json : Json} {call : ScalarCall} {rows : Array Json}
    (lowered : Zkir.lowerEntrypoint state entry rewrites = .ok json)
    (decoded : NativeRelationJson.decodeScalarCall json = .ok call)
    (rowsParsed : Native.arrayField json "instructions" = .ok rows)
    (profile : checkedScalarOpcodeProfile rows.toList.zipIdx call.body.instructions = true)
    (schema : ∀ expected,
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected →
        ∀ requirement ∈ expected.rawInputs ++ expected.inputs, requirement.ty.isForeign = false) :
    ∃ expected,
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected ∧
      ∀ {hash streams witness groups},
        CircuitSatisfies hash call.body streams witness groups →
        expected.returns.map (interpret hash witness) = (call.body.returns witness).map some := by
  obtain ⟨_, expected, _, expectedAccepted, accepted, _⟩ :=
    Zkir.lowerEntrypoint_validation_and_instructions_with_rewrites
      state entry rewrites json lowered
  let optimized := Zkir.optimizedExpected rewrites expected
  have inputsUnchanged : optimized.rawInputs ++ optimized.inputs =
      expected.rawInputs ++ expected.inputs := by cases rewrites <;> rfl
  have returnsUnchanged : optimized.returns = expected.returns := by cases rewrites <;> rfl
  have schemaOptimized : ∀ requirement ∈ optimized.rawInputs ++ optimized.inputs,
      requirement.ty.isForeign = false := by
    simpa only [inputsUnchanged] using schema expected expectedAccepted
  refine ⟨expected, expectedAccepted, ?_⟩
  intro hash streams witness groups satisfies
  rw [← returnsUnchanged]
  exact ScalarValidatedProgram.returnValues (expected := optimized) accepted rowsParsed
    (scalarCall_decoded_rows rewrites lowered decoded rowsParsed) profile schemaOptimized
    (inputs := witness) (fun _ _ => rfl) satisfies

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
  have bodyRows := scalarCall_decoded_rows rewrites lowered decoded rowsParsed
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
  have observations := ScalarValidatedProgram.sourceRequirements
    (expected := optimized) (json := json) (program := call.body) (rows := rows)
    accepted rowsParsed bodyRows profile schemaOptimized
    (hash := hash) (streams := streams) (inputs := witness) (witness := witness) (groups := groups)
    (fun _ _ => rfl) satisfies
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

/-- The exact emitted scalar call preserves the ordered payloads of the
accepted Impact schedule, including native raw call arguments and all current
rewrite modes. The scalar circuit model requires active Impact rows.
The result concerns payloads in that model, with VM execution checked separately. -/
theorem lowerEntrypoint_scalarCall_impactPayloads
    {state : List StateDecl} {entry : Entrypoint} (rewrites : Zkir.Rewrites)
    {json : Json} {call : ScalarCall} {rows : Array Json}
    (lowered : Zkir.lowerEntrypoint state entry rewrites = .ok json)
    (decoded : NativeRelationJson.decodeScalarCall json = .ok call)
    (rowsParsed : Native.arrayField json "instructions" = .ok rows)
    (profile : checkedScalarOpcodeProfile rows.toList.zipIdx call.body.instructions = true)
    (schema : ∀ expected,
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected →
        ∀ requirement ∈ expected.rawInputs ++ expected.inputs, requirement.ty.isForeign = false)
    (inputGuards : ∀ expected,
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected →
        ∀ requirement ∈ expected.inputs, requirement.activityGuard = none) :
    ∃ plan expected,
      Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected ∧
      ∀ {hash streams witness groups},
        CircuitSatisfies hash call.body streams witness groups →
        expected.groups.map (List.map (interpret hash witness)) = groups.map (List.map some) := by
  obtain ⟨plan, expected, impactAccepted, expectedAccepted, accepted, _⟩ :=
    Zkir.lowerEntrypoint_validation_and_instructions_with_rewrites
      state entry rewrites json lowered
  have bodyRows := scalarCall_decoded_rows rewrites lowered decoded rowsParsed
  let optimized := Zkir.optimizedExpected rewrites expected
  have inputsUnchanged : optimized.inputs = expected.inputs := by cases rewrites <;> rfl
  have rawInputsUnchanged : optimized.rawInputs = expected.rawInputs := by cases rewrites <;> rfl
  have groupsUnchanged : optimized.groups = expected.groups := by cases rewrites <;> rfl
  have schemaOptimized : ∀ requirement ∈ optimized.rawInputs ++ optimized.inputs,
      requirement.ty.isForeign = false := by
    simpa only [inputsUnchanged, rawInputsUnchanged] using schema expected expectedAccepted
  have guardsOptimized : ∀ requirement ∈ optimized.inputs,
      requirement.activityGuard = none := by
    simpa only [inputsUnchanged] using inputGuards expected expectedAccepted
  refine ⟨plan, expected, impactAccepted, expectedAccepted, ?_⟩
  intro hash streams witness groups satisfies
  rw [← groupsUnchanged]
  exact ScalarValidatedProgram.impactPayloads
    (expected := optimized) accepted rowsParsed bodyRows profile schemaOptimized guardsOptimized
    (inputs := witness) (fun _ _ => rfl) satisfies

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

/-- The production comparison rewrite preserves the caller's ordered scalar
arguments and satisfiability of the emitted body for every witness. The
producer seeds the prefix from the checked call header, so the proof includes
nonempty headers and uses the same raw argument assignment in both modes. -/
theorem lowerEntrypoint_comparison_preserves_scalarCall_kernel
    {state : List StateDecl} {entry : Entrypoint}
    {rangeJson comparisonJson : Json} {rangeCall comparisonCall : ScalarCall}
    {rows : Array Json}
    (rangeAccepted : Zkir.lowerEntrypoint state entry .rangeAndAssertions = .ok rangeJson)
    (comparisonAccepted :
      Zkir.lowerEntrypoint state entry .includingComparisons = .ok comparisonJson)
    (rangeDecoded : NativeRelationJson.decodeScalarCall rangeJson = .ok rangeCall)
    (comparisonDecoded : NativeRelationJson.decodeScalarCall comparisonJson = .ok comparisonCall)
    (rowsParsed : Native.arrayField rangeJson "instructions" = .ok rows)
    (profile : checkedScalarOpcodeProfile rows.toList.zipIdx rangeCall.body.instructions = true)
    (schema : ∀ expected,
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected →
        ∀ requirement ∈ expected.rawInputs ++ expected.inputs, requirement.ty.isForeign = false) :
    rangeCall.arguments = comparisonCall.arguments ∧
      ∀ hash streams witness groups returns,
        Satisfies hash rangeCall.body streams witness groups returns ↔
          Satisfies hash comparisonCall.body streams witness groups returns := by
  obtain ⟨_, expected, emittedRows, _, schedule, rangeValid, comparisonValid,
      sourceArray, rewrittenArray⟩ :=
    Zkir.lowerEntrypoint_comparison_instructions_reuse_range_instructions state entry
      rangeJson comparisonJson rangeAccepted comparisonAccepted
  have emittedEq := Except.ok.inj (sourceArray.symm.trans rowsParsed)
  subst emittedRows
  have rangeNames :=
    ScalarCallHeaderProjection.validate_decodeScalarCall_header_names rangeValid rangeDecoded
  have comparisonNames :=
    ScalarCallHeaderProjection.validate_decodeScalarCall_header_names
      comparisonValid comparisonDecoded
  refine ⟨rangeNames.trans comparisonNames.symm, ?_⟩
  have sourceDecoded := scalarCall_decoded_rows .rangeAndAssertions
    rangeAccepted rangeDecoded rowsParsed
  have runDecoded := scalarCall_decoded_rows .includingComparisons
    comparisonAccepted comparisonDecoded rewrittenArray
  obtain ⟨driverRows, _, seed, _, driver⟩ :=
    ScalarValidationProjection.validate_driver_result rangeValid
  have driverEq := Except.ok.inj (driver.instructionsParsed.symm.trans rowsParsed)
  subst driverRows
  have rawSchema : ∀ requirement ∈ expected.rawInputs, requirement.ty.isForeign = false :=
    fun requirement member => schema expected schedule requirement (List.mem_append_left _ member)
  have inputSchema : ∀ requirement ∈ expected.inputs, requirement.ty.isForeign = false :=
    fun requirement member => schema expected schedule requirement (List.mem_append_right _ member)
  have seedMeaning (hash : Hash) (witness : Assignment) :
      StateMeaning hash witness witness seed ∧ NativeDefinitions seed :=
    seedRawInputs_meaning_and_nativeDefinitions rawSchema (fun _ _ => rfl) driver.seededRawInputs
  exact acceptedArrayReusePreservesKernel
    (expected := {expected with assertions := expected.assertions.eraseDups})
    (fun hash witness => (seedMeaning hash witness).1)
    (seedMeaning (fun _ => zero) (fun _ => zero)).2 inputSchema
    (supportsMeaning_of_checkedScalarOpcodeProfile rows sourceDecoded profile)
    sourceDecoded runDecoded driver.instructionTrace

end Noctium.Verification.RangeDedupAcceptedEntrypoint
