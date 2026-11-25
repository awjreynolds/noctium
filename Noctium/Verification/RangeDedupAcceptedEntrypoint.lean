import Noctium.Verification.NativeRelationInstructionProjection
import Noctium.Verification.RangeDedupAcceptedArray
import Noctium.Verification.ScalarValidationProjection

namespace Noctium.Verification.RangeDedupAcceptedEntrypoint

open Lean Backend NativeRelation NativeRelationInstructionProjection
open RangeDedupAcceptedArray ScalarValidationMeaning ScalarValidationOpcodeProfile
open ScalarValidationArithmeticLoop (NativeDefinitions)

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
