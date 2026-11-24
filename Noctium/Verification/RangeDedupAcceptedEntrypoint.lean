import Noctium.Verification.NativeRelationInstructionProjection
import Noctium.Verification.RangeDedupAcceptedArray
import Noctium.Verification.ScalarValidationProjection

namespace Noctium.Verification.RangeDedupAcceptedEntrypoint

open Lean Backend NativeRelation NativeRelationInstructionProjection
open RangeDedupAcceptedArray ScalarValidationMeaning ScalarValidationOpcodeProfile
open ScalarValidationArithmeticLoop (NativeDefinitions)

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
  obtain ⟨driverRows, rawHeader, seed, final, driver⟩ :=
    ScalarValidationProjection.validate_driver_result rangeValid
  have rawEmpty := Except.ok.inj (driver.rawInputsParsed.symm.trans header)
  have requiredEmpty : expected.rawInputs = [] := List.length_eq_zero_iff.mp (by
    simpa [rawEmpty] using driver.rawInputCount.symm)
  have trace := driver.instructionTrace
  rw [Except.ok.inj (driver.instructionsParsed.symm.trans rowsParsed),
    driver.emptyRawSeed requiredEmpty] at trace
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
