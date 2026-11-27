import Noctium.Verification.GuardedImpactTranscript
import Noctium.Verification.RangeDedupAcceptedArray
import Noctium.Verification.ScalarValidationProjection
import Noctium.Verification.ScalarValidationRawSeedMeaning
import Noctium.Verification.ScalarNormalization

namespace Noctium.Verification.GuardedZkirRequirements

open Lean Backend Native NativeRelation GuardedScalarRows GuardedImpactTranscript
open ScalarValidationMeaning ScalarValidationProjection
open ScalarValidationArithmeticLoop (NativeDefinitions)
open ScalarValidationRawSeedMeaning
open ScalarNormalization (interpret)
open RangeDedupAssertMeaning (CheckedAssertions)
open RangeDedupAcceptedArray (AcceptedMeaningStep)

private theorem bind_ok {α β : Type} {first : Except String α}
    {next : α → Except String β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem decodeRow_member {items : List Json} {rows : List Row}
    (decoded : items.mapM GuardedScalarRows.decodeRow = .ok rows)
    {raw : Json} (member : raw ∈ items) :
    ∃ row, GuardedScalarRows.decodeRow raw = .ok row ∧ row ∈ rows := by
  induction items generalizing rows with
  | nil => simp at member
  | cons head tail ih =>
    simp only [List.mapM_cons, bind_ok] at decoded
    obtain ⟨headRow, headDecoded, tailRows, tailDecoded, rowsEq⟩ := decoded
    cases rowsEq
    rcases List.mem_cons.mp member with same | tailMember
    · subst raw
      exact ⟨headRow, headDecoded, by simp⟩
    · obtain ⟨row, rowDecoded, rowMember⟩ := ih tailDecoded tailMember
      exact ⟨row, rowDecoded, by simp [rowMember]⟩

/-- The accepted mixed-row fold exposes source requirements and the producer
meaning before and after each actual indexed row. Output consumers use the row
visit to interpret the output at its producer ordinal. -/
theorem lowerEntrypoint_guardedRows_meaning
    {state : List StateDecl} {entry : Entrypoint} (rewrites : Zkir.Rewrites)
    {json : Json} {instructions : Array Json} {rows : List Row}
    (lowered : Zkir.lowerEntrypoint state entry rewrites = .ok json)
    (instructionsParsed : Native.arrayField json "instructions" = .ok instructions)
    (decoded : instructions.toList.mapM GuardedScalarRows.decodeRow = .ok rows)
    (schema : ∀ expected,
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected →
        ∀ requirement ∈ expected.rawInputs ++ expected.inputs,
          requirement.ty.isForeign = false) :
    ∃ expected,
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected ∧
      Native.requireFinalOutput instructions.toList = .ok () ∧
      ∀ {hash : Hash} {witness : Assignment},
        (∀ row ∈ rows, GuardedImpactTranscript.ordinaryHolds hash witness row) →
          (∀ term ∈ expected.assertions, interpret hash witness term = some one) ∧
          (∀ requirement ∈ expected.bounds,
            ∃ value, interpret hash witness requirement.1 = some value ∧
              value.val ≤ requirement.2) ∧
          (∀ requirement ∈ expected.rawInputs ++ expected.inputs,
            requirement.ty.isForeign = false →
            requirement.canonicalJubjubScalar = false →
            (witness requirement.identifier).val ≤ Native.sourceMaximum requirement.ty) ∧
          (∀ raw index, (raw, index) ∈ instructions.toList.zipIdx →
            ∃ before after,
              ScalarValidationMeaning.StateMeaning hash witness witness before ∧
              Native.validateInstruction (Zkir.optimizedExpected rewrites expected)
                before raw = .ok after ∧
              ScalarValidationMeaning.StateMeaning hash witness witness after) := by
  obtain ⟨_, expected, _, expectedAccepted, accepted, _⟩ :=
    Zkir.lowerEntrypoint_validation_and_instructions_with_rewrites
      state entry rewrites json lowered
  let optimized := Zkir.optimizedExpected rewrites expected
  obtain ⟨parsedInstructions, rawInputs, seed, final, driver⟩ :=
    ScalarValidationProjection.validate_driver_result (expected := optimized) accepted
  have instructionsEq : parsedInstructions = instructions :=
    Except.ok.inj (driver.instructionsParsed.symm.trans instructionsParsed)
  subst parsedInstructions
  refine ⟨expected, expectedAccepted, driver.finalOutput, ?_⟩
  intro hash witness ordinary
  have optimizedInputs : optimized.rawInputs ++ optimized.inputs =
      expected.rawInputs ++ expected.inputs := by
    cases rewrites <;> rfl
  have rawSchema : ∀ requirement ∈ optimized.rawInputs,
      requirement.ty.isForeign = false := by
    intro requirement member
    apply schema expected expectedAccepted requirement
    rw [← optimizedInputs]
    exact List.mem_append_left _ member
  have inputSchema : ∀ requirement ∈ optimized.inputs,
      requirement.ty.isForeign = false := by
    intro requirement member
    apply schema expected expectedAccepted requirement
    rw [← optimizedInputs]
    exact List.mem_append_right _ member
  obtain ⟨seedMeaning, seedDefinitions⟩ :=
    seedRawInputs_meaning_and_nativeDefinitions
      (hash := hash) (inputs := witness) (witness := witness)
      rawSchema (fun _ _ => rfl) driver.seededRawInputs
  have seedAssertionCount := seedRawInputs_assertionCount rawSchema driver.seededRawInputs
  have initialAssertions :
      CheckedAssertions hash witness optimized seed.assertionCount := by
    simp [CheckedAssertions, seedAssertionCount]
  have driverTrace :
      Native.validateInstructionLoop optimized (instructions.toList.zipIdx) seed = .ok final :=
    driver.instructionTrace
  have steps : ∀ item ∈ instructions.toList.zipIdx,
      AcceptedMeaningStep hash witness item.1 := by
    intro item member
    have rawMember : item.1 ∈ instructions.toList := by
      have found : item.1 ∈ (instructions.toList.zipIdx).map Prod.fst :=
        List.mem_map.mpr ⟨item, member, rfl⟩
      simpa only [List.zipIdx_map_fst] using found
    obtain ⟨row, rowDecoded, rowMember⟩ := decodeRow_member decoded rawMember
    exact GuardedImpactTranscript.classify_decoded_row rowDecoded (ordinary row rowMember)
  obtain ⟨finalMeaning, _, preserveAssertions, visits⟩ :=
    RangeDedupAcceptedArray.accepted_loop_meaning_assertions_at_steps
      seedMeaning seedDefinitions inputSchema (fun _ _ => rfl) steps driverTrace
  have optimizedAssertions : ∀ term ∈ optimized.assertions,
      interpret hash witness term = some one := by
    have checked := preserveAssertions initialAssertions
    simpa only [driver.assertionCount, CheckedAssertions, List.take_length] using checked
  have assertions : ∀ term ∈ expected.assertions,
      interpret hash witness term = some one := by
    intro term member
    apply optimizedAssertions term
    by_cases strict : rewrites == .disabled <;>
      simp [optimized, Zkir.optimizedExpected, strict, List.mem_eraseDups, member]
  have boundsUnchanged : optimized.bounds = expected.bounds := by
    cases rewrites <;> rfl
  have bounds : ∀ requirement ∈ expected.bounds,
      ∃ value, interpret hash witness requirement.1 = some value ∧
        value.val ≤ requirement.2 := by
    intro requirement member
    exact driver.rangeRequirements finalMeaning requirement (by
      rw [boundsUnchanged]
      exact member)
  have inputBounds : ∀ requirement ∈ expected.rawInputs ++ expected.inputs,
      requirement.ty.isForeign = false →
      requirement.canonicalJubjubScalar = false →
      (witness requirement.identifier).val ≤ Native.sourceMaximum requirement.ty := by
    intro requirement member nonforeign ordinaryScalar
    exact driver.inputBound finalMeaning
      (by rw [optimizedInputs]; exact member) nonforeign ordinaryScalar
  have rowMeanings : ∀ raw index, (raw, index) ∈ instructions.toList.zipIdx →
      ∃ before after,
        ScalarValidationMeaning.StateMeaning hash witness witness before ∧
        Native.validateInstruction optimized before raw = .ok after ∧
        ScalarValidationMeaning.StateMeaning hash witness witness after := by
    intro raw index member
    obtain ⟨before, after, beforeMeaning, _, checked, afterMeaning, _⟩ :=
      visits raw index member
    exact ⟨before, after, beforeMeaning, checked, afterMeaning⟩
  exact ⟨assertions, bounds, inputBounds, rowMeanings⟩

private theorem raw_of_decodedRow_member {items : List Json} {rows : List Row}
    (decoded : items.mapM decodeRow = .ok rows)
    {row : Row} (present : row ∈ rows) :
    ∃ raw ∈ items, decodeRow raw = .ok row := by
  induction items generalizing rows with
  | nil =>
    change (Except.ok [] : Except String (List Row)) = .ok rows at decoded
    cases decoded
    simp at present
  | cons head tail ih =>
    simp only [List.mapM_cons, bind_ok] at decoded
    obtain ⟨headRow, headDecoded, rest, restDecoded, same⟩ := decoded
    cases same
    rcases List.mem_cons.mp present with same | later
    · subst row
      exact ⟨head, List.mem_cons_self .., headDecoded⟩
    · obtain ⟨raw, member, checked⟩ := ih restDecoded later
      exact ⟨raw, List.mem_cons_of_mem _ member, checked⟩

/-- Each comparison inherits its actual operand bounds from the state reached
by the accepted producer trace. The row's own result equation cannot establish
that premise because the equation is conditional on those bounds. -/
theorem lowerEntrypoint_guardedRows_comparison_bounds
    {state : List StateDecl} {sourceEntry : Entrypoint} (rewrites : Zkir.Rewrites)
    {json : Json} {instructions : Array Json} {rows : List Row}
    {hash : Hash} {witness : Assignment}
    (lowered : Zkir.lowerEntrypoint state sourceEntry rewrites = .ok json)
    (instructionsParsed : Native.arrayField json "instructions" = .ok instructions)
    (decoded : instructions.toList.mapM decodeRow = .ok rows)
    (schema : ∀ expected,
      Native.expectedEntrypoint state (Passes.pruneEntrypoint sourceEntry) = .ok expected →
        ∀ requirement ∈ expected.rawInputs ++ expected.inputs,
          requirement.ty.isForeign = false)
    (holds : ∀ row ∈ rows, ordinaryHolds hash witness row) :
    ∀ left right width destination, .strict (.lessThan left right width destination) ∈ rows →
      (left.read witness).val < 2 ^ width ∧ (right.read witness).val < 2 ^ width := by
  obtain ⟨_, _, _, meaning⟩ := lowerEntrypoint_guardedRows_meaning
    rewrites lowered instructionsParsed decoded schema
  obtain ⟨_, _, _, visits⟩ := meaning holds
  intro left right width destination present
  obtain ⟨raw, rawMember, rowDecoded⟩ := raw_of_decodedRow_member decoded present
  have indexed : raw ∈ instructions.toList.zipIdx.map Prod.fst := by
    simpa only [List.zipIdx_map_fst] using rawMember
  obtain ⟨⟨item, ordinal⟩, visit, same⟩ := List.mem_map.mp indexed
  change item = raw at same
  subst item
  obtain ⟨before, after, beforeMeaning, accepted, _⟩ := visits raw ordinal visit
  have step := (decodeRow_strict rowDecoded).1
  cases step.supported with
  | lessThan _ _ _ _ opcode =>
    exact RangeDedupAcceptedArray.accepted_lessThan_witnessBounds beforeMeaning opcode
      step.decoded accepted

/-- Accepted mixed ZKIR rows preserve the source assertions, source bounds,
and scalar input bounds. Strict rows use their ordinary circuit constraint;
guarded impact and public input rows pass through the guarded classifier. -/
theorem lowerEntrypoint_guardedRows_sourceRequirements
    {state : List StateDecl} {entry : Entrypoint} (rewrites : Zkir.Rewrites)
    {json : Json} {instructions : Array Json} {rows : List Row}
    (lowered : Zkir.lowerEntrypoint state entry rewrites = .ok json)
    (instructionsParsed : Native.arrayField json "instructions" = .ok instructions)
    (decoded : instructions.toList.mapM GuardedScalarRows.decodeRow = .ok rows)
    (schema : ∀ expected,
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected →
        ∀ requirement ∈ expected.rawInputs ++ expected.inputs,
          requirement.ty.isForeign = false) :
    ∃ expected,
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected ∧
      ∀ {hash : Hash} {witness : Assignment},
        (∀ row ∈ rows, GuardedImpactTranscript.ordinaryHolds hash witness row) →
          (∀ term ∈ expected.assertions, interpret hash witness term = some one) ∧
          (∀ requirement ∈ expected.bounds,
            ∃ value, interpret hash witness requirement.1 = some value ∧
              value.val ≤ requirement.2) ∧
          (∀ requirement ∈ expected.rawInputs ++ expected.inputs,
            requirement.ty.isForeign = false →
            requirement.canonicalJubjubScalar = false →
            (witness requirement.identifier).val ≤ Native.sourceMaximum requirement.ty) := by
  obtain ⟨expected, expectedAccepted, _, meaning⟩ :=
    lowerEntrypoint_guardedRows_meaning rewrites lowered instructionsParsed decoded schema
  refine ⟨expected, expectedAccepted, ?_⟩
  intro hash witness ordinary
  obtain ⟨assertions, bounds, inputBounds, _⟩ := meaning ordinary
  exact ⟨assertions, bounds, inputBounds⟩

end Noctium.Verification.GuardedZkirRequirements
