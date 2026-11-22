import Noctium.Verification.RangeDedup

namespace Noctium.Verification.RangeDedupKernel

open Lean NativeRelation NativeRelationJson

private theorem filterMap_nonRange (instructions : List Instruction)
    (observe : Instruction → Option α)
    (silent : ∀ instruction, RangeDedup.nonRange instruction = false →
      observe instruction = none) :
    instructions.filterMap observe =
      (instructions.filter RangeDedup.nonRange).filterMap observe := by
  induction instructions with
  | nil => rfl
  | cons instruction rest ih =>
    by_cases keep : RangeDedup.nonRange instruction = true
    · simp [List.filterMap, List.filter, keep, ih]
    · have drop : RangeDedup.nonRange instruction = false := by
        cases value : RangeDedup.nonRange instruction <;> simp_all
      simp [List.filterMap, List.filter, keep, silent instruction drop, ih]

private theorem flatMap_nonRange (instructions : List Instruction)
    (observe : Instruction → List α)
    (silent : ∀ instruction, RangeDedup.nonRange instruction = false →
      observe instruction = []) :
    instructions.flatMap observe =
      (instructions.filter RangeDedup.nonRange).flatMap observe := by
  induction instructions with
  | nil => rfl
  | cons instruction rest ih =>
    by_cases keep : RangeDedup.nonRange instruction = true
    · simpa [keep] using ih
    · have drop : RangeDedup.nonRange instruction = false := by
        cases value : RangeDedup.nonRange instruction <;> simp_all
      simp [drop, silent instruction drop, ih]

private theorem inputs_eq_of_nonRange {left right : Program}
    (same : left.instructions.filter RangeDedup.nonRange =
      right.instructions.filter RangeDedup.nonRange)
    (visibility : Visibility) (witness : Assignment) :
    left.inputValues visibility witness = right.inputValues visibility witness := by
  unfold Program.inputValues
  rw [filterMap_nonRange left.instructions _ (by
    intro instruction nonRange
    cases instruction <;> simp [RangeDedup.nonRange] at nonRange ⊢),
    filterMap_nonRange right.instructions _ (by
      intro instruction nonRange
      cases instruction <;> simp [RangeDedup.nonRange] at nonRange ⊢), same]

private theorem groups_eq_of_nonRange {left right : Program}
    (same : left.instructions.filter RangeDedup.nonRange =
      right.instructions.filter RangeDedup.nonRange)
    (witness : Assignment) :
    left.groups witness = right.groups witness := by
  unfold Program.groups
  rw [filterMap_nonRange left.instructions _ (by
    intro instruction nonRange
    cases instruction <;> simp [RangeDedup.nonRange] at nonRange ⊢),
    filterMap_nonRange right.instructions _ (by
      intro instruction nonRange
      cases instruction <;> simp [RangeDedup.nonRange] at nonRange ⊢), same]

private theorem returns_eq_of_nonRange {left right : Program}
    (same : left.instructions.filter RangeDedup.nonRange =
      right.instructions.filter RangeDedup.nonRange)
    (witness : Assignment) :
    left.returns witness = right.returns witness := by
  unfold Program.returns
  rw [flatMap_nonRange left.instructions _ (by
    intro instruction nonRange
    cases instruction <;> simp [RangeDedup.nonRange] at nonRange ⊢),
    flatMap_nonRange right.instructions _ (by
      intro instruction nonRange
      cases instruction <;> simp [RangeDedup.nonRange] at nonRange ⊢), same]

/-- The independent circuit relation is invariant when one instruction list
has the same ordered non-range instructions and equivalent instruction Holds. -/
theorem circuitSatisfies_iff {left right : Program} (hash : Hash)
    (streams : InputStreams) (witness : Assignment) (publicGroups : List (List Scalar))
    (same : left.instructions.filter RangeDedup.nonRange =
      right.instructions.filter RangeDedup.nonRange)
    (holds : (∀ instruction ∈ left.instructions,
        Instruction.Holds hash witness instruction) ↔
      (∀ instruction ∈ right.instructions,
        Instruction.Holds hash witness instruction)) :
    CircuitSatisfies hash left streams witness publicGroups ↔
      CircuitSatisfies hash right streams witness publicGroups := by
  constructor
  · intro satisfies
    refine ⟨holds.mp satisfies.instructions, ?_, ?_, ?_⟩
    · rw [← inputs_eq_of_nonRange same .public witness]
      exact satisfies.publicInputs
    · rw [← inputs_eq_of_nonRange same .private witness]
      exact satisfies.privateInputs
    · rw [← groups_eq_of_nonRange same witness]
      exact satisfies.groups
  · intro satisfies
    refine ⟨holds.mpr satisfies.instructions, ?_, ?_, ?_⟩
    · rw [inputs_eq_of_nonRange same .public witness]
      exact satisfies.publicInputs
    · rw [inputs_eq_of_nonRange same .private witness]
      exact satisfies.privateInputs
    · rw [groups_eq_of_nonRange same witness]
      exact satisfies.groups

/-- Full native relation satisfaction also preserves the host-visible output
sequence. Output fields come from the same ordered non-range instructions. -/
theorem satisfies_iff {left right : Program} (hash : Hash)
    (streams : InputStreams) (witness : Assignment) (publicGroups : List (List Scalar))
    (outputs : List Scalar)
    (same : left.instructions.filter RangeDedup.nonRange =
      right.instructions.filter RangeDedup.nonRange)
    (holds : (∀ instruction ∈ left.instructions,
        Instruction.Holds hash witness instruction) ↔
      (∀ instruction ∈ right.instructions,
        Instruction.Holds hash witness instruction)) :
    Satisfies hash left streams witness publicGroups outputs ↔
      Satisfies hash right streams witness publicGroups outputs := by
  have sameReturns := returns_eq_of_nonRange same witness
  constructor
  · intro satisfies
    have circuit := circuitSatisfies_iff hash streams witness publicGroups same holds |>.mp
      satisfies.circuit
    refine ⟨circuit.instructions, circuit.publicInputs, circuit.privateInputs, circuit.groups, ?_⟩
    rw [← sameReturns]
    exact satisfies.outputs
  · intro satisfies
    have circuit := circuitSatisfies_iff hash streams witness publicGroups same holds |>.mpr
      satisfies.circuit
    refine ⟨circuit.instructions, circuit.publicInputs, circuit.privateInputs, circuit.groups, ?_⟩
    rw [sameReturns]
    exact satisfies.outputs

/-- A decoded compiler relation is kernel-equivalent to the range pass when its
instruction sequence parses to the exact result of that pass. The input array
and both typed Programs come from checked artifact decoders. -/
theorem parsed_range_run_preserves_kernel (source : Array Json) (left right : Program)
    (sourceDecoded : source.toList.mapM decodeInstruction = .ok left.instructions)
    (runDecoded : (Backend.RangeDedup.run source).toList.mapM decodeInstruction =
      .ok right.instructions) :
    ∀ hash streams witness groups returns,
      (Satisfies hash left streams witness groups returns ↔
        Satisfies hash right streams witness groups returns) := by
  obtain ⟨optimizedInstructions, optimizedParsed, sameNonRange, sameHolds⟩ :=
    RangeDedup.preserves_decoded source left.instructions sourceDecoded
  have instructionsEqual : optimizedInstructions = right.instructions :=
    Except.ok.inj (optimizedParsed.symm.trans runDecoded)
  have ordered : left.instructions.filter RangeDedup.nonRange =
      right.instructions.filter RangeDedup.nonRange := by
    rw [← instructionsEqual]
    exact sameNonRange.symm
  intro hash streams witness groups returns
  have holds : (∀ instruction ∈ left.instructions,
      Instruction.Holds hash witness instruction) ↔
    (∀ instruction ∈ right.instructions,
      Instruction.Holds hash witness instruction) := by
    simpa [instructionsEqual] using (sameHolds hash witness).symm
  exact satisfies_iff hash streams witness groups returns ordered holds

end Noctium.Verification.RangeDedupKernel
