import Noctium.Verification.RangeDedup

namespace Noctium.Verification.RangeDedupKernel

open Lean NativeRelation NativeRelationJson

private theorem filterMap_filter (instructions : List Instruction) (keep : Instruction → Bool)
    (observe : Instruction → Option α)
    (silent : ∀ instruction, keep instruction = false →
      observe instruction = none) :
    instructions.filterMap observe =
      (instructions.filter keep).filterMap observe := by
  induction instructions with
  | nil => rfl
  | cons instruction rest ih =>
    by_cases kept : keep instruction = true
    · simp [List.filterMap, List.filter, kept, ih]
    · have drop : keep instruction = false := by
        cases value : keep instruction <;> simp_all
      simp [List.filterMap, List.filter, drop, silent instruction drop, ih]

private theorem flatMap_filter (instructions : List Instruction) (keep : Instruction → Bool)
    (observe : Instruction → List α)
    (silent : ∀ instruction, keep instruction = false →
      observe instruction = []) :
    instructions.flatMap observe =
      (instructions.filter keep).flatMap observe := by
  induction instructions with
  | nil => rfl
  | cons instruction rest ih =>
    by_cases kept : keep instruction = true
    · simpa [kept] using ih
    · have drop : keep instruction = false := by
        cases value : keep instruction <;> simp_all
      simp [drop, silent instruction drop, ih]

private def silent : Instruction → Prop
  | .input .. | .impact .. | .output .. => False
  | _ => True

private theorem inputs_eq_of_filter {left right : Program} {keep : Instruction → Bool}
    (same : left.instructions.filter keep = right.instructions.filter keep)
    (quiet : ∀ instruction, keep instruction = false → silent instruction)
    (visibility : Visibility) (witness : Assignment) :
    left.inputValues visibility witness = right.inputValues visibility witness := by
  unfold Program.inputValues
  rw [filterMap_filter left.instructions keep _ (by
    intro instruction dropped
    have omitted := quiet instruction dropped
    cases instruction <;> simp_all [silent]),
    filterMap_filter right.instructions keep _ (by
      intro instruction dropped
      have omitted := quiet instruction dropped
      cases instruction <;> simp_all [silent]), same]

private theorem groups_eq_of_filter {left right : Program} {keep : Instruction → Bool}
    (same : left.instructions.filter keep = right.instructions.filter keep)
    (quiet : ∀ instruction, keep instruction = false → silent instruction)
    (witness : Assignment) :
    left.groups witness = right.groups witness := by
  unfold Program.groups
  rw [filterMap_filter left.instructions keep _ (by
    intro instruction dropped
    have omitted := quiet instruction dropped
    cases instruction <;> simp_all [silent]),
    filterMap_filter right.instructions keep _ (by
      intro instruction dropped
      have omitted := quiet instruction dropped
      cases instruction <;> simp_all [silent]), same]

private theorem returns_eq_of_filter {left right : Program} {keep : Instruction → Bool}
    (same : left.instructions.filter keep = right.instructions.filter keep)
    (quiet : ∀ instruction, keep instruction = false → silent instruction)
    (witness : Assignment) :
    left.returns witness = right.returns witness := by
  unfold Program.returns
  rw [flatMap_filter left.instructions keep _ (by
    intro instruction dropped
    have omitted := quiet instruction dropped
    cases instruction <;> simp_all [silent]),
    flatMap_filter right.instructions keep _ (by
      intro instruction dropped
      have omitted := quiet instruction dropped
      cases instruction <;> simp_all [silent]), same]

/-- The independent circuit relation is invariant when one instruction list
has the same ordered observable instructions and equivalent instruction Holds. -/
private theorem circuitSatisfies_iff_of_filter {left right : Program} {keep : Instruction → Bool} (hash : Hash)
    (streams : InputStreams) (witness : Assignment) (publicGroups : List (List Scalar))
    (same : left.instructions.filter keep = right.instructions.filter keep)
    (quiet : ∀ instruction, keep instruction = false → silent instruction)
    (holds : (∀ instruction ∈ left.instructions,
        Instruction.Holds hash witness instruction) ↔
      (∀ instruction ∈ right.instructions,
        Instruction.Holds hash witness instruction)) :
    CircuitSatisfies hash left streams witness publicGroups ↔
      CircuitSatisfies hash right streams witness publicGroups := by
  constructor
  · intro satisfies
    refine ⟨holds.mp satisfies.instructions, ?_, ?_, ?_⟩
    · rw [← inputs_eq_of_filter same quiet .public witness]
      exact satisfies.publicInputs
    · rw [← inputs_eq_of_filter same quiet .private witness]
      exact satisfies.privateInputs
    · rw [← groups_eq_of_filter same quiet witness]
      exact satisfies.groups
  · intro satisfies
    refine ⟨holds.mpr satisfies.instructions, ?_, ?_, ?_⟩
    · rw [inputs_eq_of_filter same quiet .public witness]
      exact satisfies.publicInputs
    · rw [inputs_eq_of_filter same quiet .private witness]
      exact satisfies.privateInputs
    · rw [groups_eq_of_filter same quiet witness]
      exact satisfies.groups

/-- Full native relation satisfaction also preserves the host-visible output
sequence. The retained sequence contains all host observations. -/
private theorem satisfies_iff_of_filter {left right : Program} {keep : Instruction → Bool} (hash : Hash)
    (streams : InputStreams) (witness : Assignment) (publicGroups : List (List Scalar))
    (outputs : List Scalar)
    (same : left.instructions.filter keep = right.instructions.filter keep)
    (quiet : ∀ instruction, keep instruction = false → silent instruction)
    (holds : (∀ instruction ∈ left.instructions,
        Instruction.Holds hash witness instruction) ↔
      (∀ instruction ∈ right.instructions,
        Instruction.Holds hash witness instruction)) :
    Satisfies hash left streams witness publicGroups outputs ↔
      Satisfies hash right streams witness publicGroups outputs := by
  have sameReturns := returns_eq_of_filter same quiet witness
  constructor
  · intro satisfies
    have circuit := circuitSatisfies_iff_of_filter hash streams witness publicGroups same quiet holds |>.mp
      satisfies.circuit
    refine ⟨circuit.instructions, circuit.publicInputs, circuit.privateInputs, circuit.groups, ?_⟩
    rw [← sameReturns]
    exact satisfies.outputs
  · intro satisfies
    have circuit := circuitSatisfies_iff_of_filter hash streams witness publicGroups same quiet holds |>.mpr
      satisfies.circuit
    refine ⟨circuit.instructions, circuit.publicInputs, circuit.privateInputs, circuit.groups, ?_⟩
    rw [sameReturns]
    exact satisfies.outputs

private theorem nonRange_silent (instruction : Instruction)
    (dropped : RangeDedup.nonRange instruction = false) : silent instruction := by
  cases instruction <;> simp_all [RangeDedup.nonRange, silent]

theorem circuitSatisfies_iff {left right : Program} (hash : Hash)
    (streams : InputStreams) (witness : Assignment) (publicGroups : List (List Scalar))
    (same : left.instructions.filter RangeDedup.nonRange =
      right.instructions.filter RangeDedup.nonRange)
    (holds : (∀ instruction ∈ left.instructions,
        Instruction.Holds hash witness instruction) ↔
      (∀ instruction ∈ right.instructions,
        Instruction.Holds hash witness instruction)) :
    CircuitSatisfies hash left streams witness publicGroups ↔
      CircuitSatisfies hash right streams witness publicGroups :=
  circuitSatisfies_iff_of_filter hash streams witness publicGroups same nonRange_silent holds

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
      Satisfies hash right streams witness publicGroups outputs :=
  satisfies_iff_of_filter hash streams witness publicGroups outputs same nonRange_silent holds

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

/-- The actual comparison fold preserves arbitrary-witness satisfaction and
ordered inputs, Impact groups and outputs when the source relation carries the
needed comparison ranges. -/
theorem parsed_reuseComparisons_preserves_kernel (source : Array Json) (left right : Program)
    (sourceDecoded : source.toList.mapM decodeInstruction = .ok left.instructions)
    (runDecoded : (Backend.RangeDedup.reuseComparisons source).toList.mapM decodeInstruction =
      .ok right.instructions)
    (ranges : RangeDedup.ComparisonBitChecks left.instructions) :
    ∀ hash streams witness groups returns,
      (Satisfies hash left streams witness groups returns ↔
        Satisfies hash right streams witness groups returns) := by
  obtain ⟨optimized, optimizedParsed, stable, holds⟩ :=
    RangeDedup.reuseComparisons_preserves_decoded source left.instructions sourceDecoded ranges
  have equality : optimized = right.instructions :=
    Except.ok.inj (optimizedParsed.symm.trans runDecoded)
  intro hash streams witness groups returns
  apply satisfies_iff_of_filter hash streams witness groups returns
    (keep := RangeDedup.stableOutsideComparisons)
  · rw [← equality]
    exact stable.symm
  · intro instruction dropped
    cases instruction <;> simp_all [RangeDedup.stableOutsideComparisons, silent]
  · simpa only [equality] using (holds hash witness).symm

end Noctium.Verification.RangeDedupKernel
