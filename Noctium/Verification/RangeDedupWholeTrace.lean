import Noctium.Verification.RangeDedupAcceptedTrace

namespace Noctium.Verification.RangeDedupWholeTrace

open Lean Backend.Native NativeRelation NativeRelationJson
open Noctium.Backend.RangeDedup
open Noctium.Verification.RangeDedup
open Noctium.Verification.ScalarNormalization

inductive FoldObservation where
  | unchanged (item : Json)
  | comparisonOutput (name : String)

def ComparisonPairMeaning (hash : Hash) (witness : Assignment)
    (left right : Operand) (width : Nat) (firstOutput duplicateOutput : String) : Prop :=
  (Instruction.Holds hash witness (.lessThan left right width firstOutput) ∧
    Instruction.Holds hash witness
      (.equal (.reference firstOutput) (.reference duplicateOutput))) ↔
  (Instruction.Holds hash witness (.lessThan left right width firstOutput) ∧
    Instruction.Holds hash witness (.lessThan left right width duplicateOutput))

/-- Preserve exact raw JSON for non-comparisons. Comparisons and Copy
instructions share an output-name observation, since the fold replaces a
comparison with a Copy that keeps its destination. -/
def foldObservation (item : Json) : List FoldObservation :=
  match comparison? item with
  | some (_, output) => [.comparisonOutput output]
  | none =>
    match comparisonCopyOperands? item with
    | some (_, output) => [.comparisonOutput output]
    | none => [.unchanged item]

private theorem foldObservation_comparisonCopyJson (source output : String) :
    foldObservation (comparisonCopyJson source output) = [.comparisonOutput output] := by
  have noKey : comparison? (comparisonCopyJson source output) = none := rfl
  rw [foldObservation, noKey, comparisonCopyJson_decodes]

private theorem flatMap_preservedRaw (items : List Json)
    (unchanged : ∀ item ∈ items, foldObservation item = [.unchanged item]) :
    items.flatMap foldObservation = items.map FoldObservation.unchanged := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.flatMap_cons, unchanged head (by simp), List.map_cons,
      ih (fun item member => unchanged item (List.mem_cons_of_mem _ member))]
    simp

/-- Lift the previously checked producer trace to the exact whole fold output.
The fold theorem checks decode and relation satisfaction for `reuseComparisons
source` itself. The observation preserves each comparison output name and each
raw non-comparison item, including the prefix, assertion, and output JSON.

The semantic fold remains scoped to inputs satisfying `ComparisonBitChecks`.
The `acceptedBridge` argument is the accepted trace result from
`acceptedPrefixAssertComparisonOutputCopyBridge`, projected to this pair's
bounds, Copy relation, and output meaning. The producer trace and source array
must have the same ordered items. -/
theorem acceptedWholeFoldTrace
    (hash : Hash) (inputs witness : Assignment) (expected : Expected)
    (source : Array Json) (original : List Instruction)
    (prelude : List Json) (traceItems : List (Json × Nat))
    (assertionRaw earlier later outputRaw : Json)
    (left right : Operand) (width : Nat)
    (leftKey rightKey : String) (keyWidth : Nat)
    (firstOutput duplicateOutput : String) (outputValues : List Operand)
    (initial final : Backend.Native.State)
    (sourceShape : source.toList = prelude ++ [assertionRaw, earlier, later, outputRaw])
    (traceShape : traceItems.map Prod.fst =
      prelude ++ [assertionRaw, earlier, later, outputRaw])
    (earlierKey : comparison? earlier = some ((leftKey, rightKey, keyWidth), firstOutput))
    (laterKey : comparison? later = some ((leftKey, rightKey, keyWidth), duplicateOutput))
    (acceptedBridge :
      Backend.Native.validateInstructionLoop expected traceItems initial = .ok final ∧
      reuseComparisons #[earlier, later] =
        #[earlier, comparisonCopyJson firstOutput duplicateOutput] ∧
      decodeInstruction (comparisonCopyJson firstOutput duplicateOutput) =
        .ok (.equal (.reference firstOutput) (.reference duplicateOutput)) ∧
      ComparisonPairMeaning hash witness left right width firstOutput duplicateOutput ∧
      (left.read witness).val < 2 ^ width ∧ (right.read witness).val < 2 ^ width ∧
      Instruction.Holds hash witness
        (.equal (.reference firstOutput) (.reference duplicateOutput)) ∧
      expected.returns.map (interpret hash inputs) =
        (outputValues.map (·.read witness)).map some)
    (decoded : source.toList.mapM decodeInstruction = .ok original)
    (ranges : ComparisonBitChecks original)
    (preludeComparisonFree : ∀ item ∈ prelude, comparison? item = none)
    (preludeCopyFree : ∀ item ∈ prelude, comparisonCopyOperands? item = none)
    (assertionComparisonFree : comparison? assertionRaw = none)
    (assertionCopyFree : comparisonCopyOperands? assertionRaw = none)
    (outputComparisonFree : comparison? outputRaw = none)
    (outputCopyFree : comparisonCopyOperands? outputRaw = none) :
    ∃ optimized,
      (reuseComparisons source).toList.mapM decodeInstruction = .ok optimized ∧
      optimized.filter stableOutsideComparisons = original.filter stableOutsideComparisons ∧
      (∀ hash witness,
        (∀ instruction ∈ optimized, Instruction.Holds hash witness instruction) ↔
        (∀ instruction ∈ original, Instruction.Holds hash witness instruction)) ∧
      (reuseComparisons source).toList.flatMap foldObservation =
        prelude.map FoldObservation.unchanged ++
          [.unchanged assertionRaw, .comparisonOutput firstOutput,
            .comparisonOutput duplicateOutput, .unchanged outputRaw] ∧
      Backend.Native.validateInstructionLoop expected traceItems initial = .ok final ∧
      traceItems.map Prod.fst = source.toList ∧
      reuseComparisons #[earlier, later] =
        #[earlier, comparisonCopyJson firstOutput duplicateOutput] ∧
      decodeInstruction (comparisonCopyJson firstOutput duplicateOutput) =
        .ok (.equal (.reference firstOutput) (.reference duplicateOutput)) ∧
      ComparisonPairMeaning hash witness left right width firstOutput duplicateOutput ∧
      (left.read witness).val < 2 ^ width ∧ (right.read witness).val < 2 ^ width ∧
      expected.returns.map (interpret hash inputs) =
          (outputValues.map (·.read witness)).map some ∧
      Instruction.Holds hash witness
        (.equal (.reference firstOutput) (.reference duplicateOutput)) := by
  rcases acceptedBridge with
    ⟨producerAccepted, pairRewrite, copyDecoded, pairMeaning, leftBound,
      rightBound, copyHolds, outputMeaning⟩
  obtain ⟨optimized, optimizedDecoded, stable, satisfaction⟩ :=
    reuseComparisons_preserves_decoded source original decoded ranges
  have observations := Backend.RangeDedup.reuseComparisons_preserves_observations
    source foldObservation (by
      intro earlier earlierMember later laterMember key first output earlierKey laterKey
      rw [foldObservation_comparisonCopyJson first output]
      simp [foldObservation, laterKey])
  have preludeObserved : prelude.flatMap foldObservation =
      prelude.map FoldObservation.unchanged := flatMap_preservedRaw prelude (by
    intro item member
    simp [foldObservation, preludeComparisonFree item member, preludeCopyFree item member])
  rw [sourceShape] at observations
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    preludeObserved, foldObservation, earlierKey, laterKey,
    assertionComparisonFree, assertionCopyFree, outputComparisonFree,
    outputCopyFree] at observations
  have traceMatchesSource : traceItems.map Prod.fst = source.toList := by
    rw [sourceShape]
    exact traceShape
  exact ⟨optimized, optimizedDecoded, stable, satisfaction, observations,
    producerAccepted, traceMatchesSource, pairRewrite, copyDecoded,
    pairMeaning, leftBound, rightBound, outputMeaning, copyHolds⟩

end Noctium.Verification.RangeDedupWholeTrace
