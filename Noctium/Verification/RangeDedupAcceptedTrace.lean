import Noctium.Verification.RangeDedupProducer
import Noctium.Verification.RangeDedupComparisonMeaning
import Noctium.Verification.RangeDedupAssertMeaning
import Noctium.Verification.ScalarValidationNativeLoop
import Noctium.Verification.ScalarValidationOutputMeaning

namespace Noctium.Verification.RangeDedupAcceptedTrace

open Lean Backend.Native NativeRelation NativeRelationJson
open Noctium.Backend.RangeDedup
open Noctium.Verification.RangeDedup
open Noctium.Verification.RangeDedupProducer
open Noctium.Verification.ScalarValidationMeaning
open Noctium.Verification.ScalarNormalization
open Noctium.Verification.ScalarValidationNativeLoop
open Noctium.Verification.ScalarValidationOutputMeaning

private theorem loopCons {expected : Expected} {item : Json × Nat}
    {items : List (Json × Nat)} {initial middle final : State}
    (step : validateInstruction expected initial item.1 = .ok middle)
    (tail : validateInstructionLoop expected items middle = .ok final) :
    validateInstructionLoop expected (item :: items) initial = .ok final := by
  rw [validateInstructionLoop, List.forIn_cons]
  simp only [step, bind_pure_comp]
  exact tail

private theorem loopAppend {expected : Expected} {prelude suffix : List (Json × Nat)}
    {initial middle final : State}
    (first : validateInstructionLoop expected prelude initial = .ok middle)
    (second : validateInstructionLoop expected suffix middle = .ok final) :
    validateInstructionLoop expected (prelude ++ suffix) initial = .ok final := by
  induction prelude generalizing initial middle with
  | nil =>
    simp [validateInstructionLoop, pure, Except.pure] at first
    subst middle
    simpa using second
  | cons head tail ih =>
    change validateInstructionLoop expected (head :: (tail ++ suffix)) initial = .ok final
    rw [validateInstructionLoop, List.forIn_cons] at first ⊢
    cases checked : validateInstruction expected initial head.1 with
    | error message => simp [checked, Bind.bind, Except.bind] at first
    | ok next =>
      simp only [checked, bind_pure_comp] at first ⊢
      exact ih first second

/-- An ordered producer trace with a native input/arithmetic prelude, one
assertion, two accepted comparisons, and one checked output preserves the
comparison's decoded witness relation when reuse emits its exact Copy JSON.

The prelude may include accepted guarded public reads. Its private inputs still
follow the producer's unguarded-input rule.

This covers the listed trace shape only. Other producer opcodes and complete
program equivalence remain separate proof obligations. -/
theorem acceptedPrefixAssertComparisonOutputCopyBridge
    (hash : Hash) (inputs witness : Assignment) (expected : Expected)
    (prelude : List (Json × Nat)) (initial prefixFinal assertedState afterFirst
      afterSecond outputFinal : State)
    (assertionRaw earlier later outputRaw : Json)
    (assertionIndex earlierIndex laterIndex outputIndex : Nat)
    (condition : Operand) (leftKey rightKey : String) (left₁ right₁ left₂ right₂ : Operand)
    (width width₁ width₂ : Nat) (firstOutput duplicateOutput : String)
    (outputValues : List Operand)
    (initialMeaning : StateMeaning hash inputs witness initial)
    (initialNativeDefinitions : ScalarValidationArithmeticLoop.NativeDefinitions initial)
    (inputSchema : ∀ requirement ∈ expected.inputs,
      requirement.ty.isForeign = false)
    (inputAgreement : ∀ requirement ∈ expected.inputs,
      witness requirement.identifier = inputs requirement.identifier)
    (prefixSteps : ∀ item ∈ prelude, NativeStepHolds hash witness item.1)
    (prefixAccepted : validateInstructionLoop expected prelude initial = .ok prefixFinal)
    (assertionOpcode : Backend.Native.stringField assertionRaw "op" = .ok "assert")
    (assertionDecoded : decodeInstruction assertionRaw = .ok (.assert condition))
    (assertionHolds : Instruction.Holds hash witness (.assert condition))
    (assertionAccepted : validateInstruction expected prefixFinal assertionRaw = .ok assertedState)
    (earlierOpcode : Backend.Native.stringField earlier "op" = .ok "less_than")
    (earlierKey : comparison? earlier = some ((leftKey, rightKey, width), firstOutput))
    (earlierDecoded : decodeInstruction earlier =
      .ok (.lessThan left₁ right₁ width₁ firstOutput))
    (earlierHolds : Instruction.Holds hash witness
      (.lessThan left₁ right₁ width₁ firstOutput))
    (earlierAccepted : validateInstruction expected assertedState earlier = .ok afterFirst)
    (laterOpcode : Backend.Native.stringField later "op" = .ok "less_than")
    (laterKey : comparison? later = some ((leftKey, rightKey, width), duplicateOutput))
    (laterDecoded : decodeInstruction later =
      .ok (.lessThan left₂ right₂ width₂ duplicateOutput))
    (laterHolds : Instruction.Holds hash witness
      (.lessThan left₂ right₂ width₂ duplicateOutput))
    (laterAccepted : validateInstruction expected afterFirst later = .ok afterSecond)
    (outputOpcode : Backend.Native.stringField outputRaw "op" = .ok "output")
    (outputDecoded : decodeInstruction outputRaw = .ok (.output outputValues))
    (outputAccepted : validateInstruction expected afterSecond outputRaw = .ok outputFinal) :
    validateInstructionLoop expected
        (prelude ++ [(assertionRaw, assertionIndex), (earlier, earlierIndex),
          (later, laterIndex), (outputRaw, outputIndex)]) initial = .ok outputFinal ∧
      reuseComparisons #[earlier, later] =
        #[earlier, comparisonCopyJson firstOutput duplicateOutput] ∧
      decodeInstruction (comparisonCopyJson firstOutput duplicateOutput) =
        .ok (.equal (.reference firstOutput) (.reference duplicateOutput)) ∧
      ((Instruction.Holds hash witness
          (.lessThan left₁ right₁ width firstOutput) ∧
        Instruction.Holds hash witness
          (.equal (.reference firstOutput) (.reference duplicateOutput))) ↔
        (Instruction.Holds hash witness
          (.lessThan left₁ right₁ width firstOutput) ∧
        Instruction.Holds hash witness
          (.lessThan left₁ right₁ width duplicateOutput))) ∧
      (left₁.read witness).val < 2 ^ width ∧
      (right₁.read witness).val < 2 ^ width ∧
      (left₂.read witness).val < 2 ^ width ∧
      (right₂.read witness).val < 2 ^ width ∧
      Instruction.Holds hash witness
        (.equal (.reference firstOutput) (.reference duplicateOutput)) ∧
      expected.returns.map (interpret hash inputs) =
        (outputValues.map (·.read witness)).map some := by
  obtain ⟨prefixMeaning, _prefixNative⟩ := accepted_native_loop_meaning
    initialMeaning initialNativeDefinitions inputSchema inputAgreement prefixSteps prefixAccepted
  have assertionMeaning :=
    Noctium.Verification.RangeDedupAssertMeaning.assertStepMeaning prefixMeaning
      assertionOpcode assertionDecoded assertionHolds assertionAccepted
  have earlierMeaning :=
    Noctium.Verification.RangeDedupComparisonMeaning.lessThanStepMeaning assertionMeaning
      earlierOpcode earlierDecoded earlierHolds earlierAccepted
  have laterMeaning :=
    Noctium.Verification.RangeDedupComparisonMeaning.lessThanStepMeaning earlierMeaning
      laterOpcode laterDecoded laterHolds laterAccepted
  have outputMeaning := accepted_output_meaning laterMeaning outputAccepted
    outputOpcode outputDecoded
  have sameKeys := equalComparisonKeys_decode_agree earlier later leftKey rightKey width
    firstOutput duplicateOutput left₁ right₁ width₁ firstOutput
    left₂ right₂ width₂ duplicateOutput earlierKey laterKey earlierDecoded laterDecoded
  have emptyLoop : validateInstructionLoop expected [] outputFinal = .ok outputFinal := by
    simp [validateInstructionLoop, pure, Except.pure]
  have tailAccepted := loopCons (item := (outputRaw, outputIndex)) outputAccepted emptyLoop
  have tailAccepted := loopCons (item := (later, laterIndex)) laterAccepted tailAccepted
  have tailAccepted := loopCons (item := (earlier, earlierIndex)) earlierAccepted tailAccepted
  have tailAccepted := loopCons (item := (assertionRaw, assertionIndex)) assertionAccepted tailAccepted
  have fullAccepted := loopAppend prefixAccepted tailAccepted
  obtain ⟨pairRewrite, copyDecode, relationMeaning, left₁Bound, right₁Bound,
      left₂Bound, right₂Bound⟩ := acceptedProducerPairCopyBridge hash inputs witness expected
    earlier later assertedState afterFirst afterFirst afterSecond leftKey rightKey width
    firstOutput duplicateOutput left₁ right₁ width₁ firstOutput
    left₂ right₂ width₂ duplicateOutput earlierOpcode laterOpcode
    earlierAccepted laterAccepted earlierKey laterKey earlierDecoded laterDecoded
    assertionMeaning earlierMeaning
  have emittedCopyHolds : Instruction.Holds hash witness
      (.equal (.reference firstOutput) (.reference duplicateOutput)) := by
    have earlierKeyedHolds : Instruction.Holds hash witness
        (.lessThan left₁ right₁ width firstOutput) := by
      have result := earlierHolds
      rw [sameKeys.2.2.1] at result
      exact result
    have laterKeyedHolds : Instruction.Holds hash witness
        (.lessThan left₁ right₁ width duplicateOutput) := by
      have result := laterHolds
      rw [← sameKeys.1, ← sameKeys.2.1, sameKeys.2.2.2.1] at result
      exact result
    exact (relationMeaning.mpr ⟨earlierKeyedHolds, laterKeyedHolds⟩).2
  exact ⟨fullAccepted, pairRewrite, copyDecode, relationMeaning,
    left₁Bound, right₁Bound, left₂Bound, right₂Bound, emittedCopyHolds, outputMeaning.2⟩

end Noctium.Verification.RangeDedupAcceptedTrace
