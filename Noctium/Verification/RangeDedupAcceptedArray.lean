import Noctium.Verification.RangeDedupProducer
import Noctium.Verification.RangeDedupComparisonMeaning
import Noctium.Verification.RangeDedupAssertMeaning
import Noctium.Verification.RangeDedupWholeTrace
import Noctium.Verification.ScalarValidationNativeLoop
import Noctium.Verification.ScalarValidationOutputMeaning

namespace Noctium.Verification.RangeDedupAcceptedArray

open Lean Backend.Native NativeRelation NativeRelationJson
open Noctium.Backend.RangeDedup
open Noctium.Verification.RangeDedup
open Noctium.Verification.RangeDedupProducer
open Noctium.Verification.ScalarValidationMeaning
open Noctium.Verification.ScalarValidationArithmeticLoop
open Noctium.Verification.ScalarValidationNativeLoop
open Noctium.Verification.ScalarValidationOutputMeaning
open Noctium.Verification.ScalarNormalization

private theorem refine_nativeDefinitions {state next : Backend.Native.State}
    {text : String} {maximum : Nat}
    (definitions : NativeDefinitions state)
    (accepted : Backend.Native.refine state text maximum = .ok next) :
    NativeDefinitions next := by
  unfold Backend.Native.refine at accepted
  simp only [ScalarValidationMeaning.bind_ok] at accepted
  rcases accepted with ⟨fact, _, accepted⟩
  cases reference : text.startsWith "%" with
  | true =>
    simp only [reference, ↓reduceIte, Pure.pure, Except.pure] at accepted
    rcases accepted with ⟨_, _, result⟩
    cases result
    intro name found member
    simp only [List.mem_map] at member
    rcases member with ⟨⟨oldName, oldFact⟩, oldMember, equal⟩
    have sameName : oldName = name := by simpa using congrArg Prod.fst equal
    have sameFact :
        (if oldName == text then {oldFact with maximum := min oldFact.maximum maximum}
          else oldFact) = found := by simpa using congrArg Prod.snd equal
    subst name
    subst found
    have valueTypeUnchanged :
        (if oldName == text then {oldFact with maximum := min oldFact.maximum maximum}
          else oldFact).valueType = oldFact.valueType := by
      split <;> rfl
    rw [valueTypeUnchanged]
    exact definitions _ _ oldMember
  | false =>
    simp only [reference, Bool.false_eq_true, ↓reduceIte] at accepted
    simp [Backend.Native.ensure] at accepted
    rcases accepted with ⟨_, result⟩
    by_cases bounded : fact.maximum ≤ maximum
    · simp [bounded] at result
      cases result
      exact definitions
    · simp [bounded, Except.map, Functor.map] at result

private theorem accepted_assert_nativeDefinitions
    {expected : Backend.Native.Expected} {state next : Backend.Native.State}
    {raw : Json}
    (definitions : NativeDefinitions state)
    (opcode : Backend.Native.stringField raw "op" = .ok "assert")
    (accepted : Backend.Native.validateInstruction expected state raw = .ok next) :
    NativeDefinitions next := by
  unfold Backend.Native.validateInstruction at accepted
  simp only [ScalarValidationMeaning.bind_ok] at accepted
  rcases accepted with ⟨opcodeName, opcodeParsed, descriptor, descriptorParsed,
    registry, fieldsParsed, accepted⟩
  have opcodeEq : opcodeName = "assert" := Except.ok.inj (opcodeParsed.symm.trans opcode)
  subst opcodeName
  simp at accepted
  simp only [ScalarValidationMeaning.bind_ok] at accepted
  rcases accepted with ⟨value, valueParsed, _, booleanAccepted, accepted⟩
  let assertionCounted := if expected.assertions[state.assertionCount]? == some value.term then
    {state with assertionCount := state.assertionCount + 1} else state
  let assertionState : Backend.Native.State :=
    {assertionCounted with
      establishedAssertions := (value.term :: assertionCounted.establishedAssertions).eraseDups}
  have assertionDefinitions : NativeDefinitions assertionState := by
    intro name fact member
    cases matched : (expected.assertions[state.assertionCount]? == some value.term)
    · exact definitions name fact (by
        simpa [assertionState, assertionCounted, matched] using member)
    · exact definitions name fact (by
        simpa [assertionState, assertionCounted, matched] using member)
  split at accepted
  · simp only [ScalarValidationMeaning.bind_ok] at accepted
    rcases accepted with ⟨_, _, refined⟩
    exact refine_nativeDefinitions assertionDefinitions refined
  · cases accepted
    exact assertionDefinitions

private theorem accepted_lessThan_nativeDefinitions
    {expected : Backend.Native.Expected} {state next : Backend.Native.State}
    {raw : Json}
    (definitions : NativeDefinitions state)
    (opcode : Backend.Native.stringField raw "op" = .ok "less_than")
    (accepted : Backend.Native.validateInstruction expected state raw = .ok next) :
    NativeDefinitions next := by
  obtain ⟨leftText, _, right, _, fact, _, _, _, _, _, _, combined, defined⟩ :=
    RangeDedupComparisonMeaning.acceptedLessThanDefinition opcode accepted
  have factNative : fact.valueType = NativeValueType.native := combine_native combined
  have definedFactNative :
      ({fact with assertedLessThan := match right.term with
        | .constant bound => if ['%'] <+: leftText.toList then some (leftText, bound) else none
        | _ => none}).valueType = NativeValueType.native := by
    simpa using factNative
  exact defineResult_nativeDefinitions definitions definedFactNative defined

/-- The bounded producer trace class used below permits arbitrary ordering of
native input/arithmetic steps, comparisons, assertions, and a checked output.
Other producer opcodes need their own state-meaning step before they enter this
induction. -/
inductive AcceptedMeaningStep (hash : Hash) (witness : Assignment) (raw : Json) : Prop where
  | native (steps : NativeStepHolds hash witness raw) : AcceptedMeaningStep hash witness raw
  | lessThan {left right : Operand} {width : Nat} {output : String}
      (opcode : Backend.Native.stringField raw "op" = .ok "less_than")
      (decoded : NativeRelationJson.decodeInstruction raw = .ok (.lessThan left right width output))
      (holds : Instruction.Holds hash witness (.lessThan left right width output)) :
      AcceptedMeaningStep hash witness raw
  | assertion {condition : Operand}
      (opcode : Backend.Native.stringField raw "op" = .ok "assert")
      (decoded : NativeRelationJson.decodeInstruction raw = .ok (.assert condition))
      (holds : Instruction.Holds hash witness (.assert condition)) :
      AcceptedMeaningStep hash witness raw
  | output {values : List Operand}
      (opcode : Backend.Native.stringField raw "op" = .ok "output")
      (decoded : NativeRelationJson.decodeInstruction raw = .ok (.output values)) :
      AcceptedMeaningStep hash witness raw

private theorem decodedLessThanFields {raw : Json} {left right : Operand}
    {width : Nat} {output : String}
    (opcode : Backend.Native.stringField raw "op" = .ok "less_than")
    (decoded : NativeRelationJson.decodeInstruction raw =
      .ok (.lessThan left right width output)) :
    NativeRelationJson.decodeOperandField raw "a" = .ok left ∧
      NativeRelationJson.decodeOperandField raw "b" = .ok right ∧
      NativeRelationJson.naturalField raw "bits" = .ok width := by
  unfold NativeRelationJson.decodeInstruction at decoded
  simp only [ScalarValidationMeaning.bind_ok,
    ScalarValidationOutputMeaning.nativeJson_stringField_eq] at decoded
  rcases decoded with ⟨opcodeName, opcodeParsed, body⟩
  have opcodeEq : opcodeName = "less_than" := Except.ok.inj (opcodeParsed.symm.trans opcode)
  subst opcodeName
  simp only [ScalarValidationMeaning.bind_ok] at body
  rcases body with ⟨_, _, body⟩
  rcases body with ⟨_, bitsParsed, body⟩
  rcases body with ⟨_, _, body⟩
  rcases body with ⟨_, leftParsed, body⟩
  rcases body with ⟨_, rightParsed, body⟩
  rcases body with ⟨_, _, body⟩
  rcases body with ⟨_, _, result⟩
  simp only [Pure.pure, Except.pure] at result
  have resultEq := Except.ok.inj result
  injection resultEq with leftEq rightEq widthEq outputEq
  subst left right width output
  exact ⟨leftParsed, rightParsed, bitsParsed⟩

/-- The accepted producer loop's per-item bounds become concrete bounds for
each decoded comparison under that occurrence's checked prefix meaning. This
works for every list member, including repeated pairs separated by other
instructions. -/
theorem accepted_lessThan_witnessBounds
    {hash : Hash} {inputs witness : Assignment} {expected : Backend.Native.Expected}
    {state next : Backend.Native.State}
    {raw : Json} {left right : Operand} {width : Nat} {output : String}
    (meaning : StateMeaning hash inputs witness state)
    (opcode : Backend.Native.stringField raw "op" = .ok "less_than")
    (decoded : NativeRelationJson.decodeInstruction raw =
      .ok (.lessThan left right width output))
    (accepted : Backend.Native.validateInstruction expected state raw = .ok next) :
    (left.read witness).val < 2 ^ width ∧ (right.read witness).val < 2 ^ width := by
  obtain ⟨_, _, _, producerWidth, _, _, leftAccepted, rightAccepted, widthAccepted,
    leftMaximum, rightMaximum, _, _⟩ :=
    RangeDedupComparisonMeaning.acceptedLessThanDefinition opcode accepted
  have fields := decodedLessThanFields opcode decoded
  have widthEq := Noctium.Verification.ScalarParserAgreement.natField_naturalField_agree raw "bits"
    producerWidth width (by
      unfold Backend.Native.width at widthAccepted
      simp only [ScalarValidationMeaning.bind_ok] at widthAccepted
      rcases widthAccepted with ⟨found, fieldParsed, _, equal⟩
      have same : found = producerWidth := Except.ok.inj equal.2
      rw [← same]
      exact fieldParsed) fields.2.2
  have leftMeaning := argument_decoded_meaning meaning leftAccepted fields.1
  have rightMeaning := argument_decoded_meaning meaning rightAccepted fields.2.1
  constructor
  · exact Nat.lt_of_le_of_lt leftMeaning.bound (by simpa [widthEq] using leftMaximum)
  · exact Nat.lt_of_le_of_lt rightMeaning.bound (by simpa [widthEq] using rightMaximum)

private theorem acceptedMeaningStep_preserves
    {hash : Hash} {inputs witness : Assignment} {expected : Backend.Native.Expected}
    {state next : Backend.Native.State} {raw : Json}
    (meaning : StateMeaning hash inputs witness state)
    (definitions : NativeDefinitions state)
    (inputSchema : ∀ requirement ∈ expected.inputs,
      requirement.ty = .native ∧ requirement.activityGuard = none)
    (inputAgreement : ∀ requirement ∈ expected.inputs,
      witness requirement.identifier = inputs requirement.identifier)
    (step : AcceptedMeaningStep hash witness raw)
    (accepted : Backend.Native.validateInstruction expected state raw = .ok next) :
    StateMeaning hash inputs witness next ∧ NativeDefinitions next := by
  cases step with
  | native nativeStep =>
    cases nativeStep with
    | publicInput opcode =>
      obtain ⟨requirement, selected⟩ := accepted_input_requirement_selected
        (visibility := .«public») (by simpa [inputOpcode] using opcode) accepted
      have member : requirement ∈ expected.inputs := List.mem_of_getElem? selected
      obtain ⟨nativeInput, unguarded⟩ := inputSchema requirement member
      have agreement := inputAgreement requirement member
      exact ⟨public_input_step_meaning meaning selected nativeInput unguarded agreement
          opcode accepted,
        input_nativeDefinitions_step (visibility := .«public») definitions selected nativeInput
          unguarded (by simpa [inputOpcode] using opcode) accepted⟩
    | privateInput opcode =>
      obtain ⟨requirement, selected⟩ := accepted_input_requirement_selected
        (visibility := .«private») (by simpa [inputOpcode] using opcode) accepted
      have member : requirement ∈ expected.inputs := List.mem_of_getElem? selected
      obtain ⟨nativeInput, unguarded⟩ := inputSchema requirement member
      have agreement := inputAgreement requirement member
      exact ⟨private_input_step_meaning meaning selected nativeInput unguarded agreement
          opcode accepted,
        input_nativeDefinitions_step (visibility := .«private») definitions selected nativeInput
          unguarded (by simpa [inputOpcode] using opcode) accepted⟩
    | arithmetic arithmeticStep =>
      cases arithmeticStep with
      | add _ _ _ opcode decoded holds =>
        exact accepted_native_add_step_meaning meaning definitions opcode accepted decoded holds
      | mul _ _ _ opcode decoded holds =>
        exact accepted_native_mul_step_meaning meaning definitions opcode accepted decoded holds
      | neg _ _ opcode decoded holds =>
        exact accepted_native_neg_step_meaning meaning definitions opcode accepted decoded holds
  | lessThan opcode decoded holds =>
    exact ⟨RangeDedupComparisonMeaning.lessThanStepMeaning meaning opcode decoded holds accepted,
      accepted_lessThan_nativeDefinitions definitions opcode accepted⟩
  | assertion opcode decoded holds =>
    exact ⟨RangeDedupAssertMeaning.assertStepMeaning meaning opcode decoded holds accepted,
      accepted_assert_nativeDefinitions definitions opcode accepted⟩
  | output opcode decoded =>
    have outputMeaning := accepted_output_meaning meaning accepted opcode decoded
    rw [outputMeaning.1]
    exact ⟨meaning, definitions⟩

/-- Thread producer meaning through any accepted indexed trace in the declared
step class and retain the invariant at every instruction pre-state. This lets
separate comparisons use their actual checked prefix definitions even when
other supported instructions occur between them. -/
theorem accepted_loop_meaning_at_steps
    {hash : Hash} {inputs witness : Assignment} {expected : Backend.Native.Expected}
    {items : List (Json × Nat)} {initial final : Backend.Native.State}
    (initialMeaning : StateMeaning hash inputs witness initial)
    (initialDefinitions : NativeDefinitions initial)
    (inputSchema : ∀ requirement ∈ expected.inputs,
      requirement.ty = .native ∧ requirement.activityGuard = none)
    (inputAgreement : ∀ requirement ∈ expected.inputs,
      witness requirement.identifier = inputs requirement.identifier)
    (steps : ∀ item ∈ items, AcceptedMeaningStep hash witness item.1)
    (accepted : Backend.Native.validateInstructionLoop expected items initial = .ok final) :
    StateMeaning hash inputs witness final ∧ NativeDefinitions final ∧
      ∀ raw index, (raw, index) ∈ items →
        ∃ state next, StateMeaning hash inputs witness state ∧ NativeDefinitions state ∧
          Backend.Native.validateInstruction expected state raw = .ok next ∧
          StateMeaning hash inputs witness next ∧ NativeDefinitions next := by
  induction items generalizing initial final with
  | nil =>
    have initialEq : initial = final := by injection accepted
    subst final
    exact ⟨initialMeaning, initialDefinitions, by simp⟩
  | cons head tail ih =>
    rw [Backend.Native.validateInstructionLoop, List.forIn_cons] at accepted
    cases checked : Backend.Native.validateInstruction expected initial head.1 with
    | error message => simp [checked, Bind.bind, Except.bind] at accepted
    | ok next =>
      simp only [checked, bind_pure_comp] at accepted
      have after := acceptedMeaningStep_preserves initialMeaning initialDefinitions
        inputSchema inputAgreement (steps head (by simp)) checked
      obtain ⟨finalMeaning, finalDefinitions, tailVisits⟩ :=
        ih after.1 after.2
          (fun item member => steps item (List.mem_cons_of_mem _ member)) accepted
      refine ⟨finalMeaning, finalDefinitions, ?_⟩
      intro raw index member
      have headOrTail : (raw, index) = head ∨ (raw, index) ∈ tail := by
        simpa only [List.mem_cons] using member
      rcases headOrTail with headMember | tailMember
      · have rawEq : raw = head.1 := congrArg Prod.fst headMember
        have indexEq : index = head.2 := congrArg Prod.snd headMember
        subst raw
        subst index
        exact ⟨initial, next, initialMeaning, initialDefinitions, checked,
          after.1, after.2⟩
      · exact tailVisits raw index tailMember

private theorem foldObservation_copyJson (source destination : String) :
    Noctium.Verification.RangeDedupWholeTrace.foldObservation
        (comparisonCopyJson source destination) =
      [.comparisonOutput destination] := by
  have noKey : comparison? (comparisonCopyJson source destination) = none := rfl
  rw [Noctium.Verification.RangeDedupWholeTrace.foldObservation, noKey,
    comparisonCopyJson_decodes]

/-- Compose the exact whole-array pass with accepted producer meaning for
arbitrary traces in `AcceptedMeaningStep`, including any number of comparisons
interleaved with inputs, arithmetic, assertions, and outputs. The existing
all-witness fold theorem still requires `ComparisonBitChecks`; this result also
exposes producer-derived bounds at every accepted comparison for the chosen
assignment. -/
theorem acceptedArrayWholeFold
    {hash : Hash} {inputs witness : Assignment} {expected : Backend.Native.Expected}
    {source : Array Json} {original : List Instruction}
    {initial final : Backend.Native.State}
    (initialMeaning : StateMeaning hash inputs witness initial)
    (initialDefinitions : NativeDefinitions initial)
    (inputSchema : ∀ requirement ∈ expected.inputs,
      requirement.ty = .native ∧ requirement.activityGuard = none)
    (inputAgreement : ∀ requirement ∈ expected.inputs,
      witness requirement.identifier = inputs requirement.identifier)
    (steps : ∀ item ∈ source.toList.zipIdx, AcceptedMeaningStep hash witness item.1)
    (decoded : source.toList.mapM decodeInstruction = .ok original)
    (ranges : ComparisonBitChecks original)
    (accepted : Backend.Native.validateInstructionLoop expected source.toList.zipIdx
      initial = .ok final) :
    ∃ optimized,
      (reuseComparisons source).toList.mapM decodeInstruction = .ok optimized ∧
      optimized.filter stableOutsideComparisons = original.filter stableOutsideComparisons ∧
      (∀ candidateHash candidateWitness,
        (∀ instruction ∈ optimized, Instruction.Holds candidateHash candidateWitness instruction) ↔
        (∀ instruction ∈ original, Instruction.Holds candidateHash candidateWitness instruction)) ∧
      (reuseComparisons source).toList.flatMap
          Noctium.Verification.RangeDedupWholeTrace.foldObservation =
        source.toList.flatMap Noctium.Verification.RangeDedupWholeTrace.foldObservation ∧
      StateMeaning hash inputs witness final ∧ NativeDefinitions final ∧
      (∀ raw index, (raw, index) ∈ source.toList.zipIdx →
        ∀ left right width output,
          Backend.Native.stringField raw "op" = .ok "less_than" →
          NativeRelationJson.decodeInstruction raw =
            .ok (.lessThan left right width output) →
          (left.read witness).val < 2 ^ width ∧ (right.read witness).val < 2 ^ width) ∧
      (∀ raw index, (raw, index) ∈ source.toList.zipIdx →
        ∀ values, Backend.Native.stringField raw "op" = .ok "output" →
          NativeRelationJson.decodeInstruction raw = .ok (.output values) →
          expected.returns.map (interpret hash inputs) =
            (values.map (·.read witness)).map some) := by
  obtain ⟨optimized, optimizedDecoded, stable, equivalent⟩ :=
    reuseComparisons_preserves_decoded source original decoded ranges
  have observations := Backend.RangeDedup.reuseComparisons_preserves_observations
    source Noctium.Verification.RangeDedupWholeTrace.foldObservation (by
      intro earlier earlierMember later laterMember key first output earlierKey laterKey
      rw [foldObservation_copyJson first output]
      simp [Noctium.Verification.RangeDedupWholeTrace.foldObservation, laterKey])
  obtain ⟨finalMeaning, finalDefinitions, visits⟩ := accepted_loop_meaning_at_steps
    initialMeaning initialDefinitions inputSchema inputAgreement steps accepted
  refine ⟨optimized, optimizedDecoded, stable, equivalent, observations,
    finalMeaning, finalDefinitions, ?_, ?_⟩
  · intro raw index member left right width output opcode decodedComparison
    obtain ⟨state, next, before, _, checked, _, _⟩ := visits raw index member
    exact accepted_lessThan_witnessBounds before opcode decodedComparison checked
  · intro raw index member values opcode decodedOutput
    obtain ⟨state, next, before, _, checked, _, _⟩ := visits raw index member
    exact (accepted_output_meaning before checked opcode decodedOutput).2

end Noctium.Verification.RangeDedupAcceptedArray
