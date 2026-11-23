import Noctium.Backend.NativeProducer
import Noctium.Verification.NativeRelationJson
import Noctium.Verification.ScalarParserAgreement
import Noctium.Verification.ScalarNormalization
import Noctium.Verification.ScalarValidationMeaning

namespace Noctium.Verification.RangeDedupComparisonMeaning

open Lean Backend.Native NativeRelation NativeRelationJson
open Noctium.Verification.ScalarValidationMeaning
open Noctium.Verification.ScalarNormalization

private theorem decodedLessThanFields {raw : Json} {a b : Operand}
    {bits : Nat} {output : String}
    (opcode : Backend.Native.stringField raw "op" = .ok "less_than")
    (decoded : NativeRelationJson.decodeInstruction raw =
      .ok (.lessThan a b bits output)) :
    NativeRelationJson.decodeOperandField raw "a" = .ok a ∧
      NativeRelationJson.decodeOperandField raw "b" = .ok b ∧
      NativeRelationJson.naturalField raw "bits" = .ok bits ∧
      Backend.Native.stringField raw "output" = .ok output := by
  unfold NativeRelationJson.decodeInstruction at decoded
  simp only [bind_ok, nativeJson_stringField_eq] at decoded
  rcases decoded with ⟨opcodeName, opcodeParsed, body⟩
  have opcodeEq : opcodeName = "less_than" := Except.ok.inj (opcodeParsed.symm.trans opcode)
  subst opcodeName
  simp only [bind_ok] at body
  rcases body with ⟨_, _, body⟩
  rcases body with ⟨foundBits, bitsParsed, body⟩
  rcases body with ⟨_, rangeChecked, body⟩
  rcases body with ⟨foundA, aParsed, body⟩
  rcases body with ⟨foundB, bParsed, body⟩
  rcases body with ⟨foundOutput, outputParsed, body⟩
  rcases body with ⟨_, outputChecked, result⟩
  simp only [Pure.pure, Except.pure] at result
  have resultEq : Instruction.lessThan foundA foundB foundBits foundOutput =
      Instruction.lessThan a b bits output := Except.ok.inj result
  injection resultEq with aEq bEq bitsEq outputEq
  subst a b bits output
  exact ⟨aParsed, bParsed, bitsParsed, outputParsed⟩

private theorem reference_not_immediate {text : String}
    (reference : text.startsWith "%" = true) : text.startsWith "0x" = false := by
  have prefixed : ['%'] <+: text.toList := by simpa using reference
  rcases prefixed with ⟨tail, equal⟩
  apply String.startsWith_string_eq_false_iff.mpr
  rw [← equal]
  simp

private theorem decodedReference {instruction : Json} {name text : String} {value : Operand}
    (textParsed : Backend.Native.stringField instruction name = .ok text)
    (decoded : NativeRelationJson.decodeOperandField instruction name = .ok value)
    (reference : text.startsWith "%" = true) : value = .reference text := by
  unfold Backend.Native.stringField at textParsed
  unfold NativeRelationJson.decodeOperandField at decoded
  simp only [bind_ok] at textParsed decoded
  rcases textParsed with ⟨json, jsonParsed, textParsed⟩
  rcases decoded with ⟨same, sameParsed, decoded⟩
  rw [jsonParsed] at sameParsed
  cases sameParsed
  unfold NativeRelationJson.decodeOperand at decoded
  simp only [bind_ok] at decoded
  rcases decoded with ⟨sameText, sameParsed, decoded⟩
  rw [textParsed] at sameParsed
  cases sameParsed
  simp only [reference_not_immediate reference, Bool.false_eq_true, ↓reduceIte, bind_ok] at decoded
  rcases decoded with ⟨_, _, result⟩
  cases result
  rfl

private theorem lessThanOpcode (bits : Nat) :
    (toString "less_than:" ++ bits.repr).startsWith "less_than:" = true := by
  apply String.startsWith_string_iff.mpr
  change "less_than:".toList <+: ("less_than:" ++ bits.repr).toList
  rw [String.toList_append]
  exact List.prefix_append _ _

private theorem interpretLessThan (hash : Hash) (inputs : Assignment) (bits : Nat)
    (left right : Backend.Native.Term) (leftValue rightValue : Scalar)
    (leftParsed : interpret hash inputs left = some leftValue)
    (rightParsed : interpret hash inputs right = some rightValue) :
    interpret hash inputs (.binary (toString "less_than:" ++ bits.repr) left right) =
      some (bit (decide (leftValue.val < rightValue.val))) := by
  have starts := lessThanOpcode bits
  have notAdd : (toString "less_than:" ++ bits.repr) ≠ "add" := by
    intro h
    rw [h] at starts
    contradiction
  have notMul : (toString "less_than:" ++ bits.repr) ≠ "mul" := by
    intro h
    rw [h] at starts
    contradiction
  have notEq : (toString "less_than:" ++ bits.repr) ≠ "test_eq" := by
    intro h
    rw [h] at starts
    contradiction
  simp [interpret, ScalarTermMeaning.interpret?, notAdd, notMul, notEq, starts,
    leftParsed, rightParsed]

/-- A successful producer comparison defines precisely the combined fact
with its optional asserted-less-than tag. This exposes the actual producer
inputs consumed by the reducer for the semantic proof below. -/
theorem acceptedLessThanDefinition {expected : Expected} {state next : State} {raw : Json}
    (opcode : Backend.Native.stringField raw "op" = .ok "less_than")
    (accepted : Backend.Native.validateInstruction expected state raw = .ok next) :
    ∃ leftText left right bits fact,
      Backend.Native.stringField raw "a" = .ok leftText ∧
      Backend.Native.argument state raw "a" = .ok left ∧
      Backend.Native.argument state raw "b" = .ok right ∧
      Backend.Native.width raw = .ok bits ∧
      left.maximum < 2 ^ bits ∧ right.maximum < 2 ^ bits ∧
      Backend.Native.combine (.binary (toString "less_than:" ++ bits.repr) left.term right.term) 1
        [left, right] = .ok fact ∧
      Backend.Native.defineResult state raw
        {fact with assertedLessThan :=
          match right.term with
          | .constant bound => if ['%'] <+: leftText.toList then some (leftText, bound) else none
          | _ => none} = .ok next := by
  unfold Backend.Native.validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨opcodeName, opcodeParsed, descriptor, descriptorParsed, registry,
    fieldsParsed, accepted⟩
  have opcodeEq : opcodeName = "less_than" := Except.ok.inj (opcodeParsed.symm.trans opcode)
  subst opcodeName
  simp at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨foundLeftText, leftTextParsed, foundLeft, leftAcceptedNative,
    foundRight, rightAcceptedNative, foundBits, bitsParsed, _, rangesChecked, foundFact,
    combined, defined⟩
  have rangeBool := ScalarValidationMeaning.ensure_ok.mp rangesChecked
  have ranges := Bool.and_eq_true_iff.mp rangeBool
  refine ⟨foundLeftText, foundLeft, foundRight, foundBits, foundFact,
    leftTextParsed, ?_, ?_, bitsParsed, ?_, ?_, combined, ?_⟩
  · unfold Backend.Native.argument
    rw [leftTextParsed]
    change (do
      let found ← Backend.Native.operand state foundLeftText
      Backend.Native.ensure (found.valueType == Backend.Native.NativeValueType.native)
        "native instruction operand must have Native type"
      pure found) = .ok foundLeft at leftAcceptedNative
    simp only [bind_ok] at leftAcceptedNative
    rcases leftAcceptedNative with ⟨found, operandAccepted, _, equal⟩
    have same : found = foundLeft := Except.ok.inj equal.2
    rw [← same]
    simpa only [leftTextParsed, Bind.bind, Except.bind] using operandAccepted
  · unfold Backend.Native.argument
    change (do
      let text ← Backend.Native.stringField raw "b"
      let found ← Backend.Native.operand state text
      Backend.Native.ensure (found.valueType == Backend.Native.NativeValueType.native)
        "native instruction operand must have Native type"
      pure found) = .ok foundRight at rightAcceptedNative
    simp only [bind_ok] at rightAcceptedNative
    rcases rightAcceptedNative with ⟨rightText, rightTextParsed, rightNative⟩
    rcases rightNative with ⟨found, operandAccepted, _, _, equal⟩
    have same : found = foundRight := Except.ok.inj equal
    rw [← same]
    rw [rightTextParsed]
    simpa only [Bind.bind, Except.bind] using operandAccepted
  · exact of_decide_eq_true ranges.1
  · exact of_decide_eq_true ranges.2
  · exact defined

/-- Every accepted NativeProducer less_than definition preserves the partial
scalar meaning invariant for the exact typed relation decoded from its JSON. -/
theorem lessThanStepMeaning {hash : Hash} {inputs witness : Assignment}
    {expected : Expected} {state next : State} {raw : Json}
    {a b : Operand} {bits : Nat} {output : String}
    (invariant : StateMeaning hash inputs witness state)
    (opcode : Backend.Native.stringField raw "op" = .ok "less_than")
    (decoded : NativeRelationJson.decodeInstruction raw =
      .ok (.lessThan a b bits output))
    (holds : Instruction.Holds hash witness (.lessThan a b bits output))
    (accepted : Backend.Native.validateInstruction expected state raw = .ok next) :
    StateMeaning hash inputs witness next := by
  obtain ⟨leftText, left, right, producerBits, fact, leftTextParsed, leftAccepted,
      rightAccepted, producerWidth, leftRange, rightRange, combined, defined⟩ :=
    acceptedLessThanDefinition opcode accepted
  have decodedFields := decodedLessThanFields opcode decoded
  have widthEq := ScalarParserAgreement.natField_naturalField_agree raw "bits"
    producerBits bits (by
      unfold Backend.Native.width at producerWidth
      simp only [bind_ok] at producerWidth
      rcases producerWidth with ⟨found, fieldParsed, _, equal⟩
      have same : found = producerBits := Except.ok.inj equal.2
      rw [← same]
      exact fieldParsed) decodedFields.2.2.1
  have leftMeaning := argument_decoded_meaning invariant leftAccepted decodedFields.1
  have rightMeaning := argument_decoded_meaning invariant rightAccepted decodedFields.2.1
  have leftBound : (a.read witness).val < 2 ^ bits := by
    exact Nat.lt_of_le_of_lt leftMeaning.bound (by simpa [widthEq] using leftRange)
  have rightBound : (b.read witness).val < 2 ^ bits := by
    exact Nat.lt_of_le_of_lt rightMeaning.bound (by simpa [widthEq] using rightRange)
  have outputEquation : witness output =
      bit (decide ((a.read witness).val < (b.read witness).val)) := holds leftBound rightBound
  have resultTermMeaning : interpret hash inputs
      (.binary (toString "less_than:" ++ producerBits.repr) left.term right.term) =
      some (witness output) := by
    rw [interpretLessThan hash inputs producerBits left.term right.term
      (a.read witness) (b.read witness) leftMeaning.term rightMeaning.term]
    simp [outputEquation]
  have resultBound : (witness output).val ≤ 1 := by
    rw [outputEquation]
    have canonical := bit_canonical (decide ((a.read witness).val < (b.read witness).val))
    omega
  have combinedMeaning : FactMeaning hash inputs witness fact (witness output) :=
    combine_meaning combined resultTermMeaning resultBound
  let assumption := match right.term with
    | .constant bound => if ['%'] <+: leftText.toList then some (leftText, bound) else none
    | _ => none
  have finalFactMeaning : FactMeaning hash inputs witness
      {fact with assertedLessThan := assumption} (witness output) := by
    refine ⟨combinedMeaning.term, combinedMeaning.bound, ?_⟩
    intro identifier exclusive tag nonzero
    change (match right.term with
      | .constant bound => if ['%'] <+: leftText.toList then some (leftText, bound) else none
      | _ => none) = some (identifier, exclusive) at tag
    cases rightTerm : right.term with
    | constant bound =>
      rw [rightTerm] at tag
      by_cases leftPrefix : ['%'] <+: leftText.toList
      · simp only [leftPrefix] at tag
        have pairEq : (leftText, bound) = (identifier, exclusive) := Option.some.inj tag
        have identifierEq : leftText = identifier := congrArg Prod.fst pairEq
        have exclusiveEq : bound = exclusive := congrArg Prod.snd pairEq
        subst identifier
        subst exclusive
        have leftPrefixBool : leftText.startsWith "%" = true :=
          String.startsWith_string_iff.mpr leftPrefix
        have leftReference := decodedReference leftTextParsed decodedFields.1 leftPrefixBool
        have strict : (a.read witness).val < (b.read witness).val := by
          by_cases strict : (a.read witness).val < (b.read witness).val
          · exact strict
          · have zeroResult : witness output = zero := by
              rw [outputEquation]
              simp [strict, bit, zero]
            exact False.elim (nonzero zeroResult)
        have rightValue : b.read witness = scalar bound := by
          have parsed := rightMeaning.term
          rw [rightTerm] at parsed
          have scalarEq : scalar bound = b.read witness :=
            Option.some.inj (by
              simpa only [ScalarTermMeaning.interpret_constant] using parsed)
          exact scalarEq.symm
        have constantBound : (b.read witness).val ≤ bound := by
          rw [rightValue]
          exact scalar_le bound
        have leftValue : a.read witness = witness leftText := by
          rw [leftReference]
          rfl
        simpa only [leftValue] using Nat.lt_of_lt_of_le strict constantBound
      · simp [leftPrefix] at tag
    | _ => simp [rightTerm] at tag
  have definedResult : Backend.Native.defineResult state raw
      {fact with assertedLessThan := assumption} = .ok next := by
    change Backend.Native.defineResult state raw
      {fact with assertedLessThan := assumption} = .ok next at defined
    exact defined
  apply defineResult_meaning invariant ?_ definedResult
  intro identifier parsed
  have outputEq : identifier = output := Except.ok.inj (parsed.symm.trans decodedFields.2.2.2)
  subst identifier
  exact finalFactMeaning

end Noctium.Verification.RangeDedupComparisonMeaning
