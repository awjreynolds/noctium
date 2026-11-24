import Noctium.Verification.ScalarValidationProjection
import Noctium.Verification.ScalarValidationArithmeticLoop
import Noctium.Verification.ScalarValidationOutputMeaning

namespace Noctium.Verification.ScalarValidationProjectionComparison

open Lean Backend.Native NativeRelation NativeRelationJson ScalarNormalization
open Noctium.Verification.ScalarValidationProjection
open Noctium.Verification.ScalarValidationMeaning
open Noctium.Verification.ScalarValidationArithmeticLoop (combine_native)
open Noctium.Verification.ScalarValidationOutputMeaning (nativeJson_stringField_eq)

private theorem bind_ok {α β : Type} {value : Except String α}
    {next : α → Except String β} {result : β} :
    (value >>= next) = .ok result ↔ ∃ found, value = .ok found ∧ next found = .ok result :=
  ScalarValidationMeaning.bind_ok

private theorem ensure_ok {condition : Bool} {message : String} :
    Backend.Native.ensure condition message = .ok () ↔ condition = true :=
  ScalarValidationMeaning.ensure_ok

private theorem foreignCurve_eq_of_beq (left right : Foreign.Curve)
    (same : (left == right) = true) : left = right := by
  cases left <;> cases right
  all_goals change Foreign.instBEqCurve.beq _ _ = true at same
  all_goals simp [Foreign.instBEqCurve.beq, Foreign.Curve.ctorIdx] at same ⊢

private theorem foreignKind_eq_of_beq (left right : Foreign.Kind)
    (same : (left == right) = true) : left = right := by
  cases left with
  | base leftCurve =>
      cases right with
      | base rightCurve =>
          change (leftCurve == rightCurve) = true at same
          exact congrArg Foreign.Kind.base (foreignCurve_eq_of_beq leftCurve rightCurve same)
      | _ => simp [BEq.beq, Foreign.instBEqKind.beq] at same
  | scalar leftCurve =>
      cases right with
      | scalar rightCurve =>
          change (leftCurve == rightCurve) = true at same
          exact congrArg Foreign.Kind.scalar (foreignCurve_eq_of_beq leftCurve rightCurve same)
      | _ => simp [BEq.beq, Foreign.instBEqKind.beq] at same
  | point leftCurve =>
      cases right with
      | point rightCurve =>
          change (leftCurve == rightCurve) = true at same
          exact congrArg Foreign.Kind.point (foreignCurve_eq_of_beq leftCurve rightCurve same)
      | _ => simp [BEq.beq, Foreign.instBEqKind.beq] at same

private theorem nativeValueType_eq_of_beq {left right : NativeValueType}
    (same : (left == right) = true) : left = right := by
  change Noctium.Backend.Native.instBEqNativeValueType.beq left right = true at same
  cases left <;> cases right <;>
    simp_all [Noctium.Backend.Native.instBEqNativeValueType.beq]
  case foreign.foreign leftKind rightKind =>
    exact foreignKind_eq_of_beq leftKind rightKind same

/-- A checked producer definition preserves projections for existing facts
and adds the projection for its new output when its value type admits one. -/
private theorem defineResult_scalarProjection
    {hash : Hash} {inputs witness : Assignment} {state next : State}
    {instruction : Json} {fact : Fact}
    (invariant : StateScalarProjection hash inputs witness state)
    (meaning : ∀ identifier,
      Backend.Native.stringField instruction "output" = .ok identifier →
        ScalarProjection hash inputs witness fact (witness identifier))
    (accepted : defineResult state instruction fact = .ok next) :
    StateScalarProjection hash inputs witness next := by
  unfold defineResult at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨identifier, outputParsed, defined⟩
  unfold define at defined
  simp only [bind_ok] at defined
  rcases defined with ⟨_, _, _, _, result⟩
  cases result
  intro name found member scalarType
  simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at member
  rcases member with prior | ⟨sameName, sameFact⟩
  · exact invariant name found prior scalarType
  · subst name
    subst found
    exact meaning identifier outputParsed

private theorem combine_fields {term : Backend.Native.Term} {maximum : Nat}
    {children : List Fact} {fact : Fact}
    (accepted : combine term maximum children = .ok fact) :
    fact.term = term ∧ fact.maximum = maximum ∧ fact.assertedLessThan = none := by
  unfold combine at accepted
  dsimp [Backend.Native.ensure] at accepted
  split at accepted
  · simp only [Pure.pure, Except.pure] at accepted
    cases accepted
    exact ⟨rfl, rfl, rfl⟩
  · contradiction

/-- Decode the operands using the actual strict relation decoder, retaining the
same JSON fields read by the Native producer. -/
private theorem decodedTestEqFields {raw : Json} {left right : Operand} {output : String}
    (opcode : Backend.Native.stringField raw "op" = .ok "test_eq")
    (decoded : NativeRelationJson.decodeInstruction raw =
      .ok (.testEq left right output)) :
    NativeRelationJson.decodeOperandField raw "a" = .ok left ∧
      NativeRelationJson.decodeOperandField raw "b" = .ok right ∧
      Backend.Native.stringField raw "output" = .ok output := by
  unfold NativeRelationJson.decodeInstruction at decoded
  simp only [ScalarValidationMeaning.bind_ok,
    ScalarValidationOutputMeaning.nativeJson_stringField_eq] at decoded
  rcases decoded with ⟨opcodeName, opcodeParsed, body⟩
  have opcodeEq : opcodeName = "test_eq" :=
    Except.ok.inj (opcodeParsed.symm.trans opcode)
  subst opcodeName
  simp only [ScalarValidationMeaning.bind_ok] at body
  rcases body with ⟨_, _, leftName, leftParsed, rightName, rightParsed,
    outputName, outputParsed, _, _, result⟩
  simp only [Pure.pure, Except.pure] at result
  have resultEq := Except.ok.inj result
  injection resultEq with leftEq rightEq outputEq
  subst left right output
  exact ⟨leftParsed, rightParsed, outputParsed⟩

private theorem decodedLessThanFields {raw : Json} {left right : Operand}
    {bits : Nat} {output : String}
    (opcode : Backend.Native.stringField raw "op" = .ok "less_than")
    (decoded : NativeRelationJson.decodeInstruction raw =
      .ok (.lessThan left right bits output)) :
    NativeRelationJson.decodeOperandField raw "a" = .ok left ∧
      NativeRelationJson.decodeOperandField raw "b" = .ok right ∧
      NativeRelationJson.naturalField raw "bits" = .ok bits ∧
      Backend.Native.stringField raw "output" = .ok output := by
  unfold NativeRelationJson.decodeInstruction at decoded
  simp only [ScalarValidationMeaning.bind_ok,
    ScalarValidationOutputMeaning.nativeJson_stringField_eq] at decoded
  rcases decoded with ⟨opcodeName, opcodeParsed, body⟩
  have opcodeEq : opcodeName = "less_than" :=
    Except.ok.inj (opcodeParsed.symm.trans opcode)
  subst opcodeName
  simp only [ScalarValidationMeaning.bind_ok] at body
  rcases body with ⟨_, _, body⟩
  rcases body with ⟨foundBits, bitsParsed, body⟩
  rcases body with ⟨_, _, body⟩
  rcases body with ⟨foundLeft, leftParsed, body⟩
  rcases body with ⟨foundRight, rightParsed, body⟩
  rcases body with ⟨foundOutput, outputParsed, body⟩
  rcases body with ⟨_, _, result⟩
  simp only [Pure.pure, Except.pure] at result
  have resultEq : Instruction.lessThan foundLeft foundRight foundBits foundOutput =
      Instruction.lessThan left right bits output := Except.ok.inj result
  injection resultEq with leftEq rightEq bitsEq outputEq
  subst left right bits output
  exact ⟨leftParsed, rightParsed, bitsParsed, outputParsed⟩

private theorem decodedReference_notImmediate {text : String}
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
  simp only [decodedReference_notImmediate reference, Bool.false_eq_true,
    ↓reduceIte, bind_ok] at decoded
  rcases decoded with ⟨_, _, result⟩
  cases result
  rfl

private theorem accepted_lessThan_components {expected : Expected} {state next : State}
    {raw : Json}
    (opcode : Backend.Native.stringField raw "op" = .ok "less_than")
    (accepted : validateInstruction expected state raw = .ok next) :
    ∃ leftText left right bits fact,
      Backend.Native.stringField raw "a" = .ok leftText ∧
      argument state raw "a" = .ok left ∧
      argument state raw "b" = .ok right ∧
      FactScalarType left.valueType ∧ FactScalarType right.valueType ∧
      Backend.Native.width raw = .ok bits ∧
      left.maximum < 2 ^ bits ∧ right.maximum < 2 ^ bits ∧
      combine (.binary (toString "less_than:" ++ bits.repr) left.term right.term) 1
        [left, right] = .ok fact ∧
      defineResult state raw
        {fact with assertedLessThan := match right.term with
          | .constant bound => if ['%'] <+: leftText.toList then some (leftText, bound) else none
          | _ => none} = .ok next := by
  unfold validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨opcodeName, opcodeParsed, descriptor, descriptorParsed,
    registry, fieldsParsed, accepted⟩
  have opcodeEq : opcodeName = "less_than" :=
    Except.ok.inj (opcodeParsed.symm.trans opcode)
  subst opcodeName
  simp at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨leftText, leftTextParsed, left, leftNativeAccepted,
    right, rightNativeAccepted, bits, bitsParsed, _, rangesChecked, fact,
    combined, defined⟩
  have ranges := Bool.and_eq_true_iff.mp (ensure_ok.mp rangesChecked)
  have leftRange : left.maximum < 2 ^ bits := of_decide_eq_true ranges.1
  have rightRange : right.maximum < 2 ^ bits := of_decide_eq_true ranges.2
  change (do
    let found ← Backend.Native.operand state leftText
    Backend.Native.ensure (found.valueType == NativeValueType.native)
      "native instruction operand must have Native type"
    pure found) = .ok left at leftNativeAccepted
  rcases bind_ok.mp leftNativeAccepted with ⟨found, operandAccepted, checked⟩
  rcases bind_ok.mp checked with ⟨_, nativeAccepted, result⟩
  have same : found = left := Except.ok.inj result
  subst left
  have leftSupported : FactScalarType found.valueType :=
    scalarType_of_nativeType (ensure_ok.mp nativeAccepted)
  have leftArgument : argument state raw "a" = .ok found := by
    unfold argument
    rw [leftTextParsed]
    exact operandAccepted
  have rightParts := Backend.Native.nativeArgument_parts rightNativeAccepted
  have rightSupported : FactScalarType right.valueType :=
    scalarType_of_nativeType rightParts.2
  have producerWidth : Backend.Native.width raw = .ok bits := by
    exact bitsParsed
  exact ⟨leftText, found, right, bits, fact, leftTextParsed, leftArgument,
    rightParts.1, leftSupported, rightSupported, producerWidth, leftRange,
    rightRange, combined, defined⟩

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

/-- The producer admits `test_eq` on some non-scalar types too. This component
lemma keeps the checked producer type equality explicit; the projection step
below separately requires scalar support for both operands. -/
private theorem accepted_testEq_components {expected : Expected} {state next : State}
    {raw : Json}
    (opcode : Backend.Native.stringField raw "op" = .ok "test_eq")
    (accepted : validateInstruction expected state raw = .ok next) :
    ∃ left right fact,
      argument state raw "a" = .ok left ∧
      argument state raw "b" = .ok right ∧
      left.valueType = right.valueType ∧
      combine (.binary "test_eq" left.term right.term) 1 [left, right] = .ok fact ∧
      defineResult state raw fact = .ok next := by
  unfold validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨opcodeName, opcodeParsed, descriptor, support, fields, accepted⟩
  have opcodeEq : opcodeName = "test_eq" :=
    Except.ok.inj (opcodeParsed.symm.trans opcode)
  subst opcodeName
  simp [bind_ok] at accepted
  rcases accepted with ⟨_, left, leftAccepted, right, rightAccepted, sameType, reducer⟩
  rcases sameType with ⟨_, sameType⟩
  have sameTypeBool : (left.valueType == right.valueType) = true := ensure_ok.mp sameType
  have sameValueType : left.valueType = right.valueType :=
    nativeValueType_eq_of_beq sameTypeBool
  rcases reducer with ⟨_, _, _, ⟨fact, combined, defined⟩⟩
  exact ⟨left, right, fact, leftAccepted, rightAccepted, sameValueType, combined, defined⟩

/-- An accepted `test_eq` preserves the scalar projection when both actual
producer operands have Native or Bool scalar support. `holds` supplies the
arbitrary satisfying witness equation for the decoded relation instruction. -/
theorem accepted_testEq_projection_step
    {hash : Hash} {inputs witness : Assignment} {expected : Expected}
    {state next : State} {raw : Json} {left right : Operand} {output : String}
    (invariant : StateScalarProjection hash inputs witness state)
    (leftSupported : ∀ {fact}, argument state raw "a" = .ok fact →
      FactScalarType fact.valueType)
    (opcode : Backend.Native.stringField raw "op" = .ok "test_eq")
    (accepted : validateInstruction expected state raw = .ok next)
    (decoded : NativeRelationJson.decodeInstruction raw =
      .ok (.testEq left right output))
    (holds : Instruction.Holds hash witness (.testEq left right output)) :
    StateScalarProjection hash inputs witness next := by
  obtain ⟨leftFact, rightFact, fact, leftAccepted, rightAccepted,
    sameValueType, combined, defined⟩ := accepted_testEq_components opcode accepted
  have decodedFields := decodedTestEqFields opcode decoded
  have leftScalarType := leftSupported leftAccepted
  have rightScalarType : FactScalarType rightFact.valueType := by
    simpa [sameValueType] using leftScalarType
  have leftProjection := argument_decoded_meaning
    ScalarParserAgreement.producer_immediate_success invariant leftAccepted decodedFields.1
    leftScalarType
  have rightProjection := argument_decoded_meaning
    ScalarParserAgreement.producer_immediate_success invariant rightAccepted decodedFields.2.1
    rightScalarType
  have holdsEquation : witness output = bit (decide (left.read witness = right.read witness)) := by
    simpa [Instruction.Holds] using holds
  have resultMeaning :
      interpret hash inputs (.binary "test_eq" leftFact.term rightFact.term) =
        some (witness output) := by
    simp [interpret_testEq, leftProjection.term, rightProjection.term, holdsEquation]
  have resultBound : (witness output).val ≤ 1 := by
    rw [holdsEquation]
    rcases bit_canonical (decide (left.read witness = right.read witness)) with zeroValue | oneValue
    · rw [zeroValue]
      omega
    · rw [oneValue]
      omega
  obtain ⟨termEq, maximumEq, noComparison⟩ := combine_fields combined
  have outputProjection : ScalarProjection hash inputs witness fact (witness output) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [termEq]
      exact resultMeaning
    · rw [maximumEq]
      exact resultBound
    · intro name exclusive tag _
      rw [noComparison] at tag
      cases tag
  have outputMeaning : ∀ identifier,
      Backend.Native.stringField raw "output" = .ok identifier →
        ScalarProjection hash inputs witness fact (witness identifier) := by
    intro identifier parsed
    have same : identifier = output := Except.ok.inj (parsed.symm.trans decodedFields.2.2)
    subst identifier
    exact outputProjection
  exact defineResult_scalarProjection invariant outputMeaning defined

/-- An accepted native `less_than` preserves scalar projections. The witness
equation is used only under the producer checked range and bit-width bounds. -/
theorem accepted_lessThan_projection_step
    {hash : Hash} {inputs witness : Assignment} {expected : Expected}
    {state next : State} {raw : Json} {left right : Operand} {bits : Nat} {output : String}
    (invariant : StateScalarProjection hash inputs witness state)
    (opcode : Backend.Native.stringField raw "op" = .ok "less_than")
    (accepted : validateInstruction expected state raw = .ok next)
    (decoded : NativeRelationJson.decodeInstruction raw =
      .ok (.lessThan left right bits output))
    (holds : Instruction.Holds hash witness (.lessThan left right bits output)) :
    StateScalarProjection hash inputs witness next := by
  obtain ⟨leftText, leftFact, rightFact, producerBits, fact, leftTextParsed,
    leftAccepted, rightAccepted, leftScalarType, rightScalarType, producerWidth,
    leftRange, rightRange, combined, defined⟩ :=
    accepted_lessThan_components opcode accepted
  have decodedFields := decodedLessThanFields opcode decoded
  have producerBitsParsed : Backend.Native.natField raw "bits" = .ok producerBits := by
    unfold Backend.Native.width at producerWidth
    rcases bind_ok.mp producerWidth with ⟨found, parsed, rest⟩
    rcases bind_ok.mp rest with ⟨_, _, result⟩
    have same : found = producerBits := Except.ok.inj result
    rw [← same]
    exact parsed
  have widthAgreement := ScalarParserAgreement.natField_naturalField_agree raw "bits"
    producerBits bits producerBitsParsed decodedFields.2.2.1
  have leftProjection := argument_decoded_meaning
    ScalarParserAgreement.producer_immediate_success invariant leftAccepted decodedFields.1
    leftScalarType
  have rightProjection := argument_decoded_meaning
    ScalarParserAgreement.producer_immediate_success invariant rightAccepted decodedFields.2.1
    rightScalarType
  have leftBound : (left.read witness).val < 2 ^ bits := by
    exact Nat.lt_of_le_of_lt leftProjection.bound (by simpa [widthAgreement] using leftRange)
  have rightBound : (right.read witness).val < 2 ^ bits := by
    exact Nat.lt_of_le_of_lt rightProjection.bound (by simpa [widthAgreement] using rightRange)
  have outputEquation : witness output =
      bit (decide ((left.read witness).val < (right.read witness).val)) :=
    holds leftBound rightBound
  have resultMeaning : interpret hash inputs
      (.binary (toString "less_than:" ++ producerBits.repr) leftFact.term rightFact.term) =
      some (witness output) := by
    rw [interpretLessThan hash inputs producerBits leftFact.term rightFact.term
      (left.read witness) (right.read witness) leftProjection.term rightProjection.term]
    simp [outputEquation]
  have resultBound : (witness output).val ≤ 1 := by
    rw [outputEquation]
    rcases bit_canonical (decide ((left.read witness).val < (right.read witness).val)) with zeroValue | oneValue
    · rw [zeroValue]
      omega
    · rw [oneValue]
      omega
  obtain ⟨termEq, maximumEq, _⟩ := combine_fields combined
  let assumption := match rightFact.term with
    | .constant bound => if ['%'] <+: leftText.toList then some (leftText, bound) else none
    | _ => none
  have outputProjection : ScalarProjection hash inputs witness
      {fact with assertedLessThan := assumption} (witness output) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [termEq]
      exact resultMeaning
    · rw [maximumEq]
      exact resultBound
    · intro name exclusive tag nonzero
      change (match rightFact.term with
        | .constant bound => if ['%'] <+: leftText.toList then some (leftText, bound) else none
        | _ => none) = some (name, exclusive) at tag
      cases rightTerm : rightFact.term with
      | constant bound =>
          rw [rightTerm] at tag
          by_cases leftPrefix : ['%'] <+: leftText.toList
          · simp only [leftPrefix] at tag
            have pairEq : (leftText, bound) = (name, exclusive) := Option.some.inj tag
            have nameEq : leftText = name := congrArg Prod.fst pairEq
            have exclusiveEq : bound = exclusive := congrArg Prod.snd pairEq
            subst name
            subst exclusive
            have leftReference : leftText.startsWith "%" = true :=
              String.startsWith_string_iff.mpr leftPrefix
            have reference := decodedReference leftTextParsed decodedFields.1 leftReference
            have strict : (left.read witness).val < (right.read witness).val := by
              by_cases isLess : (left.read witness).val < (right.read witness).val
              · exact isLess
              · have outputZero : witness output = zero := by
                  rw [outputEquation]
                  simp [isLess, bit]
                exact False.elim (nonzero outputZero)
            have rightBoundedByTag : (right.read witness).val ≤ bound := by
              have rightTermMeaning := rightProjection.term
              rw [rightTerm] at rightTermMeaning
              have scalarValue : right.read witness = scalar bound := by
                have same : some (scalar bound) = some (right.read witness) := by
                  simpa only [interpret_constant] using rightTermMeaning
                exact Option.some.inj same.symm
              rw [scalarValue]
              exact ScalarValidationMeaning.scalar_le bound
            have strictByReference : (witness leftText).val < (right.read witness).val := by
              simpa only [reference, Operand.read] using strict
            exact Nat.lt_of_lt_of_le strictByReference rightBoundedByTag
          · simp [leftPrefix] at tag
      | input _ => simp [rightTerm] at tag
      | unary _ _ => simp [rightTerm] at tag
      | binary _ _ _ => simp [rightTerm] at tag
      | select _ _ _ => simp [rightTerm] at tag
      | hash _ => simp [rightTerm] at tag
      | bytes _ => simp [rightTerm] at tag
  have outputMeaning : ∀ identifier,
      Backend.Native.stringField raw "output" = .ok identifier →
        ScalarProjection hash inputs witness {fact with assertedLessThan := assumption}
          (witness identifier) := by
    intro identifier parsed
    have same : identifier = output := Except.ok.inj (parsed.symm.trans decodedFields.2.2.2)
    subst identifier
    exact outputProjection
  exact defineResult_scalarProjection invariant outputMeaning defined

end Noctium.Verification.ScalarValidationProjectionComparison
