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

end Noctium.Verification.ScalarValidationProjectionComparison
