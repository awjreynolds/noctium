import Noctium.Backend.NativeProducer
import Noctium.Verification.NativeRelationJson
import Noctium.Verification.ScalarValidationMeaning

namespace Noctium.Verification.RangeDedupAssertMeaning

open Lean Backend.Native NativeRelation NativeRelationJson
open Noctium.Verification.ScalarValidationMeaning

private theorem decodedAssertCondition {raw : Json} {condition : Operand}
    (opcode : Backend.Native.stringField raw "op" = .ok "assert")
    (decoded : NativeRelationJson.decodeInstruction raw = .ok (.assert condition)) :
    NativeRelationJson.decodeOperandField raw "cond" = .ok condition := by
  unfold NativeRelationJson.decodeInstruction at decoded
  simp only [bind_ok, nativeJson_stringField_eq] at decoded
  rcases decoded with ⟨opcodeName, opcodeParsed, body⟩
  have opcodeEq : opcodeName = "assert" := Except.ok.inj (opcodeParsed.symm.trans opcode)
  subst opcodeName
  simp only [bind_ok] at body
  rcases body with ⟨_, _, foundCondition, result⟩
  rcases result with ⟨conditionParsed, result⟩
  simp only [Pure.pure, Except.pure] at result
  have resultEq : Instruction.assert foundCondition = Instruction.assert condition :=
    Except.ok.inj result
  injection resultEq with conditionEq
  subst condition
  exact conditionParsed

/-- Invert the producer's checked refine operation. A reference updates its
stored maximum to the minimum of the old maximum and the checked bound. A
nonreference succeeds only when its existing maximum already passes the bound. -/
theorem refineMeaning {hash : Hash} {inputs witness : Assignment} {state next : State}
    {text : String} {maximum : Nat}
    (invariant : StateMeaning hash inputs witness state)
    (bounded : text.startsWith "%" = true → (witness text).val ≤ maximum)
    (accepted : Backend.Native.refine state text maximum = .ok next) :
    StateMeaning hash inputs witness next := by
  unfold Backend.Native.refine at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨fact, _, accepted⟩
  cases isReference : text.startsWith "%" with
  | true =>
    simp only [isReference, ↓reduceIte, Pure.pure, Except.pure] at accepted
    rcases accepted with ⟨_, _, result⟩
    cases result
    intro name value member
    simp only [List.mem_map] at member
    rcases member with ⟨⟨oldName, oldValue⟩, member, equal⟩
    have meaning := invariant oldName oldValue member
    cases same : oldName == text
    · simp only [same, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at equal
      rcases equal with ⟨rfl, rfl⟩
      exact meaning
    · have nameEq : oldName = text := eq_of_beq same
      simp only [same, ↓reduceIte, Prod.mk.injEq] at equal
      rcases equal with ⟨rfl, rfl⟩
      refine ⟨meaning.term, ?_, meaning.comparison⟩
      exact Nat.le_min.mpr ⟨meaning.bound, by simpa [nameEq] using bounded isReference⟩
  | false =>
    simp only [isReference, Bool.false_eq_true, ↓reduceIte] at accepted
    rcases accepted with ⟨_, _, accepted⟩
    simp only [bind_ok] at accepted
    rcases accepted with ⟨_, _, result⟩
    cases result
    exact invariant

/-- Every accepted NativeProducer assertion preserves the scalar meaning
invariant. Its witness must make the exact decoded condition nonzero. When the
producer recorded a comparison bound, the FactMeaning comparison field proves
the strict value bound needed by the real refine operation. -/
theorem assertStepMeaning {hash : Hash} {inputs witness : Assignment}
    {expected : Expected} {state next : State} {raw : Json} {condition : Operand}
    (invariant : StateMeaning hash inputs witness state)
    (opcode : Backend.Native.stringField raw "op" = .ok "assert")
    (decoded : NativeRelationJson.decodeInstruction raw = .ok (.assert condition))
    (holds : Instruction.Holds hash witness (.assert condition))
    (accepted : Backend.Native.validateInstruction expected state raw = .ok next) :
    StateMeaning hash inputs witness next := by
  unfold Backend.Native.validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨opcodeName, opcodeParsed, descriptor, descriptorParsed, registry,
    fieldsParsed, accepted⟩
  have opcodeEq : opcodeName = "assert" := Except.ok.inj (opcodeParsed.symm.trans opcode)
  subst opcodeName
  simp at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨value, valueParsed, _, booleanAccepted, accepted⟩
  have conditionAccepted : Backend.Native.argument state raw "cond" = .ok value := by
    unfold Backend.Native.argument
    change (do
      let text ← Backend.Native.stringField raw "cond"
      let found ← Backend.Native.operand state text
      Backend.Native.ensure (found.valueType == Backend.Native.NativeValueType.native)
        "native instruction operand must have Native type"
      pure found) = .ok value at valueParsed
    simp only [bind_ok] at valueParsed
    rcases valueParsed with ⟨text, textParsed, nativeAccepted⟩
    rcases nativeAccepted with ⟨found, operandAccepted, _, _, equal⟩
    have same : found = value := Except.ok.inj equal
    rw [← same]
    rw [textParsed]
    simpa only [Bind.bind, Except.bind] using operandAccepted
  have decodedCondition := decodedAssertCondition opcode decoded
  have conditionMeaning := argument_decoded_meaning invariant conditionAccepted decodedCondition
  have conditionNonzero : condition.read witness ≠ zero := by
    simpa only [Instruction.Holds] using holds
  let assertionCounted :=
    if expected.assertions[state.assertionCount]? == some value.term then
      {state with assertionCount := state.assertionCount + 1}
    else state
  let assertionState : State :=
    {assertionCounted with
      establishedAssertions := (value.term :: assertionCounted.establishedAssertions).eraseDups}
  have assertionMeaning : StateMeaning hash inputs witness assertionState := by
    unfold StateMeaning
    intro identifier fact member
    cases matched : (expected.assertions[state.assertionCount]? == some value.term) with
    | false =>
      exact invariant identifier fact
        (by simpa [assertionState, assertionCounted, matched] using member)
    | true =>
      exact invariant identifier fact
        (by simpa [assertionState, assertionCounted, matched] using member)
  split at accepted
  next pair identifier exclusive tag =>
    simp only [bind_ok] at accepted
    rcases accepted with ⟨_, positiveCheck, refined⟩
    have positive : exclusive > 0 := of_decide_eq_true (ensure_ok.mp positiveCheck)
    have strict := conditionMeaning.comparison identifier exclusive tag conditionNonzero
    have actualBound : (witness identifier).val ≤ exclusive - 1 := by omega
    exact refineMeaning assertionMeaning (by intro _; exact actualBound) refined
  next =>
    cases accepted
    exact assertionMeaning

end Noctium.Verification.RangeDedupAssertMeaning
