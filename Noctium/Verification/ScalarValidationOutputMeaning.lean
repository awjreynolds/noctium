import Noctium.Backend.NativeProducer
import Noctium.Verification.NativeRelationJson
import Noctium.Verification.ScalarValidationMeaning

namespace Noctium.Verification.ScalarValidationOutputMeaning

open Lean Backend.Native NativeRelation NativeRelationJson ScalarNormalization
open Noctium.Verification.ScalarValidationMeaning

theorem map_ok {α β : Type} {value : Except String α} {next : α → β}
    {result : β} : next <$> value = .ok result ↔
      ∃ found, value = .ok found ∧ next found = result := by
  cases value <;> simp [Functor.map, Except.map]

theorem mapM_value_agreement {α β γ δ : Type} (left : α → Except String β)
    (right : α → Except String γ) (leftValue : β → δ) (rightValue : γ → δ)
    (agreement : ∀ item a b, left item = .ok a → right item = .ok b →
      leftValue a = rightValue b)
    {items : List α} {a : List β} {b : List γ}
    (accepted : items.mapM left = .ok a) (decoded : items.mapM right = .ok b) :
    a.map leftValue = b.map rightValue := by
  induction items generalizing a b with
  | nil =>
    simp only [List.mapM_nil] at accepted decoded
    cases accepted
    cases decoded
    rfl
  | cons head tail ih =>
    simp only [List.mapM_cons, bind_ok] at accepted decoded
    rcases accepted with ⟨aHead, aHeadParsed, aTail, aTailParsed, result⟩
    rcases decoded with ⟨bHead, bHeadParsed, bTail, bTailParsed, decodedResult⟩
    cases result
    cases decodedResult
    simp only [List.map_cons, agreement head aHead bHead aHeadParsed bHeadParsed,
      ih aTailParsed bTailParsed]

theorem arguments_decoded_meaning
    {hash : Hash} {inputs witness : Assignment} {state : State}
    {instruction : Json} {name : String} {facts : List Fact} {values : List Operand}
    (invariant : StateMeaning hash inputs witness state)
    (accepted : arguments state instruction name = .ok facts)
    (decoded : (do NativeRelationJson.decodeOperands (← instruction.getObjVal? name)) =
      .ok values) :
    facts.map (fun fact => interpret hash inputs fact.term) =
      values.map (fun value => some (value.read witness)) := by
  unfold Backend.Native.arguments Backend.Native.arrayField at accepted
  simp only [bind_ok] at accepted decoded
  rcases accepted with ⟨array, ⟨json, parsed, arrayParsed⟩, _, _, accepted⟩
  rcases decoded with ⟨same, sameParsed, decoded⟩
  rw [parsed] at sameParsed
  cases sameParsed
  unfold NativeRelationJson.decodeOperands at decoded
  simp only [bind_ok] at decoded
  rcases decoded with ⟨sameArray, sameParsed, decoded⟩
  rw [arrayParsed] at sameParsed
  cases sameParsed
  apply mapM_value_agreement _ _ _ _ ?_ accepted decoded
  intro item fact value factParsed valueParsed
  simp only [bind_ok] at factParsed
  rcases factParsed with ⟨text, textParsed, factParsed⟩
  exact (operand_decoded_meaning invariant textParsed factParsed valueParsed).term

theorem nativeJson_stringField_eq (value : Json) (name : String) :
    NativeRelationJson.stringField value name = Backend.Native.stringField value name := rfl

private theorem arguments_of_checked_native_arguments
    {state : State} {raw : Json} {name : String} {facts : List Fact}
    (accepted : (do
      let values ← arguments state raw name
      values.forM (fun fact => Backend.Native.ensure
        (fact.valueType == NativeValueType.native)
        "native instruction operand must have Native type")
      pure values) = .ok facts) :
    arguments state raw name = .ok facts := by
  simp only [bind_ok] at accepted
  rcases accepted with ⟨_, parsed, ⟨_, _, result⟩⟩
  cases result
  exact parsed

/-- An accepted Native scalar output returns the validated state unchanged.
Its exact source return terms have checked scalar interpretations equal to the
decoded witness values in order. The opcode premise pins producer dispatch to the
output branch while the JSON decoder proves the schema and operands. -/
theorem accepted_output_meaning
    {hash : Hash} {inputs witness : Assignment} {expected : Expected}
    {state next : State} {raw : Json} {values : List Operand}
    (invariant : StateMeaning hash inputs witness state)
    (accepted : validateInstruction expected state raw = .ok next)
    (opcode : Backend.Native.stringField raw "op" = .ok "output")
    (decoded : NativeRelationJson.decodeInstruction raw = .ok (.output values)) :
    next = state ∧
      expected.returns.map (interpret hash inputs) =
        (values.map (·.read witness)).map some := by
  classical
  simp [validateInstruction, opcode, bind_ok, map_ok] at accepted
  have descriptorSpec := Classical.choose_spec accepted
  let factsExistence := descriptorSpec.2.2.2
  let facts := Classical.choose factsExistence
  have factsSpec := Classical.choose_spec factsExistence
  have factsAccepted := factsSpec.1
  let checkedExistence := factsSpec.2.1
  have equalityCheck := Classical.choose_spec checkedExistence
  have stateEq := factsSpec.2.2
  have argumentsAccepted := arguments_of_checked_native_arguments factsAccepted
  have matched : facts.map (·.term) = expected.returns :=
    eq_of_beq (ensure_ok.mp equalityCheck)
  simp [NativeRelationJson.decodeInstruction, opcode, bind_ok, map_ok,
    nativeJson_stringField_eq] at decoded
  rcases decoded with ⟨_, json, jsonParsed, valuesDecoded⟩
  have valuesMeaning := arguments_decoded_meaning invariant argumentsAccepted (by
    simp only [jsonParsed]
    exact valuesDecoded)
  constructor
  · exact stateEq.symm
  · rw [← matched]
    simpa only [List.map_map, Function.comp_def] using valuesMeaning

/-- The strict decoder and accepted producer read the same ordered Impact
payload. Each term in the producer's selected source group has a scalar
interpretation equal to its corresponding decoded operand under the witness.
The strict decoder currently accepts literal-one Impact guards. -/
theorem accepted_impact_meaning
    {hash : Hash} {inputs witness : Assignment} {expected : Expected}
    {state next : State} {raw : Json} {guard : Operand} {values : List Operand}
    (invariant : StateMeaning hash inputs witness state)
    (accepted : validateInstruction expected state raw = .ok next)
    (opcode : Backend.Native.stringField raw "op" = .ok "impact")
    (decoded : NativeRelationJson.decodeInstruction raw = .ok (.impact guard values)) :
    ∃ group, expected.groups[state.groupCount]? = some group ∧
      next = {state with groupCount := state.groupCount + 1} ∧
      group.map (interpret hash inputs) = (values.map (·.read witness)).map some := by
  unfold validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨found, op, _, _, _, _, accepted⟩
  have same := Except.ok.inj (op.symm.trans opcode)
  subst found
  simp only [bind_ok] at accepted
  rcases accepted with ⟨_, _, _, _, _, _, _, _, facts, factsParsed, accepted⟩
  have argumentsAccepted := arguments_of_checked_native_arguments factsParsed
  split at accepted
  next group groupParsed =>
    simp only [Pure.pure, Except.pure] at accepted
    have checked :
        (facts.map (·.term) == group) = true ∧
          next = {state with groupCount := state.groupCount + 1} := by
      cases empty : expected.groupGuards.isEmpty
      · cases sourceGuard : expected.groupGuards[state.groupCount]?
        · simp [empty, sourceGuard, Bind.bind, Except.bind, MonadExcept.throw] at accepted
        · simp [empty, sourceGuard, bind_ok] at accepted
          obtain ⟨_, ⟨_, payloadChecked⟩, advanced⟩ := accepted
          exact ⟨ensure_ok.mp payloadChecked, advanced.symm⟩
      · simp [empty, bind_ok] at accepted
        obtain ⟨_, ⟨_, payloadChecked⟩, advanced⟩ := accepted
        exact ⟨ensure_ok.mp payloadChecked, advanced.symm⟩
    have matched : facts.map (·.term) = group := eq_of_beq checked.1
    simp [NativeRelationJson.decodeInstruction, opcode, bind_ok,
      nativeJson_stringField_eq] at decoded
    rcases decoded with ⟨_, decodedGuard, _, decoded⟩
    cases decodedGuard <;> simp [bind_ok, map_ok] at decoded
    rcases decoded with ⟨_, json, jsonParsed, valuesDecoded, _⟩
    have valuesMeaning := arguments_decoded_meaning invariant argumentsAccepted (by
      simp only [jsonParsed]
      exact valuesDecoded)
    refine ⟨group, groupParsed, checked.2, ?_⟩
    rw [← matched]
    simpa only [List.map_map, Function.comp_def] using valuesMeaning
  next => contradiction

end Noctium.Verification.ScalarValidationOutputMeaning
