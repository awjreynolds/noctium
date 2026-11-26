import Noctium.Backend.NativeProducer
import Noctium.Verification.NativeRelationJson
import Noctium.Verification.ScalarParserAgreement
import Noctium.Verification.ScalarValidationMeaning
import Noctium.Verification.ScalarValidationProjection

namespace Noctium.Verification.ScalarValidationOutputMeaning

open Lean Backend.Native NativeRelation NativeRelationJson ScalarNormalization
open Noctium.Verification.ScalarValidationMeaning

theorem map_ok {α β : Type} {value : Except String α} {next : α → β}
    {result : β} : next <$> value = .ok result ↔
      ∃ found, value = .ok found ∧ next found = result := by
  cases value <;> simp [Functor.map, Except.map]

theorem mapM_value_agreement {α β γ δ : Type} (left : α → Except String β)
    (right : α → Except String γ) (leftValue : β → δ) (rightValue : γ → δ)
    {items : List α} {a : List β} {b : List γ}
    (agreement : ∀ item x y, left item = .ok x → right item = .ok y →
      x ∈ a → leftValue x = rightValue y)
    (accepted : items.mapM left = .ok a) (decoded : items.mapM right = .ok b) :
    a.map leftValue = b.map rightValue := by
  induction items generalizing a b agreement with
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
    have agreementTail : ∀ item x y, left item = .ok x → right item = .ok y →
        x ∈ aTail → leftValue x = rightValue y := by
      intro item x y itemAccepted itemDecoded member
      exact agreement item x y itemAccepted itemDecoded (List.mem_cons_of_mem _ member)
    simp only [List.map_cons,
      agreement head aHead bHead aHeadParsed bHeadParsed (by simp),
      ih agreementTail aTailParsed bTailParsed]

private theorem arguments_decoded_meaning_of
    {hash : Hash} {inputs witness : Assignment} {state : State}
    {instruction : Json} {name : String} {facts : List Fact} {values : List Operand}
    (accepted : arguments state instruction name = .ok facts)
    (decoded : (do NativeRelationJson.decodeOperands (← instruction.getObjVal? name)) =
      .ok values)
    (argumentMeaning : ∀ item fact value,
      (do let text ← item.getStr?; operand state text) = .ok fact →
      NativeRelationJson.decodeOperand item = .ok value → fact ∈ facts →
      interpret hash inputs fact.term = some (value.read witness)) :
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
  intro item fact value factParsed valueParsed member
  exact argumentMeaning item fact value factParsed valueParsed member

theorem arguments_decoded_meaning
    {hash : Hash} {inputs witness : Assignment} {state : State}
    {instruction : Json} {name : String} {facts : List Fact} {values : List Operand}
    (invariant : StateMeaning hash inputs witness state)
    (accepted : arguments state instruction name = .ok facts)
    (decoded : (do NativeRelationJson.decodeOperands (← instruction.getObjVal? name)) =
      .ok values) :
    facts.map (fun fact => interpret hash inputs fact.term) =
      values.map (fun value => some (value.read witness)) := by
  apply arguments_decoded_meaning_of accepted decoded
  intro item fact value factParsed valueParsed _member
  simp only [bind_ok] at factParsed
  rcases factParsed with ⟨text, textParsed, factParsed⟩
  exact (operand_decoded_meaning invariant textParsed factParsed valueParsed).term

theorem nativeJson_stringField_eq (value : Json) (name : String) :
    NativeRelationJson.stringField value name = Backend.Native.stringField value name := rfl

private theorem native_checks_of_forM
    {facts : List Fact} {result : PUnit}
    (checks : facts.forM (fun fact => Backend.Native.ensure
      (fact.valueType == NativeValueType.native)
      "native instruction operand must have Native type") = .ok result) :
    ∀ fact, fact ∈ facts → (fact.valueType == NativeValueType.native) = true := by
  induction facts with
  | nil => simp
  | cons head tail ih =>
    change (do
      Backend.Native.ensure (head.valueType == NativeValueType.native)
        "native instruction operand must have Native type"
      tail.forM (fun fact => Backend.Native.ensure
        (fact.valueType == NativeValueType.native)
        "native instruction operand must have Native type")
    ) = .ok result at checks
    simp only [bind_ok] at checks
    rcases checks with ⟨_, headChecked, tailChecked⟩
    have headNative := ensure_ok.mp headChecked
    intro fact member
    rcases List.mem_cons.mp member with same | member
    · cases same
      exact headNative
    · exact ih tailChecked fact member

private theorem arguments_of_checked_native_arguments
    {state : State} {raw : Json} {name : String} {facts : List Fact}
    (accepted : (do
      let values ← arguments state raw name
      values.forM (fun fact => Backend.Native.ensure
        (fact.valueType == NativeValueType.native)
        "native instruction operand must have Native type")
      pure values) = .ok facts) :
    arguments state raw name = .ok facts ∧
      ∀ fact, fact ∈ facts → (fact.valueType == NativeValueType.native) = true := by
  simp only [bind_ok] at accepted
  rcases accepted with ⟨values, parsed, checkResult, checksAccepted, result⟩
  cases result
  exact ⟨parsed, native_checks_of_forM checksAccepted⟩

private theorem arguments_decoded_projection_meaning
    {hash : Hash} {inputs witness : Assignment} {state : State}
    {instruction : Json} {name : String} {facts : List Fact} {values : List Operand}
    (invariant : ScalarValidationProjection.StateScalarProjection hash inputs witness state)
    (accepted : arguments state instruction name = .ok facts)
    (nativeChecks : ∀ fact, fact ∈ facts →
      (fact.valueType == NativeValueType.native) = true)
    (decoded : (do NativeRelationJson.decodeOperands (← instruction.getObjVal? name)) =
      .ok values) :
    facts.map (fun fact => interpret hash inputs fact.term) =
      values.map (fun value => some (value.read witness)) := by
  apply arguments_decoded_meaning_of accepted decoded
  intro item fact value factParsed valueParsed member
  simp only [bind_ok] at factParsed
  rcases factParsed with ⟨text, textParsed, factParsed⟩
  have agreement := ScalarValidationProjection.operand_decoded_meaning
    ScalarParserAgreement.producer_immediate_success invariant textParsed factParsed valueParsed
  exact (agreement (ScalarValidationProjection.scalarType_of_nativeType
    (nativeChecks fact member))).term

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
  have valuesMeaning := arguments_decoded_meaning invariant argumentsAccepted.1 (by
    simp only [jsonParsed]
    exact valuesDecoded)
  constructor
  · exact stateEq.symm
  · rw [← matched]
    simpa only [List.map_map, Function.comp_def] using valuesMeaning

/-- The source activity term for this row, using the producer's unguarded
default only when the whole activity schedule is empty. -/
def sourceImpactGuard (expected : Expected) (state : State) : Option Backend.Native.Term :=
  if expected.groupGuards.isEmpty then some (.constant 1)
  else expected.groupGuards[state.groupCount]?

private theorem accepted_impact_operands {expected : Expected}
    {state next : State} {raw : Json}
    (accepted : validateInstruction expected state raw = .ok next)
    (opcode : Backend.Native.stringField raw "op" = .ok "impact") :
    ∃ text guard facts,
      Backend.Native.stringField raw "guard" = .ok text ∧
      operand state text = .ok guard ∧
      (guard.valueType == NativeValueType.native) = true ∧ guard.maximum ≤ 1 ∧
      sourceImpactGuard expected state = some guard.term ∧
      arguments state raw "inputs" = .ok facts ∧
      (∀ fact, fact ∈ facts → (fact.valueType == NativeValueType.native) = true) ∧
      expected.groups[state.groupCount]? = some (facts.map (·.term)) ∧
      next = {state with groupCount := state.groupCount + 1} := by
  unfold validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨found, op, _, _, _, _, accepted⟩
  have same := Except.ok.inj (op.symm.trans opcode)
  subst found
  simp only [bind_ok] at accepted
  rcases accepted with ⟨_, _, text, textParsed, guard, guardParsed, booleanUnit, booleanChecked,
    facts, factsParsed, accepted⟩
  change (do
    let fact ← operand state text
    Backend.Native.ensure (fact.valueType == NativeValueType.native)
      "native instruction operand must have Native type"
    pure fact) = .ok guard at guardParsed
  rcases bind_ok.mp guardParsed with ⟨fact, factParsed, typed⟩
  rcases bind_ok.mp typed with ⟨_, nativeChecked, guardEq⟩
  have guardNative := ensure_ok.mp nativeChecked
  change Except.ok fact = Except.ok guard at guardEq
  cases guardEq
  cases booleanUnit
  have maximum : guard.maximum ≤ 1 := of_decide_eq_true (ensure_ok.mp booleanChecked)
  obtain ⟨argumentsAccepted, factsNative⟩ :=
    arguments_of_checked_native_arguments factsParsed
  refine ⟨text, guard, facts, textParsed, factParsed, guardNative, maximum, ?_⟩
  split at accepted
  next group groupParsed =>
    simp only [Pure.pure, Except.pure] at accepted
    cases empty : expected.groupGuards.isEmpty
    · cases scheduled : expected.groupGuards[state.groupCount]?
      · simp [empty, scheduled, Bind.bind, Except.bind, MonadExcept.throw] at accepted
      · simp [empty, scheduled, bind_ok] at accepted
        obtain ⟨⟨guardUnit, guardChecked⟩, ⟨payloadUnit, payloadChecked⟩, advanced⟩ :=
          accepted
        cases guardUnit
        cases payloadUnit
        rw [← eq_of_beq (ensure_ok.mp payloadChecked)] at groupParsed
        exact ⟨by simpa [sourceImpactGuard, empty, scheduled] using
          (eq_of_beq (ensure_ok.mp guardChecked)).symm,
          argumentsAccepted, factsNative, groupParsed, advanced.symm⟩
    · simp [empty, bind_ok] at accepted
      obtain ⟨⟨guardUnit, guardChecked⟩, ⟨payloadUnit, payloadChecked⟩, advanced⟩ :=
        accepted
      cases guardUnit
      cases payloadUnit
      rw [← eq_of_beq (ensure_ok.mp payloadChecked)] at groupParsed
      exact ⟨by simpa [sourceImpactGuard, empty] using
        (eq_of_beq (ensure_ok.mp guardChecked)).symm,
        argumentsAccepted, factsNative, groupParsed, advanced.symm⟩
  next => contradiction

/-- The strict decoder and accepted producer read the same ordered Impact
payload. Each selected source term has a scalar interpretation equal to its
corresponding decoded operand. -/
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
  obtain ⟨_, _, facts, _, _, _, _, selected, parsed, _, groupSelected, advanced⟩ :=
    accepted_impact_operands accepted opcode
  simp [NativeRelationJson.decodeInstruction, opcode, bind_ok,
    nativeJson_stringField_eq] at decoded
  rcases decoded with ⟨_, decodedGuard, _, decoded⟩
  cases decodedGuard <;> simp [bind_ok, map_ok] at decoded
  rcases decoded with ⟨_, json, jsonParsed, valuesDecoded, _⟩
  have valuesMeaning := arguments_decoded_meaning invariant parsed (by
    simp only [jsonParsed]
    exact valuesDecoded)
  exact ⟨facts.map (·.term), groupSelected, advanced,
    by simpa only [List.map_map, Function.comp_def] using valuesMeaning⟩

/-- The strict decoder and accepted producer read the same ordered Impact
guard and payload. Local Native checks provide scalar support for these
selected operands without requiring every state definition to be scalar. -/
theorem accepted_impact_guard_and_payload_projection
    {hash : Hash} {inputs witness : Assignment} {expected : Expected}
    {state next : State} {raw : Json} {guard : Operand} {values : List Operand}
    (invariant : ScalarValidationProjection.StateScalarProjection hash inputs witness state)
    (accepted : validateInstruction expected state raw = .ok next)
    (opcode : Backend.Native.stringField raw "op" = .ok "impact")
    (decodedGuard : NativeRelationJson.decodeOperandField raw "guard" = .ok guard)
    (decodedPayload : (do NativeRelationJson.decodeOperands (← raw.getObjVal? "inputs")) =
      .ok values) :
    ∃ guardTerm group, sourceImpactGuard expected state = some guardTerm ∧
      expected.groups[state.groupCount]? = some group ∧
      next = {state with groupCount := state.groupCount + 1} ∧
      interpret hash inputs guardTerm = some (guard.read witness) ∧
      (guard.read witness = zero ∨ guard.read witness = one) ∧
      group.map (interpret hash inputs) = (values.map (·.read witness)).map some := by
  obtain ⟨_, fact, facts, textParsed, parsed, guardNative, maximum, guardSelected,
    payloadParsed, payloadNative, groupSelected, advanced⟩ :=
    accepted_impact_operands accepted opcode
  unfold Backend.Native.stringField at textParsed
  unfold NativeRelationJson.decodeOperandField at decodedGuard
  obtain ⟨guardJson, jsonParsed, textAccepted⟩ := bind_ok.mp textParsed
  rw [jsonParsed] at decodedGuard
  change NativeRelationJson.decodeOperand guardJson = .ok guard at decodedGuard
  have guardAgreement := ScalarValidationProjection.operand_decoded_meaning
    ScalarParserAgreement.producer_immediate_success invariant textAccepted parsed decodedGuard
  have guardMeaning : ScalarValidationProjection.ScalarProjection hash inputs witness fact
      (guard.read witness) :=
    guardAgreement (ScalarValidationProjection.scalarType_of_nativeType guardNative)
  have bound := Nat.le_trans guardMeaning.bound maximum
  have boolean : (guard.read witness).val = 0 ∨ (guard.read witness).val = 1 := by omega
  have valuesMeaning := arguments_decoded_projection_meaning
    invariant payloadParsed payloadNative decodedPayload
  refine ⟨fact.term, facts.map (·.term), guardSelected, groupSelected,
    advanced, guardMeaning.term, ?_, ?_⟩
  · rcases boolean with inactive | active
    · exact Or.inl (Fin.ext inactive)
    · exact Or.inr (Fin.ext active)
  · simpa only [List.map_map, Function.comp_def] using valuesMeaning


/-- An accepted Impact row independently decoded from the emitted JSON has
the source-selected guard and payload under the same witness. The Boolean
fact comes from producer validation and the scalar meaning invariant. -/
theorem accepted_impact_guard_and_payload_meaning
    {hash : Hash} {inputs witness : Assignment} {expected : Expected}
    {state next : State} {raw : Json} {guard : Operand} {values : List Operand}
    (invariant : StateMeaning hash inputs witness state)
    (accepted : validateInstruction expected state raw = .ok next)
    (opcode : Backend.Native.stringField raw "op" = .ok "impact")
    (decodedGuard : NativeRelationJson.decodeOperandField raw "guard" = .ok guard)
    (decodedPayload : (do NativeRelationJson.decodeOperands (← raw.getObjVal? "inputs")) =
      .ok values) :
    ∃ guardTerm group, sourceImpactGuard expected state = some guardTerm ∧
      expected.groups[state.groupCount]? = some group ∧
      next = {state with groupCount := state.groupCount + 1} ∧
      interpret hash inputs guardTerm = some (guard.read witness) ∧
      (guard.read witness = zero ∨ guard.read witness = one) ∧
      group.map (interpret hash inputs) = (values.map (·.read witness)).map some := by
  have projected : ScalarValidationProjection.StateScalarProjection hash inputs witness state := by
    intro identifier fact member _
    have meaning := invariant identifier fact member
    exact ⟨meaning.term, meaning.bound, meaning.comparison⟩
  exact accepted_impact_guard_and_payload_projection projected accepted opcode
    decodedGuard decodedPayload


end Noctium.Verification.ScalarValidationOutputMeaning
