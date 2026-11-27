import Noctium.Verification.GuardedScalarRows
import Noctium.Verification.NativeInputOrdinal

namespace Noctium.Verification.GuardedPublicInputMeaning

open Lean Backend.Native NativeRelation NativeRelationJson
open Noctium.Verification.GuardedScalarRows
open Noctium.Verification.NativeInputOrdinal
open Noctium.Verification.ScalarValidationMeaning
open Noctium.Verification.ScalarNormalization

private theorem bind_ok {α β : Type} {first : Except String α}
    {next : α → Except String β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

/-- The source-selected activity guard, with the producer's active default
when no guard was attached to the input requirement. -/
def sourceReadGuard (hash : Hash) (inputs : Assignment)
    (requirement : InputRequirement) : Option Scalar :=
  (requirement.activityGuard.map (interpret hash inputs)).getD (some one)

private theorem accepted_unguarded_public_input_guard_null {expected : Expected}
    {state next : State} {raw : Json} {requirement : InputRequirement}
    (selected : expected.inputs[state.inputCount]? = some requirement)
    (nonforeignInput : requirement.ty.isForeign = false)
    (unguarded : requirement.activityGuard = none)
    (opcodeParsed : Backend.Native.stringField raw "op" = .ok "public_input")
    (accepted : validateInstruction expected state raw = .ok next) :
    raw.getObjVal? "guard" = .ok Json.null := by
  unfold validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨opcode, op, descriptor, registry, _, fields, accepted⟩
  have opcodeEq : opcode = "public_input" := Except.ok.inj (op.symm.trans opcodeParsed)
  subst opcode
  simp only [selected, unguarded] at accepted
  cases ty : requirement.ty <;> try simp [Ty.isForeign, ty] at nonforeignInput
  all_goals
    simp only [ty] at accepted
    simp only [bind_ok] at accepted
    rcases accepted with ⟨typeJson, typeParsed, nativeTypeValue, nativeTypeParsed,
      valueType, valueParsed, guardJson, guardParsed, guardUnit, guardChecked,
      output, outputParsed, schemaUnit, schemaChecked, definedState, defined, result⟩
    have guardNull : guardJson.isNull = true := by
      cases guardUnit
      cases isNull : guardJson.isNull with
      | false =>
        simp [Backend.Native.ensure, isNull, throw, throwThe] at guardChecked
      | true => rfl
    cases guardJson <;> simp_all [Json.isNull]

private theorem decodeOperandField_null_impossible {raw : Json} {operand : Operand}
    (guardNull : raw.getObjVal? "guard" = .ok Json.null)
    (decoded : NativeRelationJson.decodeOperandField raw "guard" = .ok operand) :
    False := by
  unfold NativeRelationJson.decodeOperandField at decoded
  rw [guardNull] at decoded
  simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Json.getStr?,
    NativeRelationJson.decodeOperand, NativeRelationJson.decodeImmediate] at decoded

/-- Relate one accepted independently decoded public input row to the live
producer requirement. Missing source guards select the active scalar default.
Present source guards match the decoded Native operand and pass the producer's
Boolean check. -/
theorem accepted_publicInput_meaning
    {hash : Hash} {inputs witness : Assignment} {expected : Expected}
    {state next : State} {raw : Json} {output : String} {guard : Option Operand}
    (invariant : StateMeaning hash inputs witness state)
    (inputSchema : ∀ requirement ∈ expected.inputs,
      requirement.ty.isForeign = false)
    (decoded : decodeRow raw = .ok (.publicInput output guard))
    (accepted : validateInstruction expected state raw = .ok next) :
    ∃ requirement,
      expected.inputs[state.inputCount]? = some requirement ∧
      requirement.visibility = .«public» ∧
      output = requirement.identifier ∧
      sourceReadGuard hash inputs requirement =
        some ((guard.map (Operand.read witness)).getD one) ∧
      (((guard.map (Operand.read witness)).getD one = zero) ∨
        ((guard.map (Operand.read witness)).getD one = one)) := by
  have fields := decodeRow_publicInput_fields decoded
  obtain ⟨requirement, selected⟩ := ScalarValidationNativeLoop.accepted_input_requirement_selected
    (visibility := .«public»)
    fields.1 accepted
  have member : requirement ∈ expected.inputs := List.mem_of_getElem? selected
  have nonforeignInput := inputSchema requirement member
  obtain ⟨outputParsed, visibility⟩ := accepted_input_output_descriptor
    (visibility := .«public»)
    selected nonforeignInput fields.1 accepted
  have outputEq : output = requirement.identifier :=
    Except.ok.inj (fields.2.1.symm.trans outputParsed)
  cases activity : requirement.activityGuard with
  | none =>
    have guardNull := accepted_unguarded_public_input_guard_null
      selected nonforeignInput activity fields.1 accepted
    have guardNone : guard = none := by
      cases guard with
      | none => rfl
      | some operand =>
        have decodedGuard := fields.2.2.2 operand rfl
        exact False.elim (decodeOperandField_null_impossible guardNull decodedGuard)
    refine ⟨requirement, selected, ?_, outputEq, ?_, ?_⟩
    · simp [visibility]
    · simp [sourceReadGuard, activity, guardNone]
    · simp [guardNone]
  | some guardTerm =>
    have guardSome : ∃ operand, guard = some operand := by
      cases guard with
      | none =>
        obtain ⟨guardText, textParsed⟩ := accepted_guarded_public_input_guard_string
          selected nonforeignInput activity fields.1 accepted
        have guardNull := fields.2.2.1 rfl
        unfold Backend.Native.stringField at textParsed
        rcases bind_ok.mp textParsed with ⟨json, fieldParsed, stringParsed⟩
        have jsonEq : json = Json.null := Except.ok.inj (fieldParsed.symm.trans guardNull)
        subst json
        cases stringParsed
      | some operand => exact ⟨operand, rfl⟩
    obtain ⟨operand, guardEq⟩ := guardSome
    subst guard
    have decodedGuard := fields.2.2.2 operand rfl
    obtain ⟨meaning, boolean⟩ := accepted_guarded_public_input_guard_meaning
      invariant selected nonforeignInput activity fields.1 accepted decodedGuard
    refine ⟨requirement, selected, ?_, outputEq, ?_, ?_⟩
    · simp [visibility]
    · simp [sourceReadGuard, activity, meaning]
    · simpa using boolean

/-- Inverting one accepted public input exposes the exact input fact inserted
by the producer and the intermediate definition state. -/
private theorem accepted_publicInput_definition
    {expected : Expected} {state next : State} {raw : Json}
    {requirement : InputRequirement} {output : String}
    (selected : expected.inputs[state.inputCount]? = some requirement)
    (nonforeignInput : requirement.ty.isForeign = false)
    (opcodeParsed : Backend.Native.stringField raw "op" = .ok "public_input")
    (accepted : validateInstruction expected state raw = .ok next)
    (outputParsed : Backend.Native.stringField raw "output" = .ok output) :
    ∃ definedState,
      define state output
        ({term := .input output, maximum := Field.modulus - 1} : Fact) = .ok definedState ∧
      next.definitions = definedState.definitions := by
  unfold validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨opcode, op, descriptor, registry, _, fields, accepted⟩
  have opcodeEq : opcode = "public_input" := Except.ok.inj (op.symm.trans opcodeParsed)
  subst opcode
  cases activity : requirement.activityGuard with
  | none =>
    simp only [selected, activity] at accepted
    cases ty : requirement.ty <;> try simp [Ty.isForeign, ty] at nonforeignInput
    all_goals
      simp only [ty] at accepted
      simp only [bind_ok] at accepted
      rcases accepted with ⟨typeJson, typeParsed, _, _, valueType, valueParsed,
        guardJson, guardParsed, _, _, outputName, outputNameParsed, _, schema,
        definedState, defined, result⟩
      cases valueParsed
      have sameOutput : outputName = output :=
        Except.ok.inj (outputNameParsed.symm.trans outputParsed)
      subst outputName
      have nextEq := Except.ok.inj result
      exact ⟨definedState, defined, (congrArg State.definitions nextEq).symm⟩
  | some guardTerm =>
    simp only [selected, activity] at accepted
    cases ty : requirement.ty <;> try simp [Ty.isForeign, ty] at nonforeignInput
    all_goals
      simp only [ty] at accepted
      simp only [bind_ok] at accepted
      rcases accepted with ⟨typeJson, typeParsed, _, _, valueType, valueParsed,
        guardModeUnit, guardModeChecked, guardText, guardTextParsed, guardFact,
        guardOperand, guardBoolean, guardBooleanChecked, guardMatchUnit, guardMatch,
        outputName, outputNameParsed, _, schema, definedState, defined, result⟩
      cases valueParsed
      have sameOutput : outputName = output :=
        Except.ok.inj (outputNameParsed.symm.trans outputParsed)
      subst outputName
      have nextEq := Except.ok.inj result
      exact ⟨definedState, defined, (congrArg State.definitions nextEq).symm⟩

/-- An accepted decoded public input has its guard references in the producer
pre-state, defines a fresh output, and appends exactly its native input fact. -/
theorem accepted_publicInput_ssa_footprint
    {expected : Expected} {state next : State} {raw : Json}
    {output : String} {guard : Option Operand}
    (inputSchema : ∀ requirement ∈ expected.inputs,
      requirement.ty.isForeign = false)
    (decoded : decodeRow raw = .ok (.publicInput output guard))
    (accepted : validateInstruction expected state raw = .ok next) :
    (∀ name ∈ guard.toList.flatMap ScalarWitness.operandIdentifiers,
      ∃ fact, state.definitions.lookup name = some fact) ∧
    state.definitions.lookup output = none ∧
    next.definitions = state.definitions ++
      [(output, ({term := .input output, maximum := Field.modulus - 1} : Fact))] := by
  have fields := decodeRow_publicInput_fields decoded
  obtain ⟨requirement, selected⟩ := ScalarValidationNativeLoop.accepted_input_requirement_selected
    (visibility := .«public») fields.1 accepted
  have member : requirement ∈ expected.inputs := List.mem_of_getElem? selected
  have nonforeignInput := inputSchema requirement member
  obtain ⟨outputParsed, visibility⟩ := accepted_input_output_descriptor
    (visibility := .«public») selected nonforeignInput
    (by simpa [ScalarValidationNativeLoop.inputOpcode] using fields.1) accepted
  have outputEq : output = requirement.identifier :=
    Except.ok.inj (fields.2.1.symm.trans outputParsed)
  have outputParsedForRow : Backend.Native.stringField raw "output" = .ok output := by
    rw [outputEq]
    exact outputParsed
  have defined := accepted_publicInput_definition selected nonforeignInput fields.1 accepted
    outputParsedForRow
  obtain ⟨definedState, insertion, nextDefinitions⟩ := defined
  have insertionFacts := define_appended_and_missing insertion
  have outputAbsent : state.definitions.lookup output = none := insertionFacts.2
  have appendFacts := insertionFacts.1
  constructor
  · intro name used
    cases guard with
    | none => simp at used
    | some operand =>
      cases activity : requirement.activityGuard with
      | none =>
        have guardNull := accepted_unguarded_public_input_guard_null selected
          nonforeignInput activity fields.1 accepted
        exact False.elim (decodeOperandField_null_impossible guardNull
          (fields.2.2.2 operand rfl))
      | some guardTerm =>
        obtain ⟨guardText, guardFact, guardString, operandAccepted, _, _, _⟩ :=
          accepted_guarded_public_input_guard_fact selected nonforeignInput activity
            fields.1 accepted
        have decodedGuard := fields.2.2.2 operand rfl
        unfold NativeRelationJson.decodeOperandField at decodedGuard
        rcases bind_ok.mp decodedGuard with ⟨guardJson, jsonParsed, decodedOperand⟩
        unfold Backend.Native.stringField at guardString
        rcases bind_ok.mp guardString with ⟨sameJson, guardJsonParsed, textParsed⟩
        have sameJsonEq : sameJson = guardJson := Except.ok.inj
          (guardJsonParsed.symm.trans jsonParsed)
        subst sameJson
        cases operand with
        | immediate value => simp [ScalarWitness.operandIdentifiers] at used
        | reference reference =>
          have sameName : name = reference := by
            simpa [ScalarWitness.operandIdentifiers] using used
          subst name
          exact ⟨guardFact, operand_decoded_reference_lookup textParsed
            operandAccepted decodedOperand⟩
  · constructor
    · exact outputAbsent
    · rw [nextDefinitions, appendFacts]

end Noctium.Verification.GuardedPublicInputMeaning
