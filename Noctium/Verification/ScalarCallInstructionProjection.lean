import Noctium.Verification.NativeRelationInstructionProjection

namespace Noctium.Verification.ScalarCallInstructionProjection

open Lean Backend NativeRelation NativeRelationJson

private theorem bind_ok {ε α β} {value : Except ε α} {next : α → Except ε β}
    {result : β} : (value >>= next) = .ok result ↔
      ∃ found, value = .ok found ∧ next found = .ok result := by
  cases value <;> simp [Bind.bind, Except.bind]

private theorem arrayField_insert_inputs (fields : Std.TreeMap.Raw String Json compare)
    (wellFormed : fields.WF) :
    Native.arrayField (.obj (fields.insert "inputs" (.arr #[]))) "instructions" =
      Native.arrayField (.obj fields) "instructions" := by
  have lookup :
      Json.getObjVal? (.obj (fields.insert "inputs" (.arr #[]))) "instructions" =
        Json.getObjVal? (.obj fields) "instructions" := by
    simp only [Json.getObjVal?]
    simp only [Std.TreeMap.Raw.get?_eq_getElem?]
    rw [Std.TreeMap.Raw.getElem?_insert wellFormed]
    have keyNe : compare "inputs" "instructions" ≠ .eq := by decide
    simp [keyNe]
  unfold Native.arrayField
  rw [lookup]

/-- The scalar-call body parses the same raw instruction rows as the original
native call object, provided its raw object map is well formed. -/
theorem decodeScalarCall_instructionProjection_of_wf {json : Json} {call : ScalarCall}
    (decoded : decodeScalarCall json = .ok call)
    (fields : Std.TreeMap.Raw String Json compare)
    (fieldsParsed : json.getObj? = .ok fields)
    (wellFormed : fields.WF) :
    ∃ instructions : Array Json,
      Native.arrayField json "instructions" = .ok instructions ∧
      instructions.toList.mapM decodeInstruction = .ok call.body.instructions := by
  unfold decodeScalarCall at decoded
  simp only [bind_ok] at decoded
  rcases decoded with ⟨parsedFields, fieldsAccepted, header, headerAccepted,
    body, bodyAccepted, result⟩
  have fieldsEq : parsedFields = fields := Except.ok.inj (fieldsAccepted.symm.trans fieldsParsed)
  subst parsedFields
  have callEq : ({arguments := header.2, body} : ScalarCall) = call := Except.ok.inj result
  cases callEq
  obtain ⟨bodyInstructions, bodyArrayParsed, bodyRowsDecoded⟩ :=
    NativeRelationInstructionProjection.decode_instructionProjection bodyAccepted
  have jsonEq : json = .obj fields := by
    cases json with
    | obj parsed =>
      simp only [Json.getObj?] at fieldsParsed
      cases fieldsParsed
      rfl
    | null => simp [Json.getObj?] at fieldsParsed
    | bool value => simp [Json.getObj?] at fieldsParsed
    | num value => simp [Json.getObj?] at fieldsParsed
    | str value => simp [Json.getObj?] at fieldsParsed
    | arr values => simp [Json.getObj?] at fieldsParsed
  have originalArrayParsed : Native.arrayField json "instructions" = .ok bodyInstructions := by
    rw [jsonEq]
    rw [← arrayField_insert_inputs fields wellFormed]
    exact bodyArrayParsed
  exact ⟨bodyInstructions, originalArrayParsed, bodyRowsDecoded⟩

private theorem mkObj_root_fields_wf {items : List (String × Json)} :
    ∃ fields : Std.TreeMap.Raw String Json compare,
      (Json.mkObj items).getObj? = .ok fields ∧ fields.WF := by
  refine ⟨Std.TreeMap.Raw.ofList items compare, rfl, ?_⟩
  exact Std.TreeMap.Raw.WF.ofList

theorem lowerEntrypoint_root_fields_wf {state : List StateDecl} {entry : Entrypoint}
    (rewrites : Zkir.Rewrites) {json : Json}
    (lowered : Zkir.lowerEntrypoint state entry rewrites = .ok json) :
    ∃ fields : Std.TreeMap.Raw String Json compare,
      json.getObj? = .ok fields ∧ fields.WF := by
  unfold Zkir.lowerEntrypoint at lowered
  simp only [bind_ok] at lowered
  rcases lowered with ⟨found, prunedAccepted, resultEq⟩
  have resultEq' : found.2 = json := Except.ok.inj resultEq
  subst json
  unfold Zkir.lowerPrunedEntrypoint at prunedAccepted
  simp only [bind_ok] at prunedAccepted
  rcases prunedAccepted with ⟨plan, planAccepted, gate⟩
  cases produced : (Zkir.lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {} with
  | mk value bodyState =>
    simp only [produced] at gate
    simp only [bind_ok] at gate
    rcases gate with ⟨expected, expectedAccepted, relation, relationAccepted, resultEq⟩
    have pairEq : (plan, relation) = found := Except.ok.inj resultEq
    cases pairEq
    obtain ⟨relationEq, _⟩ := (Zkir.validateProduced_ok _ _ _ _).mp relationAccepted
    rw [relationEq]
    exact mkObj_root_fields_wf

/-- Bind a decoded scalar call body to the exact rows validated and emitted by
the compiler for its native entrypoint artifact. -/
theorem lowerEntrypoint_decodeScalarCall_instructionProjection
    {state : List StateDecl} {entry : Entrypoint} {json : Json} {call : ScalarCall}
    (lowered : Zkir.lowerEntrypoint state entry = .ok json)
    (decoded : decodeScalarCall json = .ok call) :
    ∃ plan expected instructions,
      Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected ∧
      Native.validate expected json = .ok () ∧
      Native.arrayField json "instructions" = .ok instructions ∧
      instructions =
        ((Zkir.lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {}).2.instructions ∧
      instructions.toList.mapM decodeInstruction = .ok call.body.instructions := by
  obtain ⟨plan, expected, impactAccepted, scheduleAccepted, validated, bodyArray⟩ :=
    Zkir.lowerEntrypoint_validation_and_instructions state entry json lowered
  obtain ⟨fields, fieldsParsed, fieldsWF⟩ := lowerEntrypoint_root_fields_wf .disabled lowered
  obtain ⟨instructions, parsed, rowsDecoded⟩ :=
    decodeScalarCall_instructionProjection_of_wf decoded fields fieldsParsed fieldsWF
  have exactBodyInstructions :
      instructions =
        ((Zkir.lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {}).2.instructions :=
    Except.ok.inj (parsed.symm.trans bodyArray)
  exact ⟨plan, expected, instructions, impactAccepted, scheduleAccepted, validated,
    parsed, exactBodyInstructions, rowsDecoded⟩

end Noctium.Verification.ScalarCallInstructionProjection
