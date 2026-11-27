import Noctium.Verification.ArtifactBytes
import Noctium.Verification.GuardedScalarRows
import Noctium.Verification.NativeRelationJson
import Noctium.Verification.ScalarCallHeaderProjection
import Noctium.Backend.Zkir

namespace Noctium.Verification.GuardedZkirArtifact

open Lean
open Noctium.Backend
open Noctium.Verification.ArtifactBytes
open Noctium.Verification.GuardedScalarRows
open Noctium.Verification.NativeRelationJson

/-- The pinned scalar-call header fields which remain meaningful when the
guarded instruction stream is decoded separately. -/
structure Header where
  arguments : List String
  outputArity : Nat
  communicationsCommitment : Bool
  deriving DecidableEq

/-- The header and ordered guarded rows exposed by the checked artifact view. -/
structure View where
  header : Header
  rows : List GuardedScalarRows.Row
  deriving DecidableEq

private def decodeHeader (json : Json) : Except String Header := do
  let fields ← json.getObj?
  let call ← NativeRelationJson.decodeScalarCall
    (.obj (fields.insert "instructions" (.arr #[])))
  pure {
    arguments := call.arguments
    outputArity := call.body.outputArity
    communicationsCommitment := call.body.communicationsCommitment
  }

/-- Decode a JSON tree using the native scalar-call schema for its header and
the guarded row decoder for its ordered instruction stream. -/
def decodeView (json : Json) : Except String View := do
  let header ← decodeHeader json
  let instructions ← Backend.Native.arrayField json "instructions"
  let rows ← instructions.toList.mapM GuardedScalarRows.decodeRow
  pure { header, rows }

/-- Parse the exact public bytes, then decode their guarded scalar view. -/
def decodeBytes (bytes : ArtifactBytes.Bytes) : Except String View := do
  decodeView (← ArtifactBytes.parse bytes)

private def compareViews (actual pinned : View) :
    Except String (List GuardedScalarRows.Row) :=
  match decEq actual pinned with
  | .isTrue _ => .ok actual.rows
  | .isFalse _ => .error "guarded scalar artifact differs from pinned view"

/-- Accept bytes only when their complete guarded scalar view equals the
independently pinned JSON view. -/
def check (bytes : ArtifactBytes.Bytes) (expected : Lean.Json) :
    Except String (List GuardedScalarRows.Row) := do
  let actual ← decodeBytes bytes
  let pinned ← decodeView expected
  compareViews actual pinned

private theorem bind_ok {ε α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem decode_commitment_projection {json : Json}
    {program : NativeRelation.Program}
    (decoded : NativeRelationJson.decode json = .ok program) :
    (json.getObjVal? "do_communications_commitment" >>= Json.getBool?) =
      .ok program.communicationsCommitment := by
  unfold NativeRelationJson.decode at decoded
  simp only [bind_ok] at decoded
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, outputs, _, _, _,
      flagJSON, flagField, flag, flagDecoded, _, _, instructions, _, finished⟩ := decoded
  have programEq :
      (⟨instructions, outputs.size, flag⟩ : NativeRelation.Program) = program :=
    Except.ok.inj finished
  rw [← programEq]
  rw [flagField]
  exact flagDecoded

/-- A successful ledger lowering emits its commitment-enabled root object.
Producer validation returns the exact JSON built by the lowerer. -/
private theorem lowerEntrypoint_rootJson {state : List StateDecl}
    {entry : Entrypoint} {rewrites : Zkir.Rewrites} {json : Json}
    (lowered : Zkir.lowerEntrypoint state entry rewrites = .ok json) :
    ∃ version inputs outputs instructions : Json,
      json = Json.mkObj
        [("version", version), ("inputs", inputs), ("outputs", outputs),
         ("do_communications_commitment", toJson true), ("instructions", instructions)] := by
  simp only [Zkir.lowerEntrypoint, bind_ok] at lowered
  obtain ⟨⟨resultPlan, relation⟩, prunedAccepted, result⟩ := lowered
  cases result
  simp only [Zkir.lowerPrunedEntrypoint, bind_ok] at prunedAccepted
  rcases prunedAccepted with ⟨plan, planAccepted, gate⟩
  cases produced : (Zkir.lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {} with
  | mk value result =>
    simp only [produced] at gate
    simp only [bind_ok] at gate
    rcases gate with ⟨expected, expectedAccepted, _, producerAccepted, output⟩
    cases output
    obtain ⟨equal, _⟩ := (Zkir.validateProduced_ok _ _ _ _).mp producerAccepted
    subst relation
    refine ⟨_, _, _, _, rfl⟩

/-- Successful native decoding returns the commitment bit read from that
same JSON object. -/
private theorem decodeHeader_lowered_commitment {state : List StateDecl}
    {entry : Entrypoint} {rewrites : Zkir.Rewrites} {json : Json}
    {header : Header}
    (lowered : Zkir.lowerEntrypoint state entry rewrites = .ok json)
    (decoded : decodeHeader json = .ok header) :
    header.communicationsCommitment = true := by
  obtain ⟨version, rootInputs, outputs, instructions, jsonEq⟩ :=
    lowerEntrypoint_rootJson lowered
  let rootFields := Std.TreeMap.Raw.ofList
    [("version", version), ("inputs", rootInputs), ("outputs", outputs),
     ("do_communications_commitment", toJson true), ("instructions", instructions)] compare
  have modifiedFlag :
      (Json.obj ((rootFields.insert "instructions" (.arr #[])).insert "inputs" (.arr #[]))).getObjVal?
          "do_communications_commitment" = .ok (.bool true) := rfl
  unfold decodeHeader at decoded
  simp only [bind_ok] at decoded
  rcases decoded with ⟨fields, fieldsParsed, call, callParsed, result⟩
  have fieldsEq : fields = rootFields := by
    rw [jsonEq] at fieldsParsed
    change Except.ok rootFields = Except.ok fields at fieldsParsed
    exact (Except.ok.inj fieldsParsed).symm
  unfold NativeRelationJson.decodeScalarCall at callParsed
  simp only [bind_ok] at callParsed
  rcases callParsed with ⟨callFields, callFieldsParsed, arguments, argumentsParsed,
    body, bodyParsed, callResult⟩
  have callFieldsEq :
      callFields = fields.insert "instructions" (.arr #[]) := by
    change Except.ok (fields.insert "instructions" (.arr #[])) = Except.ok callFields
      at callFieldsParsed
    exact (Except.ok.inj callFieldsParsed).symm
  have bodyObjectEq :
      Json.obj (callFields.insert "inputs" (.arr #[])) =
        Json.obj ((rootFields.insert "instructions" (.arr #[])).insert "inputs" (.arr #[])) := by
    rw [callFieldsEq, fieldsEq]
  have bodyFlag := decode_commitment_projection bodyParsed
  rw [bodyObjectEq, modifiedFlag] at bodyFlag
  have bodyCommitted : body.communicationsCommitment = true := by
    simpa using Except.ok.inj bodyFlag
  have headerEq : header.communicationsCommitment = body.communicationsCommitment := by
    have scalarEqual :
        ({ arguments := arguments.2, body := body } : NativeRelationJson.ScalarCall) = call :=
      Except.ok.inj callResult
    have equal := Except.ok.inj result
    rw [← scalarEqual] at equal
    exact (congrArg Header.communicationsCommitment equal).symm
  rw [headerEq]
  exact bodyCommitted

private theorem compareViews_sound {actual pinned : View}
    {rows : List GuardedScalarRows.Row}
    (accepted : compareViews actual pinned = .ok rows) :
    actual = pinned ∧ actual.rows = rows := by
  unfold compareViews at accepted
  cases same : decEq actual pinned with
  | isTrue equal =>
    simp only [same, Except.ok.injEq] at accepted
    exact ⟨equal, accepted⟩
  | isFalse different =>
    simp only [same] at accepted
    cases accepted

/-- Successful JSON-view decoding exposes the exact ordered instruction rows. -/
private theorem decodeView_rows {json : Json} {view : View}
    (accepted : decodeView json = .ok view) :
    ∃ instructions,
      Backend.Native.arrayField json "instructions" = .ok instructions ∧
      instructions.toList.mapM GuardedScalarRows.decodeRow = .ok view.rows := by
  unfold decodeView at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨header, _, instructions, instructionsParsed, rows, rowsDecoded, result⟩
  have viewEq : ({ header := header, rows := rows } : View) = view := by
    simpa only [Pure.pure, Except.pure, Except.ok.injEq] using result
  cases viewEq
  exact ⟨instructions, instructionsParsed, rowsDecoded⟩

/-- An accepted artifact has the same guarded rows as its exact-byte view, and
the pinned JSON independently decodes to those same ordered rows. -/
theorem check_sound {bytes : ArtifactBytes.Bytes} {expected : Lean.Json}
    {rows : List GuardedScalarRows.Row} (accepted : check bytes expected = .ok rows) :
    (decodeBytes bytes).map View.rows = .ok rows ∧
      ∃ instructions,
        Backend.Native.arrayField expected "instructions" = .ok instructions ∧
        instructions.toList.mapM GuardedScalarRows.decodeRow = .ok rows := by
  unfold check at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨actual, actualDecoded, pinned, pinnedDecoded, result⟩
  obtain ⟨same, rowsEq⟩ := compareViews_sound result
  have exactBytes : (decodeBytes bytes).map View.rows = .ok rows := by
    calc
      (decodeBytes bytes).map View.rows =
          (Except.ok actual : Except String View).map View.rows :=
        congrArg (fun result : Except String View => result.map View.rows) actualDecoded
      _ = (Except.ok rows : Except String (List GuardedScalarRows.Row)) := by
        change Except.ok actual.rows = Except.ok rows
        exact congrArg Except.ok rowsEq
  obtain ⟨instructions, instructionsParsed, pinnedRows⟩ := decodeView_rows pinnedDecoded
  have pinnedRowsEq : pinned.rows = rows := by
    rw [← same]
    exact rowsEq
  exact ⟨exactBytes, instructions, instructionsParsed, pinnedRows.trans (congrArg Except.ok pinnedRowsEq)⟩

private theorem decodeView_header_accepted {json : Json} {view : View}
    (accepted : decodeView json = .ok view) :
    decodeHeader json = .ok view.header := by
  unfold decodeView at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨header, headerAccepted, instructions, instructionsAccepted,
    rows, rowsAccepted, result⟩
  have viewEq : ({ header := header, rows := rows } : View) = view :=
    Except.ok.inj result
  cases viewEq
  exact headerAccepted

/-- The guarded view carries the exact ordered raw inputs of the lowered
program. Stripping the body for header decoding preserves the input array. -/
theorem lowered_view_arguments {state : List StateDecl} {entry : Entrypoint}
    {rewrites : Zkir.Rewrites} {json : Json} {view : View}
    (lowered : Zkir.lowerEntrypoint state entry rewrites = .ok json)
    (decoded : decodeView json = .ok view) :
    ∃ rawInputs,
      Native.arrayField json "inputs" = .ok rawInputs ∧
      rawInputs.toList.mapM (fun item => Native.stringField item "name") =
        .ok view.header.arguments ∧
      view.header.arguments.all validIdentifier = true := by
  have header := decodeView_header_accepted decoded
  unfold decodeHeader at header
  simp only [bind_ok] at header
  obtain ⟨fields, fieldsParsed, call, callParsed, sameHeader⟩ := header
  have arguments : view.header.arguments = call.arguments :=
    congrArg Header.arguments (Except.ok.inj sameHeader).symm
  obtain ⟨rawInputs, names, inputField, namesParsed, namesEq⟩ :=
    ScalarCallHeaderProjection.decodeScalarCall_header_names callParsed
  obtain ⟨version, inputs, outputs, instructions, root⟩ := lowerEntrypoint_rootJson lowered
  rw [root] at fieldsParsed
  have wf : fields.WF := by
    cases fieldsParsed
    exact Std.TreeMap.Raw.WF.ofList
  have inputPreserved : Json.getObjVal? (.obj (fields.insert "instructions" (.arr #[]))) "inputs" =
      Json.getObjVal? (.obj fields) "inputs" := by
    simp only [Json.getObjVal?, Std.TreeMap.Raw.get?_eq_getElem?]
    rw [Std.TreeMap.Raw.getElem?_insert wf]
    have keyNe : compare "instructions" "inputs" ≠ .eq := by decide
    simp [keyNe]
  have arrayPreserved :
      Native.arrayField (.obj (fields.insert "instructions" (.arr #[]))) "inputs" =
        Native.arrayField json "inputs" := by
    unfold Native.arrayField
    rw [inputPreserved, root]
    cases fieldsParsed
    rfl
  refine ⟨rawInputs, arrayPreserved.symm.trans inputField, ?_, ?_⟩
  · simpa only [arguments, namesEq] using namesParsed
  · rw [arguments]
    exact List.all_eq_true.mpr
      (ScalarCallHeaderProjection.decodeScalarCall_argument_identifiers callParsed)

/-- The lowered guarded header uses the ordered raw names from the expected
source arguments. The native producer checks each header and its count. -/
theorem lowered_view_arguments_expected {state : List StateDecl} {entry : Entrypoint}
    {rewrites : Zkir.Rewrites} {json : Json} {view : View} {expected : Native.Expected}
    (lowered : Zkir.lowerEntrypoint state entry rewrites = .ok json)
    (decoded : decodeView json = .ok view)
    (accepted : Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected) :
    view.header.arguments = expected.rawInputs.map (·.identifier) := by
  obtain ⟨_, actual, _, actualAccepted, validated, _⟩ :=
    Zkir.lowerEntrypoint_validation_and_instructions_with_rewrites state entry rewrites json lowered
  have same := Except.ok.inj (actualAccepted.symm.trans accepted)
  subst actual
  obtain ⟨rawInputs, parsed, names, _⟩ := lowered_view_arguments lowered decoded
  obtain ⟨_, validatedInputs, _, _, driver⟩ := ScalarValidationProjection.validate_driver_result validated
  have sameInputs := Except.ok.inj (driver.rawInputsParsed.symm.trans parsed)
  subst validatedInputs
  have expectedNames := Native.seedRawInputs_header_names
    driver.seededRawInputs driver.rawInputCount
  have unchanged : (Zkir.optimizedExpected rewrites expected).rawInputs = expected.rawInputs := by
    cases rewrites <;> rfl
  rw [unchanged] at expectedNames
  exact Except.ok.inj (names.symm.trans expectedNames)

/-- An exact-byte guarded artifact accepted against an accepted ledger-call
lowering has the producer's enabled communications commitment in its header. -/
theorem check_lowerEntrypoint_header {state : List StateDecl} {entry : Entrypoint}
    {rewrites : Zkir.Rewrites} {bytes : ArtifactBytes.Bytes} {json : Lean.Json}
    {rows : List GuardedScalarRows.Row}
    (lowered : Zkir.lowerEntrypoint state entry rewrites = .ok json)
    (checked : check bytes json = .ok rows) :
    ∃ view, decodeBytes bytes = .ok view ∧ view.rows = rows ∧
      view.header.communicationsCommitment = true := by
  unfold check at checked
  simp only [bind_ok] at checked
  rcases checked with ⟨actual, actualAccepted, pinned, pinnedAccepted, compared⟩
  obtain ⟨viewsEqual, rowsEqual⟩ := compareViews_sound compared
  refine ⟨actual, actualAccepted, rowsEqual, ?_⟩
  rw [viewsEqual]
  exact decodeHeader_lowered_commitment lowered
    (decodeView_header_accepted pinnedAccepted)

end Noctium.Verification.GuardedZkirArtifact
