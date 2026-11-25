import Noctium.Verification.ArtifactBytes
import Noctium.Verification.GuardedScalarRows
import Noctium.Verification.NativeRelationJson

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

private theorem bind_ok {α β : Type} {first : Except String α}
    {next : α → Except String β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

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

end Noctium.Verification.GuardedZkirArtifact
