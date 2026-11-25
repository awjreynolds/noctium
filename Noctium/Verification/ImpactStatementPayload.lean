import Noctium.Verification.NativeRelation
import Noctium.Verification.ImpactNoopPreview

namespace Noctium.Verification.ImpactStatementPayload

open ImpactNoopPreview NativeRelation

/-- The public field contribution of one preview entry. Active operations use
their native field encoder. A skipped Noop contributes its advertised zero
fields, matching Rust's `FieldRepr` implementation. -/
def entryFields (encode : α → List Scalar) : PreviewEntry α → List Scalar
  | .active operation => encode operation
  | .noop count => List.replicate count zero

/-- The ordered public scalar stream of a previewed transcript. -/
def payload (encode : α → List Scalar) (entries : List (PreviewEntry α)) : List Scalar :=
  match entries with
  | [] => []
  | entry :: rest => entryFields encode entry ++ payload encode rest

/-- Count public fields without constructing any Noop zero list. -/
def payloadWidth (encode : α → List Scalar) : List (PreviewEntry α) → Nat
  | [] => 0
  | .active operation :: rest => (encode operation).length + payloadWidth encode rest
  | .noop count :: rest => count + payloadWidth encode rest

/-- Build public fields directly from a source program and its activity
schedule. Each active slot consumes the next operation. A skipped slot emits
the requested number of zero fields. -/
def scheduledPayload (encode : α → List Scalar) :
    List α → List (Option Nat) → Option (List Scalar)
  | [], [] => some []
  | _ :: _, [] => none
  | program, some count :: activity =>
      (scheduledPayload encode program activity).map
        (List.replicate count zero ++ ·)
  | operation :: program, none :: activity =>
      (scheduledPayload encode program activity).map (encode operation ++ ·)
  | [], none :: _ => none

theorem payload_length_eq_payloadWidth (encode : α → List Scalar)
    (entries : List (PreviewEntry α)) :
    (payload encode entries).length = payloadWidth encode entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      cases entry with
      | active operation =>
          simp [payload, payloadWidth, entryFields, ih]
      | noop count =>
          simp [payload, payloadWidth, entryFields, ih]

private theorem replicate_add (left right : Nat) (value : Scalar) :
    List.replicate (left + right) value =
      List.replicate left value ++ List.replicate right value := by
  induction left with
  | zero => simp
  | succ left ih =>
      simp only [Nat.succ_add, List.replicate]
      rw [ih]
      rfl

private theorem coalesceNoop_head_payload (encode : α → List Scalar) (count : Nat)
    (rest : List (PreviewEntry α)) :
    payload encode (coalesceNoops (.noop count :: rest)) =
      List.replicate count zero ++ payload encode (coalesceNoops rest) := by
  cases count with
  | zero => rfl
  | succ count =>
      cases tail : coalesceNoops rest with
      | nil =>
          simp only [coalesceNoops, tail]
          rfl
      | cons head tailEntries =>
          cases head with
          | active operation =>
              simp only [coalesceNoops, tail]
              rfl
          | noop next =>
              simp only [coalesceNoops, tail]
              change List.replicate (Nat.succ count + next) zero ++
                  payload encode tailEntries =
                List.replicate (Nat.succ count) zero ++
                  (List.replicate next zero ++ payload encode tailEntries)
              rw [replicate_add]
              rw [List.append_assoc]

/-- Pairing a preview entry list with its represented activity and active
program produces the same ordered scalar fields as `payload`. -/
theorem scheduledPayload_rawActivity (encode : α → List Scalar)
    (entries : List (PreviewEntry α)) :
    scheduledPayload encode (activeProjection entries) (rawActivity entries) =
      some (payload encode entries) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      cases entry with
      | active operation =>
          simp [scheduledPayload, activeProjection, rawActivity, payload, entryFields, ih]
      | noop count =>
          simp [scheduledPayload, activeProjection, rawActivity, payload, entryFields, ih]

/-- Coalescing adjacent Noop entries preserves every public scalar, including
the position of each active operation's encoded fields. -/
theorem coalesceNoops_preserves_payload (encode : α → List Scalar)
    (entries : List (PreviewEntry α)) :
    payload encode (coalesceNoops entries) = payload encode entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      cases entry with
      | active operation =>
          simp [payload, coalesceNoops, ih]
      | noop count =>
          calc
            payload encode (coalesceNoops (.noop count :: rest)) =
                List.replicate count zero ++ payload encode (coalesceNoops rest) :=
              coalesceNoop_head_payload encode count rest
            _ = List.replicate count zero ++ payload encode rest := by rw [ih]
            _ = payload encode (.noop count :: rest) := rfl

/-- Coalescing also preserves the directly computed public field width. -/
theorem coalesceNoops_preserves_payloadWidth (encode : α → List Scalar)
    (entries : List (PreviewEntry α)) :
    payloadWidth encode (coalesceNoops entries) = payloadWidth encode entries := by
  calc
    payloadWidth encode (coalesceNoops entries) =
        (payload encode (coalesceNoops entries)).length :=
      (payload_length_eq_payloadWidth encode _).symm
    _ = (payload encode entries).length :=
      congrArg List.length (coalesceNoops_preserves_payload encode entries)
    _ = payloadWidth encode entries := payload_length_eq_payloadWidth encode entries

/-- A successful transcript preview emits exactly the source program's
scheduled public fields, with adjacent Noops coalesced without changing them. -/
theorem payload_of_previewProgram (encode : α → List Scalar)
    {program : List α} {activity : List (Option Nat)}
    {entries : List (PreviewEntry α)}
    (previewed : previewProgram program activity = some entries) :
    scheduledPayload encode program activity = some (payload encode entries) := by
  obtain ⟨expanded, entriesEq, activeEq, activityEq⟩ :=
    ImpactNoopPreview.previewProgram_expansion previewed
  rw [← activeEq, ← activityEq, scheduledPayload_rawActivity, entriesEq,
    ← coalesceNoops_preserves_payload]

end Noctium.Verification.ImpactStatementPayload
