import Lean
import Noctium.Verification.NativeRelationJson

namespace Noctium.Verification.GuardedImpactObservation

open Lean
open Noctium.Verification.NativeRelation
open Noctium.Verification.NativeRelationJson

/-- A single observation emitted by pinned scalar Impact preprocessing. The
activity bit is kept even when every masked payload field is zero, so inactive
groups stay distinguishable from active groups carrying zero values. -/
structure Observation where
  active : Bool
  payload : List Scalar
  deriving Repr, DecidableEq

/-- Convert a scalar Impact guard into the pinned preprocessing observation.
Active groups retain their values. Inactive groups retain their field count
and emit zero for every payload field. Other scalar guards reject. This models
preprocessing observations only, not in-circuit constraints. -/
def observeImpact (guard : Scalar) (values : List Scalar) : Option Observation :=
  if guard = one then
    some ⟨true, values⟩
  else if guard = zero then
    some ⟨false, List.replicate values.length zero⟩
  else
    none

theorem observeImpact_active (values : List Scalar) :
    observeImpact one values = some ⟨true, values⟩ := by
  simp [observeImpact]

theorem observeImpact_inactive (values : List Scalar) :
    observeImpact zero values =
      some ⟨false, List.replicate values.length zero⟩ := by
  simp [observeImpact, zero_ne_one]

theorem observeImpact_rejects_nonboolean (guard : Scalar) (values : List Scalar)
    (notZero : guard ≠ zero) (notOne : guard ≠ one) :
    observeImpact guard values = none := by
  simp [observeImpact, notOne, notZero]

/-- A successful row observation preserves the input payload width. -/
theorem observeImpact_preserves_width (guard : Scalar) (values : List Scalar)
    (observation : Observation)
    (accepted : observeImpact guard values = some observation) :
    observation.payload.length = values.length := by
  by_cases active : guard = one
  · simp [observeImpact, active] at accepted
    cases accepted
    rfl
  · by_cases inactive : guard = zero
    · simp [observeImpact, inactive] at accepted
      cases accepted
      simp
    · simp [observeImpact, active, inactive] at accepted

/-- Ordered Impact rows either all decode to observations or reject on the
first non-Boolean activity guard. -/
def observeRows : List (Scalar × List Scalar) → Option (List Observation)
  | [] => some []
  | (guard, values) :: rows =>
    match observeImpact guard values with
    | none => none
    | some head =>
      match observeRows rows with
      | none => none
      | some tail => some (head :: tail)

theorem observeRows_cons (row : Scalar × List Scalar) (rows : List (Scalar × List Scalar)) :
    observeRows (row :: rows) =
      match observeImpact row.1 row.2, observeRows rows with
      | some head, some tail => some (head :: tail)
      | _, _ => none := by
  cases row with
  | mk guard values =>
    cases observed : observeImpact guard values <;>
      cases tail : observeRows rows <;> simp [observeRows, observed, tail]

/-- Successful observation preserves the number and order of static groups. -/
theorem observeRows_preserves_group_count (rows : List (Scalar × List Scalar))
    (observations : List Observation)
    (accepted : observeRows rows = some observations) :
    observations.length = rows.length := by
  induction rows generalizing observations with
  | nil =>
    simp [observeRows] at accepted
    cases accepted
    rfl
  | cons row rows ih =>
    rw [observeRows_cons] at accepted
    cases head : observeImpact row.1 row.2 with
    | none => simp [head] at accepted
    | some observation =>
      cases tail : observeRows rows with
      | none => simp [head, tail] at accepted
      | some tailObservations =>
        have same : observations = observation :: tailObservations := by
          simpa [observeRows, head, tail] using accepted.symm
        subst observations
        have tailCount := ih tailObservations tail
        simp [tailCount]

/-- This concrete mixed schedule preserves row order and width while masking
only the inactive row's payload. -/
theorem observeRows_ordered_example (a b c d : Scalar) :
    observeRows [(one, [a, b]), (zero, [c]), (one, [d])] =
      some [⟨true, [a, b]⟩, ⟨false, [zero]⟩, ⟨true, [d]⟩] := by
  simp [observeRows, observeImpact, zero_ne_one]

/-- The existing strict parser accepts the producer's literal-one Impact row.
Dynamic guards remain outside its current decoder profile. -/
private def literalImpactRow : Json := Json.mkObj [
  ("op", toJson ("impact" : String)),
  ("guard", toJson ("0x01" : String)),
  ("inputs", toJson (["%left", "%right"] : List String))]

#guard match NativeRelationJson.decodeInstruction literalImpactRow with
  | .ok (.impact (.immediate guard) [.reference "%left", .reference "%right"]) => guard == one
  | _ => false

end Noctium.Verification.GuardedImpactObservation
