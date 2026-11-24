import Noctium.Verification.ScalarValidationOutputMeaning

namespace Noctium.Verification.GuardedImpactObservation

open Lean
open Backend.Native
open Noctium.Verification.NativeRelation
open Noctium.Verification.NativeRelationJson
open ScalarNormalization ScalarValidationMeaning ScalarValidationOutputMeaning

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

def sourceObservation (hash : Hash) (inputs : Assignment) (guard : Backend.Native.Term)
    (group : List Backend.Native.Term) : Option Observation := do
  let active ← interpret hash inputs guard
  let values ← group.mapM (interpret hash inputs)
  observeImpact active values

private theorem mapM_of_values (f : α → Option β)
    {terms : List α} {values : List β} (matched : terms.map f = values.map some) :
    terms.mapM f = some values := by
  induction terms generalizing values with
  | nil => cases values <;> simp_all
  | cons head tail ih =>
    cases values with
    | nil => simp at matched
    | cons value rest =>
      simp only [List.map_cons, List.cons.injEq] at matched
      simp [List.mapM_cons, matched.1, ih matched.2]

/-- With scalar meaning at the accepted row pre-state, independent raw operand
decoding produces the same activity and ordered public payload as the
source-selected terms. An inactive group keeps its width and contributes
zeros. This relates one row to the preprocessing model. -/
theorem accepted_impact_observation
    {hash : Hash} {inputs witness : Assignment} {expected : Expected}
    {state next : State} {raw : Json} {guard : Operand} {values : List Operand}
    (invariant : StateMeaning hash inputs witness state)
    (accepted : validateInstruction expected state raw = .ok next)
    (opcode : Backend.Native.stringField raw "op" = .ok "impact")
    (decodedGuard : decodeOperandField raw "guard" = .ok guard)
    (decodedPayload : (do decodeOperands (← raw.getObjVal? "inputs")) = .ok values) :
    ∃ guardTerm group observation, sourceImpactGuard expected state = some guardTerm ∧
      expected.groups[state.groupCount]? = some group ∧
      next = {state with groupCount := state.groupCount + 1} ∧
      sourceObservation hash inputs guardTerm group = some observation ∧
      observeImpact (guard.read witness) (values.map (·.read witness)) = some observation ∧
      observation.payload.length = group.length := by
  obtain ⟨guardTerm, group, guardSelected, groupSelected, advanced, guardMeaning, boolean,
      payloadMeaning⟩ :=
    accepted_impact_guard_and_payload_meaning invariant accepted opcode decodedGuard decodedPayload
  have evaluated := mapM_of_values _ payloadMeaning
  have width : group.length = values.length := by
    simpa using congrArg List.length payloadMeaning
  have sourceExact :
      sourceObservation hash inputs guardTerm group =
        observeImpact (guard.read witness) (values.map (·.read witness)) := by
    simp [sourceObservation, guardMeaning, evaluated]
  rcases boolean with inactive | active
  · refine ⟨guardTerm, group, ⟨false, List.replicate values.length zero⟩,
      guardSelected, groupSelected, advanced, ?_, ?_, by simp [width]⟩
    all_goals simp [sourceExact, inactive, observeImpact_inactive]
  · refine ⟨guardTerm, group, ⟨true, values.map (·.read witness)⟩,
      guardSelected, groupSelected, advanced, ?_, ?_, by simp [width]⟩
    all_goals simp [sourceExact, active, observeImpact_active]

end Noctium.Verification.GuardedImpactObservation
