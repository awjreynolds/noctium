import Noctium.Verification.ScalarValidationOutputMeaning
import Noctium.Verification.ScalarValidationProjection

namespace Noctium.Verification.GuardedImpactProjectionFixture

open Lean Backend.Native NativeRelation NativeRelationJson ScalarNormalization
  ScalarValidationProjection

private def hash : Hash := fun _ => zero
private def inputs : Assignment := fun _ => zero
private def witness (name : String) : Scalar :=
  if name == "%guard" then one else zero

private def guardFact : Fact := { term := .constant 1, maximum := 1 }
private def byteFact : Fact := {
  term := .bytes [.constant 9]
  maximum := 0
  valueType := .bytes 1
}

private def state : State := {
  definitions := [("%guard", guardFact), ("%bytes", byteFact)]
}

example : interpret hash inputs byteFact.term = none := by
  change ScalarTermMeaning.interpret? hash inputs (.bytes [.constant 9]) = none
  simp

private def expected : Expected := {
  mode := .relation
  inputs := []
  groups := [[.constant 2, .constant 3]]
  groupGuards := [.constant 1]
  returns := []
  assertions := []
  bounds := []
}

private def impactRow : Json := Json.mkObj [
  ("op", toJson ("impact" : String)),
  ("guard", toJson ("%guard" : String)),
  ("inputs", toJson (["0x02", "0x03"] : List String))]

private def bytePayloadRow : Json := Json.mkObj [
  ("op", toJson ("impact" : String)),
  ("guard", toJson ("%guard" : String)),
  ("inputs", toJson (["%bytes"] : List String))]

private def nextState : State := { state with groupCount := 1 }

private theorem state_scalar_projection :
    StateScalarProjection hash inputs witness state := by
  intro identifier fact member scalarType
  simp only [state, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with guardMember | byteMember
  · injection guardMember with identifierEq factEq
    subst identifier
    subst fact
    cases scalarType
    constructor
    · simp [interpret, guardFact, witness]
    · exact Nat.le_refl 1
    · intro name exclusive asserted nonzero
      simp [guardFact] at asserted
  · injection byteMember with identifierEq factEq
    subst identifier
    subst fact
    cases scalarType

private theorem impact_row_accepted :
    validateInstruction expected state impactRow = .ok nextState := by
  with_unfolding_all rfl

private theorem impact_guard_decoded :
    NativeRelationJson.decodeOperandField impactRow "guard" = .ok (.reference "%guard") := by
  with_unfolding_all rfl

private theorem impact_payload_decoded :
    (do NativeRelationJson.decodeOperands (← impactRow.getObjVal? "inputs")) =
      .ok [.immediate (scalar 2), .immediate (scalar 3)] := by
  with_unfolding_all rfl

private theorem impact_opcode :
    Backend.Native.stringField impactRow "op" = .ok "impact" := by
  with_unfolding_all rfl

theorem byte_definition_is_present_without_scalar_interpretation :
    ("%bytes", byteFact) ∈ state.definitions ∧
      interpret hash inputs byteFact.term = none := by
  constructor
  · simp [state]
  · simp [interpret, byteFact]

/-- The producer accepts a guarded Native row, and strict field decoding plus
the partial scalar projection preserve the guard and payload order. The byte
definition stays in the state without requiring a scalar interpretation. -/
theorem guarded_impact_row_projects_ordered_payload :
    ∃ guardTerm group, ScalarValidationOutputMeaning.sourceImpactGuard expected state = some guardTerm ∧
      expected.groups[state.groupCount]? = some group ∧
      nextState = {state with groupCount := state.groupCount + 1} ∧
      interpret hash inputs guardTerm = some ((Operand.reference "%guard").read witness) ∧
      (((Operand.reference "%guard").read witness) = zero ∨
        ((Operand.reference "%guard").read witness) = one) ∧
      group.map (interpret hash inputs) =
        ([Operand.immediate (scalar 2), Operand.immediate (scalar 3)].map (·.read witness)).map some := by
  exact ScalarValidationOutputMeaning.accepted_impact_guard_and_payload_projection
    state_scalar_projection impact_row_accepted impact_opcode impact_guard_decoded
    impact_payload_decoded

/-- Selecting a byte definition as an Impact payload fails at the producer's
Native operand check, before payload matching. -/
theorem byte_payload_is_rejected :
    validateInstruction expected state bytePayloadRow =
      .error "native instruction operand must have Native type" := by
  with_unfolding_all rfl

end Noctium.Verification.GuardedImpactProjectionFixture
