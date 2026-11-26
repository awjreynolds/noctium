import Noctium.Frontend
import Noctium.Verification.GenericStateMapAdmission

open scoped Noctium
open Noctium
open Noctium.Verification
open Noctium.Verification.NativeRelation
open Noctium.Verification.NativeState

noctium_circuit guardedScalarMapInputs where
  private account : Native
  private amount : UInt 8
  public enabled : Bool
end

noctium_contract GuardedScalarMapAdmission where
  map balances : Native => UInt 8

  entry guardedRoundTrip uses guardedScalarMapInputs where
    when enabled insert balances[disclose(account)] := disclose(amount)
    when enabled read balances[disclose(account)] as saved
    return result : UInt 8 := saved
  end
end

noctium_circuit bytes32ScalarMapInputs where
  private key : Bytes32
end

noctium_contract Bytes32ScalarMapAdmission where
  map digests : Bytes32 => Bool

  entry readDigest uses bytes32ScalarMapInputs where
    read digests[disclose(key)] as found
    return result : Bool := found
  end
end

namespace GuardedScalarMapAdmissionProof

private def guardedEntry : Entrypoint :=
  (GuardedScalarMapAdmission.entrypoints.find? (·.name == "guardedRoundTrip")).getD
    {name := "missing", circuit := {name := "missing"}}

private def sourceState : List StateDecl := GuardedScalarMapAdmission.state

private def guardedPlan : Backend.Impact.Plan :=
  match Backend.Impact.lower sourceState guardedEntry with
  | .ok plan => plan
  | .error _ => {}

private def guardedLowerSucceeded : _root_.Bool :=
  match Backend.Impact.lower sourceState guardedEntry with
  | .ok _ => _root_.Bool.true
  | .error _ => _root_.Bool.false

private theorem guarded_lower_succeeded : guardedLowerSucceeded = _root_.Bool.true := by
  decide +kernel

private theorem guarded_lowered :
    Backend.Impact.lower sourceState guardedEntry = .ok guardedPlan := by
  cases result : Backend.Impact.lower sourceState guardedEntry with
  | error message =>
      have succeeded := guarded_lower_succeeded
      simp [guardedLowerSucceeded, result] at succeeded
  | ok loweredPlan => simp [guardedPlan, result]

private theorem guarded_inputs_compatible :
    ∀ input ∈ guardedEntry.circuit.inputs,
      Backend.Impact.publicInputScalarCompatible input := by
  intro input inputMember
  simp [guardedEntry, GuardedScalarMapAdmission, guardedScalarMapInputs] at inputMember
  rcases inputMember with rfl | rfl | rfl <;>
    simp [Backend.Impact.publicInputScalarCompatible]

private theorem guarded_effects_supported :
    ∀ effect ∈ guardedEntry.effects,
      GenericStateMapAdmission.ScalarCellOrMapEffect sourceState effect := by
  intro effect effectMember
  simp [guardedEntry, GuardedScalarMapAdmission, guardedScalarMapInputs] at effectMember
  rcases effectMember with isWrite | isRead
  · cases isWrite
    exact .writeMap "balances" .native (.uint 255)
      (.disclose _ (.ref "account")) (.disclose _ (.ref "amount"))
      .native (.uint 255 (by decide))
  · cases isRead
    exact .readMap "balances" "saved" .native (.uint 255)
      (.disclose _ (.ref "account"))
      .native (.uint 255 (by decide))

theorem guarded_lowering_operations_supported :
    ∀ operation ∈ guardedPlan.operations,
      GenericStateOps.ScalarOperation operation :=
  GenericStateMapAdmission.lower_scalar_cell_or_map_operations_supported
    sourceState guardedEntry guardedPlan guarded_lowered guarded_inputs_compatible
      guarded_effects_supported

private def interpreterContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by guarded scalar Map admission fixture"
}

private def interpreterEnvironment : EvalEnv := [
  ("account", .native 17),
  ("amount", .uint 255 41),
  ("enabled", .bool _root_.Bool.true),
  ("saved", .uint 255 41)
]

private def guardedEvaluationSucceeded : _root_.Bool :=
  match GenericStateOps.evalPlan interpreterContext interpreterEnvironment guardedPlan with
  | .ok _ => _root_.Bool.true
  | .error _ => _root_.Bool.false

private theorem guarded_evaluation_succeeded :
    guardedEvaluationSucceeded = _root_.Bool.true := by
  decide +kernel

private def bytes32Entry : Entrypoint :=
  (Bytes32ScalarMapAdmission.entrypoints.find? (·.name == "readDigest")).getD
    {name := "missing", circuit := {name := "missing"}}

private def bytes32State : List StateDecl := Bytes32ScalarMapAdmission.state

#guard match bytes32Entry.effects with
  | [.readMap "digests" "found" (.bytes 32) .bool (.disclose _ (.ref "key"))] =>
      _root_.Bool.true
  | _ => _root_.Bool.false

private def bytes32LowerThenRejectSucceeded : _root_.Bool :=
  match Backend.Impact.lower bytes32State bytes32Entry with
  | .error _ => _root_.Bool.false
  | .ok plan =>
      match GenericStateOps.evalPlan interpreterContext
          [("key", .bytes 32 (List.range 32))] plan with
      | .error message =>
          message == "unsupported Impact operation in scalar state interpreter"
      | .ok _ => _root_.Bool.false

theorem bytes32_map_read_lower_then_rejects :
    bytes32LowerThenRejectSucceeded = _root_.Bool.true := by
  decide +kernel

end GuardedScalarMapAdmissionProof
