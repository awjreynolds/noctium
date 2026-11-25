import Noctium.Frontend
import Noctium.Verification.GenericStateScalarPrefix

open scoped Noctium
open Noctium
open Noctium.Verification
open Noctium.Verification.NativeRelation
open Noctium.Verification.NativeState

noctium_circuit scalarImpactInputs where
  public amount : Native
  public enabled : Bool
  public count : UInt 5
end

noctium_contract ScalarImpactInputAdmission where
  entry acceptScalars uses scalarImpactInputs where
  end
end

noctium_circuit bytes32ImpactInput where
  public digest : Bytes32
end

noctium_contract Bytes32ImpactInputAdmission where
  entry rejectBytes32 uses bytes32ImpactInput where
  end
end

private def scalarImpactEntry : Entrypoint :=
  (ScalarImpactInputAdmission.entrypoints.find? (·.name == "acceptScalars")).getD
    {name := "missing", circuit := {name := "missing"}}

private def bytes32ImpactEntry : Entrypoint :=
  (Bytes32ImpactInputAdmission.entrypoints.find? (·.name == "rejectBytes32")).getD
    {name := "missing", circuit := {name := "missing"}}

private def scalarImpactContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by scalar Impact admission fixture"
}

private def scalarImpactEnv : EvalEnv := [
  ("amount", .native 17),
  ("enabled", .bool Bool.true),
  ("count", .uint 31 23)
]

private def scalarImpactExpected : List NativeState.Op := [
  .push (NativeState.field (scalar 17)) Bool.false,
  .popeq (NativeState.field (scalar 17)),
  .push (NativeState.field (scalar 1)) Bool.false,
  .popeq (NativeState.field (scalar 1)),
  .push (NativeState.field (scalar 23)) Bool.false,
  .popeq (NativeState.field (scalar 23))
]

private theorem scalarImpact_lowered_operations_supported :
    ∀ plan, Backend.Impact.lower [] scalarImpactEntry = .ok plan →
      ∀ operation ∈ plan.operations, GenericStateOps.ScalarOperation operation := by
  have noEffects : scalarImpactEntry.effects = [] := by
    simp [scalarImpactEntry, ScalarImpactInputAdmission]
  have compatible : ∀ input ∈ scalarImpactEntry.circuit.inputs,
      Backend.Impact.publicInputScalarCompatible input := by
    intro input hmem
    simp [scalarImpactEntry, ScalarImpactInputAdmission, scalarImpactInputs] at hmem
    rcases hmem with h | h | h <;> subst input <;>
      simp [Backend.Impact.publicInputScalarCompatible]
  intro plan lowered
  exact GenericStateScalarPrefix.lower_public_input_only_scalar_supported
    [] scalarImpactEntry plan lowered noEffects compatible

#guard match Backend.Impact.publicInputPlan scalarImpactEntry.circuit.inputs with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Impact.lower [] scalarImpactEntry with
  | .ok plan =>
    match GenericStateOps.evalPlan scalarImpactContext scalarImpactEnv plan with
    | .ok operations => operations == scalarImpactExpected
    | .error _ => Bool.false
  | .error _ => Bool.false

-- The first supplied parameter succeeds. Both evaluators must report the
-- same next missing parameter before reaching the later count read.
#guard match Backend.Impact.lower [] scalarImpactEntry with
  | .ok plan =>
    let incomplete : EvalEnv := [("amount", .native 17)]
    match GenericStateOps.evalPlan scalarImpactContext incomplete plan,
      plan.operations.mapM (fun operation =>
        GenericStateOps.evalFields scalarImpactContext incomplete operation.fields) with
    | .error operationError, .error fieldError =>
      operationError == "missing value 'enabled'" && fieldError == operationError
    | _, _ => Bool.false
  | .error _ => Bool.false

private def bytes32ImpactEnv : EvalEnv :=
  [("digest", .bytes 32 (List.range 32))]

#guard match Backend.Impact.publicInputPlan bytes32ImpactEntry.circuit.inputs with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Impact.lower [] bytes32ImpactEntry with
  | .ok plan =>
    match GenericStateOps.evalPlan scalarImpactContext bytes32ImpactEnv plan with
    | .error message => message == "unsupported Impact alignment in scalar state interpreter"
    | .ok _ => Bool.false
  | .error _ => Bool.false
