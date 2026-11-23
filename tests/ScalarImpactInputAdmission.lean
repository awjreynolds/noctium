import Noctium.Frontend
import Noctium.Verification.GenericStateOps

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

#guard match Backend.Impact.publicInputPlan scalarImpactEntry.circuit.inputs with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Impact.lower [] scalarImpactEntry with
  | .ok plan =>
    match GenericStateOps.evalPlan scalarImpactContext scalarImpactEnv plan with
    | .ok operations => operations == scalarImpactExpected
    | .error _ => Bool.false
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
