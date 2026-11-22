import Noctium.Frontend
import Noctium.Backend.NativeExpected
import Noctium.Backend.Zkir
import Noctium.Semantics

open scoped Noctium
open Noctium
open Noctium.Types

private def emptyFabBytesEnvironment : CompositeEnv := {
  structures := [
    {id := "EmptyFabBytes.Mixed", fields := [
      {name := "empty", type := .bytes 0},
      {name := "value", type := .scalar .bool}
    ]},
    {id := "EmptyFabBytes.EmptyOnly", fields := [
      {name := "empty", type := .bytes 0}
    ]}
  ]
}

private def emptyFabBytesMixedType : CompositeType := .structure "EmptyFabBytes.Mixed"
private def emptyFabBytesOnlyType : CompositeType := .structure "EmptyFabBytes.EmptyOnly"

noctium_circuit emptyFabBytesInputs where
  private mustPass : Bool
  private value : Bool
  private emptyBytes : Bytes 0
  output mixedDigest : Bytes32 := disclose(persistentHashFab(
    emptyFabBytesEnvironment, emptyFabBytesMixedType,
    [assertThen(mustPass, emptyBytes), value]))
  output emptyOnlyDigest : Bytes32 := disclose(persistentHashFab(
    emptyFabBytesEnvironment, emptyFabBytesOnlyType, [emptyBytes]))
end

noctium_contract EmptyFabBytes where
  entry hash uses emptyFabBytesInputs where
    return mixedDigestResult : Bytes32 := mixedDigest
    return emptyOnlyDigestResult : Bytes32 := emptyOnlyDigest
  end
end

private def emptyFabBytesGuardedExpression : Expr (.bytes 32) :=
  .disclose {} (.persistentHashFab emptyFabBytesEnvironment emptyFabBytesMixedType [
    ⟨.bytes 0, .assertE (.ref "mustPass") (.bytesLiteral 0 [])⟩,
    ⟨.bool, .ref "value"⟩])

private def emptyFabBytesGuardedCircuit : Circuit := {
  name := "empty_fab_bytes_guarded"
  inputs := [
    {name := "mustPass", ty := .bool, visibility := .private},
    {name := "value", ty := .bool, visibility := .private}
  ]
  outputs := [{name := "mixedDigest", ty := .bytes 32, value := emptyFabBytesGuardedExpression}]
}

private def emptyFabBytesEvaluationContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => pure 0
  persistentHash32 := fun preimage =>
    if preimage == [] then pure (List.replicate 32 9)
    else if preimage == [0] then pure (List.replicate 32 8)
    else if preimage == [1] then pure (List.replicate 32 7)
    else throw "unexpected empty FAB test preimage"
}

#guard match emptyFabBytesGuardedExpression.eval
    emptyFabBytesEvaluationContext
      [("mustPass", .bool _root_.Bool.true), ("value", .bool _root_.Bool.true)] with
  | .ok digest => digest == List.replicate 32 7
  | .error _ => _root_.Bool.false

#guard match emptyFabBytesGuardedExpression.eval
    emptyFabBytesEvaluationContext
      [("mustPass", .bool _root_.Bool.false), ("value", .bool _root_.Bool.true)] with
  | .error "helper assertion failed" => _root_.Bool.true
  | _ => _root_.Bool.false

#guard match (Expr.persistentHashFab emptyFabBytesEnvironment emptyFabBytesOnlyType [
    ⟨.bytes 0, .bytesLiteral 0 []⟩]).eval emptyFabBytesEvaluationContext [] with
  | .ok digest => digest == List.replicate 32 9
  | .error _ => _root_.Bool.false

#guard match Backend.Native.expectedCircuit emptyFabBytesGuardedCircuit with
  | .ok expected => expected.assertions.contains (.input "%input_mustPass")
  | .error _ => _root_.Bool.false

private def emptyFabBytesOpcodes (relation : Lean.Json) : List String :=
  let instructions := ((relation.getObjValD "instructions").getArr?).toOption.getD #[]
  instructions.toList.filterMap fun instruction =>
    (instruction.getObjVal? "op").toOption.bind fun op => op.getStr?.toOption

#guard match Backend.Zkir.lowerCircuit emptyFabBytesGuardedCircuit with
  | .ok relation => emptyFabBytesOpcodes relation |>.contains "assert"
  | .error _ => _root_.Bool.false

private def emptyFabBytesCompiledMixed : Except LayoutDiagnostic CompiledType :=
  compileType emptyFabBytesEnvironment emptyFabBytesMixedType

private def emptyFabBytesCompiledOnly : Except LayoutDiagnostic CompiledType :=
  compileType emptyFabBytesEnvironment emptyFabBytesOnlyType

#guard match emptyFabBytesCompiledMixed with
  | .ok compiled =>
    match Helpers.Wire.transientHashOperands compiled (.ref "payload") with
    | .ok operands => operands.length == 1
    | .error _ => _root_.Bool.false
  | .error _ => _root_.Bool.false

#guard match emptyFabBytesCompiledOnly with
  | .ok compiled =>
    match Helpers.Wire.transientHashOperands compiled (.ref "payload") with
    | .ok operands => operands.isEmpty
    | .error _ => _root_.Bool.false
  | .error _ => _root_.Bool.false

#guard match emptyFabBytesCompiledOnly with
  | .ok compiled =>
    match Helpers.Wire.fabDigestOperands compiled (.ref "payload") with
    | .ok fields => fields.length == 1
    | .error _ => _root_.Bool.false
  | .error _ => _root_.Bool.false
