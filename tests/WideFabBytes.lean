import Noctium.Frontend
import Noctium.Backend.NativeExpected
import Noctium.Backend.Zkir
import Noctium.Semantics

open scoped Noctium
open Noctium
open Noctium.Types

private def wideFabBytesEnvironment : CompositeEnv := {
  structures := [
    {id := "WideFabBytes.Mixed33", fields := [
      {name := "payload", type := .bytes 33},
      {name := "value", type := .scalar (.uint 255)}
    ]},
    {id := "WideFabBytes.Mixed63", fields := [
      {name := "payload", type := .bytes 63},
      {name := "value", type := .scalar (.uint 255)}
    ]},
    {id := "WideFabBytes.Only63", fields := [
      {name := "payload", type := .bytes 63}
    ]}
  ]
}

private def wideFabBytesMixed33Type : CompositeType := .structure "WideFabBytes.Mixed33"
private def wideFabBytesMixed63Type : CompositeType := .structure "WideFabBytes.Mixed63"
private def wideFabBytesOnly63Type : CompositeType := .structure "WideFabBytes.Only63"

noctium_circuit wideFabBytes33Inputs where
  private payload : Bytes 33
  private value : UInt 8
  output mixedDigest : Bytes32 := disclose(persistentHashFab(
    wideFabBytesEnvironment, wideFabBytesMixed33Type, [payload, value]))
end

noctium_circuit wideFabBytes63Inputs where
  private payload : Bytes 63
  private value : UInt 8
  output threeChunkDigest : Bytes32 := disclose(persistentHashFab(
    wideFabBytesEnvironment, wideFabBytesMixed63Type, [payload, value]))
end

noctium_circuit wideFabBytes63SingletonInputs where
  private payload : Bytes 63
  output singletonDigest : Bytes32 := disclose(persistentHashFab(
    wideFabBytesEnvironment, wideFabBytesOnly63Type, [payload]))
end

noctium_contract WideFabBytes where
  entry hash33 uses wideFabBytes33Inputs where
    return mixedDigestResult : Bytes32 := mixedDigest
  end
  entry hash63 uses wideFabBytes63Inputs where
    return threeChunkDigestResult : Bytes32 := threeChunkDigest
  end
  entry hash63Only uses wideFabBytes63SingletonInputs where
    return singletonDigestResult : Bytes32 := singletonDigest
  end
end

private def wideFabBytesPayload33 : List Nat :=
  (List.range 33).map fun index => (3 + 17 * index) % 256

private def wideFabBytesPayload63 : List Nat :=
  (List.range 63).map fun index => (1 + 29 * index) % 256

private def wideFabBytesGuardedExpression : Expr (.bytes 32) :=
  .disclose {} (.persistentHashFab wideFabBytesEnvironment wideFabBytesMixed33Type [
    ⟨.bytes 33, .assertE (.ref "mustPass") (.ref "payload")⟩,
    ⟨.uint 255, .ref "value"⟩])

private def wideFabBytesGuardedCircuit : Circuit := {
  name := "wide_fab_bytes_guarded"
  inputs := [
    {name := "mustPass", ty := .bool, visibility := .private},
    {name := "payload", ty := .bytes 33, visibility := .private},
    {name := "value", ty := .uint 255, visibility := .private}
  ]
  outputs := [{name := "mixedDigest", ty := .bytes 32, value := wideFabBytesGuardedExpression}]
}

private def wideFabBytesEvaluationContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => pure 0
  persistentHash32 := fun preimage =>
    if preimage == wideFabBytesPayload33 ++ [197] then pure (List.replicate 32 77)
    else if preimage == wideFabBytesPayload63 ++ [9] then pure (List.replicate 32 76)
    else throw "wide FAB byte fixture received a different byte preimage"
}

#guard match wideFabBytesGuardedExpression.eval wideFabBytesEvaluationContext [
    ("mustPass", .bool _root_.Bool.true),
    ("payload", .bytes 33 wideFabBytesPayload33),
    ("value", .uint 255 197)] with
  | .ok digest => digest == List.replicate 32 77
  | .error _ => _root_.Bool.false

#guard match wideFabBytesGuardedExpression.eval wideFabBytesEvaluationContext [
    ("mustPass", .bool _root_.Bool.false),
    ("payload", .bytes 33 wideFabBytesPayload33),
    ("value", .uint 255 197)] with
  | .error "helper assertion failed" => _root_.Bool.true
  | _ => _root_.Bool.false

#guard match (Expr.persistentHashFab wideFabBytesEnvironment wideFabBytesMixed63Type [
    ⟨.bytes 63, .bytesLiteral 63 wideFabBytesPayload63⟩,
    ⟨.uint 255, .uint 255 9⟩]).eval wideFabBytesEvaluationContext [] with
  | .ok digest => digest == List.replicate 32 76
  | .error _ => _root_.Bool.false

#guard match Backend.Native.expectedCircuit wideFabBytesGuardedCircuit with
  | .ok expected => expected.assertions.contains (.input "%input_mustPass")
  | .error _ => _root_.Bool.false

private def wideFabBytesOpcodes (relation : Lean.Json) : List String :=
  let instructions := ((relation.getObjValD "instructions").getArr?).toOption.getD #[]
  instructions.toList.filterMap fun instruction =>
    (instruction.getObjVal? "op").toOption.bind fun op => op.getStr?.toOption

#guard match Backend.Zkir.lowerCircuit wideFabBytesGuardedCircuit with
  | .ok relation => wideFabBytesOpcodes relation |>.contains "assert"
  | .error _ => _root_.Bool.false

private def wideFabBytesCompiled63 : Except LayoutDiagnostic CompiledType :=
  compileType wideFabBytesEnvironment wideFabBytesMixed63Type

#guard match wideFabBytesCompiled63 with
  | .ok compiled =>
    match Helpers.Wire.transientHashOperands compiled (.ref "payload") with
    | .ok [
        .cast .native (.project (.project (.ref "payload") (.field "payload")) (.byteIndex 62)),
        _, _, .cast .native (.project (.ref "payload") (.field "value"))] => _root_.Bool.true
    | .ok _ => _root_.Bool.false
    | .error _ => _root_.Bool.false
  | .error _ => _root_.Bool.false

private def wideFabBytesHelperProgram : Except String Helpers.Program := do
  let compiled ← (Types.compileType wideFabBytesEnvironment wideFabBytesMixed63Type).mapError (·.message)
  let operands ← Helpers.Wire.fabDigestOperands compiled (.ref "payload")
  pure {
    composites := wideFabBytesEnvironment
    declarations := [{
      id := ⟨0, 0⟩
      name := "hashPayload"
      parameters := [{name := "payload", ty := .native}]
      compositeParameters := [("payload", wideFabBytesMixed63Type)]
      result := .scalar (.bytes 32)
      body := [.return (some (.bytes
        (.fabDigest .persistentHash wideFabBytesMixed63Type (operands.map Prod.fst))
        (operands.map Prod.snd)))]
    }]
    exports := [{
      name := "hashPayload"
      target := ⟨0, 0⟩
      compositeInputs := [{name := "payload", type := wideFabBytesMixed63Type, visibility := .public}]
    }]
  }

private def wideFabBytesHelperInputs : List (String × Value) :=
  ((List.range 63).map fun index =>
    (s!"payload.payload.{index}", Value.native ((1 + 29 * index) % 256))) ++
      [("payload.value", Value.native 9)]

private def wideFabBytesHelperResult : Except String (List (String × Value)) := do
  let program ← wideFabBytesHelperProgram
  let circuit ← (Helpers.compile program "hashPayload").mapError (·.message)
  circuit.run wideFabBytesEvaluationContext wideFabBytesHelperInputs

#guard match wideFabBytesHelperResult with
  | .ok outputs => outputs.lookup "result" == some (.bytes 32 (List.replicate 32 76))
  | .error _ => _root_.Bool.false
