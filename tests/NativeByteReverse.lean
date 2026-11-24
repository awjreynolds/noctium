import Noctium.Frontend
import Noctium.Backend.NativeMeaning
import Noctium.Backend.NativeProducer
import Noctium.Disclosure

open scoped Noctium
open Noctium

noctium_circuit computedByteReverse where
  private payload : Bytes32
  private field : Native
  public chooseHash : Bool
  let reversed : Bytes32 := reverseBytes32(payload)
  let digest : Bytes32 := persistentHash32(payload)
  let serialized : Bytes32 := toBytes32(field)
  output rawFirst : UInt 8 := disclose(byteAt(reversed, 0))
  output rawLast : UInt 8 := disclose(byteAt(reversed, 31))
  output digestFirst : UInt 8 := disclose(byteAt(reverseBytes32(digest), 0))
  output serializedFirst : UInt 8 := disclose(byteAt(reverseBytes32(serialized), 0))
  output selectedFirst : UInt 8 := disclose(byteAt(reverseBytes32(select(chooseHash, digest, serialized)), 0))
  output roundTripFirst : UInt 8 := disclose(byteAt(reverseBytes32(reversed), 0))
end

noctium_contract NativeByteReverse where
  cell rawFirst : UInt 8
  cell rawLast : UInt 8
  cell digestFirst : UInt 8
  cell serializedFirst : UInt 8
  cell selectedFirst : UInt 8
  cell roundTripFirst : UInt 8
  entry inspect uses computedByteReverse where
    write rawFirst := rawFirst
    write rawLast := rawLast
    write digestFirst := digestFirst
    write serializedFirst := serializedFirst
    write selectedFirst := selectedFirst
    write roundTripFirst := roundTripFirst
  end
end

noctium_circuit reverseByteAtProjection where
  private value : Bytes32
  output first : UInt 8 := disclose(byteAt(reverseBytes32(value), 0))
  output last : UInt 8 := disclose(byteAt(reverseBytes32(value), 31))
end

noctium_circuit mirroredByteAtProjection where
  private value : Bytes32
  output first : UInt 8 := disclose(byteAt(value, 31))
  output last : UInt 8 := disclose(byteAt(value, 0))
end

#guard match Backend.Zkir.lowerCircuit reverseByteAtProjection,
    Backend.Zkir.lowerCircuit mirroredByteAtProjection with
  | .ok reverse, .ok mirrored => reverse == mirrored
  | _, _ => _root_.Bool.false

private def byteReverseSemanticContext : EvalContext :=
  {modulus := Field.modulus, poseidon2 := fun _ _ _ => pure 0}

private def ascendingBytes32 : Expr (.bytes 32) :=
  .bytes32Literal ((List.range 32).map (· + 1))

#guard match (Expr.reverseBytes32 ascendingBytes32).eval byteReverseSemanticContext [] with
  | .ok bytes => bytes == (((List.range 32).map (· + 1)).reverse)
  | .error _ => _root_.Bool.false
#guard match (Expr.reverseBytes32 (Expr.reverseBytes32 ascendingBytes32)).eval
    byteReverseSemanticContext [] with
  | .ok bytes => bytes == ((List.range 32).map (· + 1))
  | .error _ => _root_.Bool.false
example : (Expr.reverseBytes32 (Expr.reverseBytes32 ascendingBytes32)).eval
    byteReverseSemanticContext [] = ascendingBytes32.eval byteReverseSemanticContext [] :=
  Expr.eval_reverseBytes32_twice byteReverseSemanticContext [] ascendingBytes32

#guard match (Expr.bytesAt (Expr.reverseBytes32 ascendingBytes32) 0).eval
    byteReverseSemanticContext [] with
  | .ok byte => byte == 32
  | .error _ => _root_.Bool.false
#guard match (Expr.bytesAt (Expr.reverseBytes32 ascendingBytes32) 31).eval
    byteReverseSemanticContext [] with
  | .ok byte => byte == 1
  | .error _ => _root_.Bool.false
#guard match Backend.Native.normalize []
    (Expr.bytesAt (Expr.reverseBytes32 ascendingBytes32) 32) with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false

#guard match Disclosure.circuit {
  name := "undisclosedByteReverse"
  inputs := [{name := "payload", ty := .bytes 32, visibility := .private}]
  outputs := [{name := "reversed", ty := .bytes 32, value := (Noctium.Expr.reverseBytes32 (Noctium.Expr.ref "payload"))}]
} with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false

/-- error: Noctium expression type mismatch -/
#guard_msgs in
noctium_circuit wrongByteReverseType where
  private field : Native
  output reversed : Bytes32 := reverseBytes32(field)
end

private def reverseProducerAccepts (valueType : Noctium.Backend.Native.NativeValueType)
    (malformed : _root_.Bool) : _root_.Bool := Id.run do
  let expected : Noctium.Backend.Native.Expected :=
    {mode := .relation, inputs := [], groups := [], returns := [], assertions := [], bounds := []}
  let state : Noctium.Backend.Native.State :=
    {definitions := [("%bytes", {term := .input "%bytes", maximum := 0, valueType})]}
  let fields := [("op", Lean.toJson ("reverse" : String)),
    ("bytes", Lean.toJson ("%bytes" : String)), ("output", Lean.toJson ("%out" : String))]
  let instruction := Lean.Json.mkObj (fields ++ if malformed then
    [("extra", Lean.toJson _root_.Bool.true)] else [])
  return (Noctium.Backend.Native.validateInstruction expected state instruction).isOk

#guard reverseProducerAccepts .bytes32 _root_.Bool.false
#guard !(reverseProducerAccepts .native _root_.Bool.false)
#guard !(reverseProducerAccepts .bytes32 _root_.Bool.true)
