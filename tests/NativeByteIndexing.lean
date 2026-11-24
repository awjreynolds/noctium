import Noctium.Frontend
import Noctium.Backend.NativeProducer
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium

noctium_circuit computedByteIndexing where
  private payload : Bytes32
  private field : Native
  public chooseHash : Bool
  let digest : Bytes32 := persistentHash32(payload)
  output rawFirst : UInt 8 := disclose(byteAt(payload, 0))
  output digestFirst : UInt 8 := disclose(byteAt(digest, 0))
  output digestLast : UInt 8 := disclose(byteAt(digest, 31))
  output serializedSecond : UInt 8 := disclose(byteAt(toBytes32(field), 1))
  output selectedByte : UInt 8 := disclose(byteAt(select(chooseHash, digest, toBytes32(field)), 7))
end

noctium_contract NativeByteIndexing where
  cell rawFirst : UInt 8
  cell digestFirst : UInt 8
  cell digestLast : UInt 8
  cell serializedSecond : UInt 8
  cell selectedByte : UInt 8
  entry inspect uses computedByteIndexing where
    write rawFirst := rawFirst
    write digestFirst := digestFirst
    write digestLast := digestLast
    write serializedSecond := serializedSecond
    write selectedByte := selectedByte
  end
end

-- Selecting a digest byte retains its private source origin.
#guard !(Noctium.Disclosure.circuit {
  name := "byteLeak"
  inputs := [{name := "payload", ty := .bytes 32, visibility := .private}]
  outputs := [{name := "leaked", ty := .uint 255, value := .bytesAt (.persistentHash32 (.ref "payload")) 0}]
}).isOk

noctium_circuit serializedByteAtProjection where
  private field : Native
  output first : UInt 8 := disclose(byteAt(toBytes32(field), 0))
  output last : UInt 8 := disclose(byteAt(toBytes32(field), 31))
end

private def opCount (instructions : Array Lean.Json) (name : String) : Nat :=
  (instructions.toList.filter fun instruction => Backend.Native.opcode instruction == name).length

private def usesRawSerializedBytes (program : Lean.Json) : _root_.Bool := Id.run do
  let .ok instructions := program.getObjValAs? (Array Lean.Json) "instructions" | return _root_.Bool.false
  if opCount instructions "to_bytes" != 1 || opCount instructions "bytes_into_natives" != 0 ||
      opCount instructions "bytes_from_natives" != 0 || opCount instructions "nth" != 2 ||
      opCount instructions "encode" != 2 then
    return _root_.Bool.false
  let some toBytes := instructions.toList.find? (fun instruction =>
    Backend.Native.opcode instruction == "to_bytes") | return _root_.Bool.false
  let some raw := (toBytes.getObjValAs? String "output").toOption | return _root_.Bool.false
  let nths := instructions.toList.filter fun instruction => Backend.Native.opcode instruction == "nth"
  match nths with
  | [first, last] =>
    (first.getObjValAs? String "bytes").toOption == some raw &&
      (first.getObjValAs? Nat "index").toOption == some 0 &&
      (last.getObjValAs? String "bytes").toOption == some raw &&
      (last.getObjValAs? Nat "index").toOption == some 31
  | _ => _root_.Bool.false

#guard match Backend.Zkir.lowerCircuit serializedByteAtProjection with
  | .ok program => usesRawSerializedBytes program
  | .error _ => _root_.Bool.false

noctium_circuit widenedNativeByteProjection where
  private value : UInt 8
  output first : UInt 8 := disclose(byteAt(toBytes32(cast(Native, value)), 0))
  output last : UInt 8 := disclose(byteAt(toBytes32(cast(Native, value)), 31))
end

#guard match Backend.Zkir.lowerCircuit widenedNativeByteProjection with
  | .ok program =>
    match program.getObjValAs? (Array Lean.Json) "instructions" with
    | .ok instructions => opCount instructions "to_bytes" == 0 &&
        opCount instructions "bytes_into_natives" == 0 &&
        opCount instructions "bytes_from_natives" == 0 &&
        opCount instructions "nth" == 0
    | .error _ => _root_.Bool.false
  | .error _ => _root_.Bool.false

private def nativeSerializedByteMeaningMatches (index : Nat) : _root_.Bool :=
  let source : Expr .native := .ref "field"
  let expression := Expr.bytesAt (Expr.toBytes32 source) index
  match Backend.Native.normalize [("field", Backend.Native.Term.input "field")] expression with
  | .error _ => _root_.Bool.false
  | .ok normalized =>
    let bytes := Backend.Native.Term.unary "to_bytes32_native" (.input "field")
    let byte := Backend.Native.bytes32ByteAtTerm bytes index
    normalized.term == byte && normalized.bounds == [(byte, 255)] && normalized.assertions == []

#guard nativeSerializedByteMeaningMatches 0
#guard nativeSerializedByteMeaningMatches 31
