import Noctium.Frontend
import Noctium.Disclosure

open scoped Noctium
open Noctium

noctium_circuit hashValues where
  private payload : Bytes 64
  private enabled : Bool
  let payload31 : Bytes 31 := sliceBytes(payload, 0, 31)
  let payload32 : Bytes 32 := sliceBytes(payload, 0, 32)
  let payload33 : Bytes 33 := sliceBytes(payload, 0, 33)
  let shaPayload : Bytes 64 := sha512(payload)
  let sha31 : Bytes 64 := sha512(payload31)
  let sha32 : Bytes 64 := sha512(payload32)
  let sha33 : Bytes 64 := sha512(payload33)
  let keccak31 : Bytes 32 := keccak256(payload31)
  let keccak32 : Bytes 32 := keccak256(payload32)
  let keccak33 : Bytes 32 := keccak256(payload33)
  let shaWindow : Bytes 33 := sliceBytes(shaPayload, 31, 64)
  assert eq(concatBytes(sliceBytes(shaPayload, 0, 31), shaWindow), shaPayload)
  output sha31First : UInt 8 := disclose(byteAt(sha31, 0))
  output sha31Last : UInt 8 := disclose(byteAt(sha31, 63))
  output sha32First : UInt 8 := disclose(byteAt(sha32, 0))
  output sha32Last : UInt 8 := disclose(byteAt(sha32, 63))
  output sha33First : UInt 8 := disclose(byteAt(sha33, 0))
  output sha33Last : UInt 8 := disclose(byteAt(sha33, 63))
  output keccak31First : UInt 8 := disclose(byteAt(keccak31, 0))
  output keccak31Last : UInt 8 := disclose(byteAt(keccak31, 31))
  output keccak32First : UInt 8 := disclose(byteAt(keccak32, 0))
  output keccak32Last : UInt 8 := disclose(byteAt(keccak32, 31))
  output keccak33First : UInt 8 := disclose(byteAt(keccak33, 0))
  output keccak33Last : UInt 8 := disclose(byteAt(keccak33, 31))
  output shaWindowFirst : UInt 8 := disclose(byteAt(shaWindow, 0))
  output shaWindowLast : UInt 8 := disclose(byteAt(shaWindow, 32))
end

noctium_contract ByteHashes where
  cell sha31First : UInt 8
  cell sha31Last : UInt 8
  cell sha32First : UInt 8
  cell sha32Last : UInt 8
  cell sha33First : UInt 8
  cell sha33Last : UInt 8
  cell keccak31First : UInt 8
  cell keccak31Last : UInt 8
  cell keccak32First : UInt 8
  cell keccak32Last : UInt 8
  cell keccak33First : UInt 8
  cell keccak33Last : UInt 8
  cell shaWindowFirst : UInt 8
  cell shaWindowLast : UInt 8
  entry inspect uses hashValues where
    write sha31First := sha31First
    write sha31Last := sha31Last
    write sha32First := sha32First
    write sha32Last := sha32Last
    write sha33First := sha33First
    write sha33Last := sha33Last
    write keccak31First := keccak31First
    write keccak31Last := keccak31Last
    write keccak32First := keccak32First
    write keccak32Last := keccak32Last
    write keccak33First := keccak33First
    write keccak33Last := keccak33Last
    write shaWindowFirst := shaWindowFirst
    write shaWindowLast := shaWindowLast
    return shaEmpty : Bytes 64 := disclose(sha512(assertThen(enabled, bytes(0, ""))))
    return keccakEmpty : Bytes32 := disclose(keccak256(assertThen(enabled, bytes(0, ""))))
    return shaAbc : Bytes 64 := disclose(sha512(bytes(3, "abc")))
    return keccakAbc : Bytes32 := disclose(keccak256(bytes(3, "abc")))
    return shaPayload : Bytes 64 := disclose(sha512(payload))
    return keccakPayload : Bytes32 := disclose(keccak256(payload))
  end
end

private def byteHashesEvalContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => pure 0
  sha512 := fun input => pure (List.replicate 64 (input.length % 256))
  keccak256 := fun input => pure (List.replicate 32 ((input.length + 1) % 256))
}

private def malformedSha512Context : EvalContext := {
  byteHashesEvalContext with sha512 := fun _ => pure (List.replicate 63 0)
}

private def malformedKeccak256Context : EvalContext := {
  byteHashesEvalContext with keccak256 := fun _ => pure (List.replicate 32 256)
}

#guard match (Expr.sha512 (.bytesLiteral 3 [97, 98, 99])).eval byteHashesEvalContext [] with
  | .ok digest => digest == List.replicate 64 3
  | .error _ => _root_.Bool.false
#guard match (Expr.keccak256 (.bytesLiteral 0 [])).eval byteHashesEvalContext [] with
  | .ok digest => digest == List.replicate 32 1
  | .error _ => _root_.Bool.false
#guard match (Expr.sha512 (.bytesLiteral 0 [])).eval malformedSha512Context [] with
  | .error "SHA-512 oracle returned a malformed Bytes64 digest" => _root_.Bool.true
  | _ => _root_.Bool.false
#guard match (Expr.keccak256 (.bytesLiteral 0 [])).eval malformedKeccak256Context [] with
  | .error "Keccak-256 oracle returned a malformed Bytes32 digest" => _root_.Bool.true
  | _ => _root_.Bool.false
#guard match (Expr.sha512
    (Expr.assertE (.bool Bool.false) (.bytesLiteral 0 [] : Expr (.bytes 0)))).eval
    byteHashesEvalContext [] with
  | .error "helper assertion failed" => _root_.Bool.true
  | _ => _root_.Bool.false
#guard match (Expr.sha512 (.bytesLiteral 1025 (List.replicate 1025 0))).validate
    Capabilities.source [] with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false
#guard match (Expr.keccak256 (.bytesLiteral 1025 (List.replicate 1025 0))).validate
    Capabilities.source [] with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false
#guard match (Expr.sha512 (.bytesLiteral 0 [])).validate
    {Capabilities.source with sha512 := _root_.Bool.false} [] with
  | .error "target lacks qualified SHA-512 support" => _root_.Bool.true
  | _ => _root_.Bool.false
#guard match (Expr.keccak256 (.bytesLiteral 0 [])).validate
    {Capabilities.source with keccak256 := _root_.Bool.false} [] with
  | .error "target lacks qualified Keccak-256 support" => _root_.Bool.true
  | _ => _root_.Bool.false
#guard match Disclosure.circuit {
  name := "undisclosedByteHash"
  inputs := [{name := "payload", ty := .bytes 64, visibility := .private}]
  outputs := [{name := "digest", ty := .bytes 64, value := (Noctium.Expr.sha512 (length := 64) (Noctium.Expr.ref "payload"))}]
} with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false

/-- error: sha512 requires a Bytes expression -/
#guard_msgs in
noctium_circuit invalidSha512Input where
  private payload : Native
  output digest : Bytes 64 := sha512(payload)
end

/-- error: keccak256 requires a Bytes, Native, or Secp256k1Point expression -/
#guard_msgs in
noctium_circuit invalidKeccakInput where
  private payload : Bool
  output digest : Bytes32 := keccak256(payload)
end

private def byteHashProducerAccepts (alignment : Lean.Json) (inputs : List String)
    (maximum : Nat) : _root_.Bool := Id.run do
  let expected : Noctium.Backend.Native.Expected :=
    {mode := .relation, inputs := [], groups := [], returns := [], assertions := [], bounds := []}
  let state : Noctium.Backend.Native.State :=
    {definitions := [("%byte", {term := .input "%byte", maximum})]}
  let instruction := Lean.Json.mkObj [
    ("op", Lean.toJson ("sha512" : String)), ("alignment", alignment),
    ("inputs", Lean.toJson inputs), ("output", Lean.toJson ("%digest" : String))]
  return (Noctium.Backend.Native.validateInstruction expected state instruction).isOk

private def oneByteHashAlignment : Lean.Json := Lean.Json.arr #[Lean.Json.mkObj [
  ("tag", Lean.toJson ("atom" : String)),
  ("value", Lean.Json.mkObj [("tag", Lean.toJson ("bytes" : String)),
    ("length", Lean.toJson (1 : Nat))])]]

#guard byteHashProducerAccepts oneByteHashAlignment ["%byte"] 255
#guard byteHashProducerAccepts (Lean.Json.arr #[]) [] 255
#guard !(byteHashProducerAccepts oneByteHashAlignment [] 255)
#guard !(byteHashProducerAccepts oneByteHashAlignment ["%byte"] 256)

private def oneFieldHashAlignment : Lean.Json := Lean.Json.arr #[Lean.Json.mkObj [
  ("tag", Lean.toJson ("atom" : String)),
  ("value", Lean.Json.mkObj [("tag", Lean.toJson ("field" : String))])]]

noctium_circuit rawOneByteHash where
  private payload : Bytes 1
  output first : UInt 8 := disclose(byteAt(sha512(payload), 0))
end

private def replaceHashJson (object : Lean.Json) (field : String) (value : Lean.Json) :
    Lean.Json := match object.getObj? with
  | .error _ => object
  | .ok fields => Lean.Json.mkObj (fields.toList.filter (·.1 != field) ++ [(field, value)])

-- A typed Field hash uses different binary bytes from a raw Bytes1 hash.
#guard match Backend.Zkir.lowerCircuit rawOneByteHash, Backend.Native.expectedCircuit rawOneByteHash with
  | .ok program, .ok expected =>
    match (program.getObjVal? "instructions").bind Lean.Json.getArr? with
    | .error _ => Bool.false
    | .ok instructions =>
      let mutated := instructions.map fun instruction =>
        if (instruction.getObjVal? "op").toOption == some (Lean.toJson ("sha512" : String)) then
          replaceHashJson instruction "alignment" oneFieldHashAlignment
        else instruction
      mutated != instructions &&
        (Backend.Native.validate expected program).isOk &&
        !(Backend.Native.validate expected
          (replaceHashJson program "instructions" (.arr mutated))).isOk
  | _, _ => Bool.false
