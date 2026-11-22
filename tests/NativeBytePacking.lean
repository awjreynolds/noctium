import Noctium.Frontend
import Noctium.Backend.Zkir
import Noctium.Semantics

open scoped Noctium

noctium_circuit packingInputs where
  private b1 : Bytes 1
  private b31 : Bytes 31
  private b32 : Bytes 32
  private b62 : Bytes 62
  private b63 : Bytes 63
  private empty0 : Bytes 0
end

private def nativeBytePackingLiteralValues : List Nat :=
  List.replicate 31 255 ++ [173]

private def nativeBytePackingLiteralCircuit : Noctium.Circuit := {
  name := "native_byte_packing_literal"
  outputs := [{name := "digest", ty := .bytes 32, value := .persistentHash32 (.bytes32Literal nativeBytePackingLiteralValues)}]
}

private def nativeBytePackingSymbolicCircuit : Noctium.Circuit := {
  name := "native_byte_packing_symbolic"
  inputs := [{name := "payload", ty := .bytes 32, visibility := .«private»}]
  outputs := [{name := "digest", ty := .bytes 32, value := .disclose {} (.persistentHash32 (.ref "payload"))}]
}

private def nativeBytePackingLiteralVectorCircuit : Noctium.Circuit := {
  name := "native_byte_packing_literal_vector"
  outputs := [{name := "digest", ty := .bytes 32, value := .persistentHashVector32 [
    .bytes32Literal nativeBytePackingLiteralValues,
    .bytes32Literal (List.replicate 32 7)]}]
}

private def nativeBytePackingMixedVectorCircuit : Noctium.Circuit := {
  name := "native_byte_packing_mixed_vector"
  inputs := [{name := "payload", ty := .bytes 32, visibility := .«private»}]
  outputs := [{name := "digest", ty := .bytes 32, value := .disclose {} (.persistentHashVector32 [
    .bytes32Literal nativeBytePackingLiteralValues,
    .ref "payload"])}]
}

private def narrowPackedByte (maximum value : Nat) : Noctium.Expr (.bytes 1) :=
  .sliceBytes (.toBytes32 (.cast .native (.uint maximum value))) 0 1

private def narrowLiteralPackingCircuit : Noctium.Circuit := {
  name := "narrow_literal_packing"
  outputs := [{
    name := "packed"
    ty := .bytes 2
    value := .disclose {} (.concatBytes (narrowPackedByte 7 7) (narrowPackedByte 23 23))
  }]
}

private def narrowRuntimePackingCircuit : Noctium.Circuit := {
  name := "narrow_runtime_packing"
  inputs := [{name := "octet", ty := .uint 7, visibility := .«public»}]
  outputs := [{
    name := "packed"
    ty := .bytes 1
    value := .disclose {} (.sliceBytes
      (.toBytes32 (.cast .native (.ref "octet" : Noctium.Expr (.uint 7)))) 0 1)
  }]
}

noctium_circuit hashVectorInputs where
  private payload : Bytes 32
end

noctium_contract HashVectorFold where
  entry measureHashVector uses hashVectorInputs where
    return digest : Bytes 32 := disclose(persistentHashVector32([
      bytes32("noctium:packing-test"), payload]))
  end
end

private def nativeBytePackingInstructions (relation : Lean.Json) : List Lean.Json :=
  ((relation.getObjValD "instructions").getArr?).toOption.getD #[] |>.toList

private def nativeBytePackingOpcode (instruction : Lean.Json) : Option String :=
  (instruction.getObjVal? "op").toOption.bind fun value => value.getStr?.toOption

private def nativeBytePackingCount (relation : Lean.Json) (opcode : String) : Nat :=
  (nativeBytePackingInstructions relation).filter
    (fun instruction => nativeBytePackingOpcode instruction == some opcode) |>.length

#guard match Noctium.Backend.Zkir.lowerCircuit nativeBytePackingLiteralCircuit with
  | .ok relation =>
      nativeBytePackingCount relation "add" == 0 && nativeBytePackingCount relation "mul" == 0
  | .error _ => _root_.Bool.false

#guard match Noctium.Backend.Zkir.lowerCircuit nativeBytePackingSymbolicCircuit with
  | .ok relation =>
      nativeBytePackingCount relation "add" == 30 && nativeBytePackingCount relation "mul" == 30
  | .error _ => _root_.Bool.false

#guard match Noctium.Backend.Zkir.lowerCircuit nativeBytePackingLiteralVectorCircuit with
  | .ok relation =>
      nativeBytePackingCount relation "add" == 0 && nativeBytePackingCount relation "mul" == 0
  | .error _ => _root_.Bool.false

#guard match Noctium.Backend.Zkir.lowerCircuit nativeBytePackingMixedVectorCircuit with
  | .ok relation =>
      nativeBytePackingCount relation "add" == 30 && nativeBytePackingCount relation "mul" == 30
  | .error _ => _root_.Bool.false

#guard match Noctium.Backend.Zkir.lowerCircuit narrowLiteralPackingCircuit with
  | .ok relation =>
      (nativeBytePackingInstructions relation).map nativeBytePackingOpcode ==
        [some "mul", some "add", some "impact", some "output"]
  | .error _ => _root_.Bool.false

private def narrowPackingContext : Noctium.EvalContext := {
  modulus := Noctium.Field.modulus
  poseidon2 := fun _ _ _ => pure 0
}

#guard match narrowRuntimePackingCircuit.run narrowPackingContext [
    ("octet", .uint 7 6)] with
  | .ok [("packed", .bytes 1 [6])] => _root_.Bool.true
  | _ => _root_.Bool.false

#guard match narrowRuntimePackingCircuit.run narrowPackingContext [
    ("octet", .uint 7 8)] with
  | .error _ => _root_.Bool.true
  | _ => _root_.Bool.false

#guard match Noctium.Backend.Zkir.lowerCircuit narrowRuntimePackingCircuit with
  | .ok relation =>
      (nativeBytePackingInstructions relation).map nativeBytePackingOpcode ==
        [some "public_input", some "constrain_bits", some "impact", some "impact", some "output"]
  | .error _ => _root_.Bool.false

noctium_contract NativeBytePacking where
  entry pack uses packingInputs where
    return r1 : Bytes 1 := disclose(reverseBytes(b1))
    return r31 : Bytes 31 := disclose(reverseBytes(b31))
    return r32 : Bytes 32 := disclose(reverseBytes(b32))
    return r62 : Bytes 62 := disclose(reverseBytes(b62))
    return r63 : Bytes 63 := disclose(reverseBytes(b63))
    return emptyResult : Bytes 0 := disclose(reverseBytes(empty0))
  end
end
