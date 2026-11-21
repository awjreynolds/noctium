import Noctium.Frontend
import Noctium.Backend.Zkir

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
