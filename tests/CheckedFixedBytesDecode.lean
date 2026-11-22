import Noctium.Frontend
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium

noctium_circuit checkedBytes1 where
  public value : Bytes 1
  output decoded : Native := fromBytesChecked(Native, value)
end

noctium_circuit checkedBytes31 where
  public value : Bytes 31
  output decoded : Native := fromBytesChecked(Native, value)
end

noctium_circuit checkedBytes32 where
  public value : Bytes 32
  output decoded : Native := fromBytesChecked(Native, value)
end

noctium_circuit nativeBytes32Baseline where
  public value : Bytes32
  output decoded : Native := fromBytes32(Native, value)
end

noctium_circuit checkedBytes33 where
  public value : Bytes 33
  output decoded : Native := fromBytesChecked(Native, value)
end

noctium_circuit checkedBytes64 where
  public value : Bytes 64
  output decoded : Native := fromBytesChecked(Native, value)
end

noctium_circuit checkedUInt16 where
  public value : Bytes 3
  output decoded : UInt 16 := fromBytesChecked(UInt 16, value)
end

noctium_witness_circuit checkedBytesReadable where
  public value : Bytes 2
  output decoded : UInt 16 := fromBytesChecked(UInt 16, value)
end

noctium_circuit checkedFixedBytesExecution where
  public nativeBytes : Bytes 33
  public uintBytes : Bytes 3
  output nativeDecoded : Native := fromBytesChecked(Native, nativeBytes)
  output uintDecoded : UInt 16 := fromBytesChecked(UInt 16, uintBytes)
end

noctium_contract CheckedFixedBytesDecode where
  entry decode uses checkedFixedBytesExecution where
    return nativeValue : Native := nativeDecoded
    return uintValue : UInt 16 := uintDecoded
  end
end

private def checkedBytesContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by checked byte decoding"
}

private def littleEndian (width value : Nat) : List Nat :=
  (List.range width).map fun index => value / (256 ^ index) % 256

#guard (Noctium.Backend.Zkir.lowerCircuit checkedBytes1).isOk
#guard (Noctium.Backend.Zkir.lowerCircuit checkedBytes31).isOk
#guard (Noctium.Backend.Zkir.lowerCircuit checkedBytes32).isOk
#guard (Noctium.Backend.Zkir.lowerCircuit nativeBytes32Baseline).isOk
#guard (Noctium.Backend.Zkir.lowerCircuit checkedBytes33).isOk
#guard (Noctium.Backend.Zkir.lowerCircuit checkedBytes64).isOk
#guard (Noctium.Backend.Zkir.lowerCircuit checkedUInt16).isOk
#guard (Noctium.Witness.compile checkedBytesReadable.__program
  "noctium.witness-circuit.checkedBytesReadable.v1").isOk

#guard match checkedBytes1.run checkedBytesContext [("value", .bytes 1 [255])] with
  | .ok [("decoded", .native 255)] => Bool.true
  | _ => Bool.false
#guard match checkedBytes31.run checkedBytesContext
    [("value", .bytes 31 (List.replicate 31 255))] with
  | .ok [("decoded", .native value)] => value == 2 ^ 248 - 1
  | _ => Bool.false
#guard match checkedBytes32.run checkedBytesContext
    [("value", .bytes 32 (littleEndian 32 (Field.modulus - 1)))] with
  | .ok [("decoded", .native value)] => value == Field.modulus - 1
  | _ => Bool.false
#guard match checkedBytes32.run checkedBytesContext
    [("value", .bytes 32 (littleEndian 32 Field.modulus))] with
  | .error _ => Bool.true
  | _ => Bool.false
#guard match (Expr.fromBytes (target := .native)
    (.bytesLiteral 33 (littleEndian 33 Field.modulus))).eval checkedBytesContext [] with
  | .ok 0 => Bool.true
  | _ => Bool.false

#guard match checkedBytes33.run checkedBytesContext
    [("value", .bytes 33 (littleEndian 32 513 ++ [0]))] with
  | .ok [("decoded", .native 513)] => Bool.true
  | _ => Bool.false
#guard match checkedBytes33.run checkedBytesContext
    [("value", .bytes 33 (littleEndian 32 513 ++ [1]))] with
  | .error _ => Bool.true
  | _ => Bool.false
#guard match checkedBytes33.run checkedBytesContext
    [("value", .bytes 33 (littleEndian 32 Field.modulus ++ [0]))] with
  | .error _ => Bool.true
  | _ => Bool.false
#guard match checkedBytes64.run checkedBytesContext
    [("value", .bytes 64 (littleEndian 32 513 ++ List.replicate 32 0))] with
  | .ok [("decoded", .native 513)] => Bool.true
  | _ => Bool.false
#guard match checkedBytes64.run checkedBytesContext
    [("value", .bytes 64 (littleEndian 32 513 ++
      List.replicate 8 0 ++ [1] ++ List.replicate 23 0))] with
  | .error _ => Bool.true
  | _ => Bool.false

#guard match checkedUInt16.run checkedBytesContext [("value", .bytes 3 [255, 255, 0])] with
  | .ok [("decoded", .uint 65535 65535)] => Bool.true
  | _ => Bool.false
#guard match checkedUInt16.run checkedBytesContext [("value", .bytes 3 [0, 0, 1])] with
  | .error _ => Bool.true
  | _ => Bool.false

/- error: fromBytesChecked requires at least one byte -/
#guard_msgs (substring := true) in
noctium_circuit rejectsEmptyCheckedBytes where
  public value : Bytes 0
  output decoded : Native := fromBytesChecked(Native, value)
end
