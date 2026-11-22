import Noctium.Frontend
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium

noctium_circuit fieldOne where
  public value : Native
  output oneByte : Bytes 1 := disclose(toBytes(value, 1))
end

noctium_circuit field31 where
  public value : Native
  output thirtyOneBytes : Bytes 31 := disclose(toBytes(value, 31))
end

noctium_circuit fieldWide where
  public value : Native
  output wordBytes : Bytes32 := disclose(toBytes(value, 32))
  output paddedThirtyThree : Bytes 33 := disclose(toBytes(value, 33))
  output paddedSixtyFour : Bytes 64 := disclose(toBytes(value, 64))
end

noctium_witness_circuit readableUIntOne where
  public value : UInt 16
  output uintByte : Bytes 1 := disclose(toBytes(value, 1))
end

noctium_contract FixedNumericBytes where
  entry fieldOne uses fieldOne where
    return encoded : Bytes 1 := oneByte
  end
  entry field31 uses field31 where
    return encoded : Bytes 31 := thirtyOneBytes
  end
  entry fieldWide uses fieldWide where
    return word : Bytes32 := wordBytes
    return padded33 : Bytes 33 := paddedThirtyThree
    return padded64 : Bytes 64 := paddedSixtyFour
  end
end

noctium_contract ReadableFixedNumericBytes where
  entry uintOne uses readableUIntOne where
    return encoded : Bytes 1 := uintByte
  end
end

private def fixedNumericBytesContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused"
}

#guard (Noctium.Backend.Zkir.lowerCircuit fieldOne).isOk
#guard (Noctium.Backend.Zkir.lowerCircuit field31).isOk
#guard (Noctium.Backend.Zkir.lowerCircuit fieldWide).isOk
#guard (Noctium.Witness.compile readableUIntOne.__program
  "noctium.witness-circuit.readableUIntOne.v1").isOk
#guard readableUIntOne.__observation.generatedValidity ==
  ["checked byte fit toBytes(value, 1)"]
#guard readableUIntOne.__observation.explicitReleases == ["toBytes(value, 1)"]
#guard match Noctium.Wire.numericBytesTarget .native Noctium.maxBytesLength with
  | .ok .native => _root_.Bool.true
  | _ => _root_.Bool.false

#guard match fieldOne.run fixedNumericBytesContext [("value", .native 255)] with
  | .ok [("oneByte", .bytes 1 [255])] => _root_.Bool.true
  | _ => _root_.Bool.false
#guard match fieldOne.run fixedNumericBytesContext [("value", .native 256)] with
  | .error _ => _root_.Bool.true
  | _ => _root_.Bool.false
#guard match field31.run fixedNumericBytesContext
    [("value", .native Noctium.ScalarPolicy.maxUint)] with
  | .ok [("thirtyOneBytes", .bytes 31 bytes)] => bytes == List.replicate 31 255
  | _ => _root_.Bool.false
#guard match field31.run fixedNumericBytesContext
    [("value", .native (Noctium.ScalarPolicy.maxUint + 1))] with
  | .error _ => _root_.Bool.true
  | _ => _root_.Bool.false
#guard match fieldWide.run fixedNumericBytesContext [("value", .native 513)] with
  | .ok [
      ("wordBytes", .bytes 32 word),
      ("paddedThirtyThree", .bytes 33 padded33),
      ("paddedSixtyFour", .bytes 64 padded64)] =>
    word == [1, 2] ++ List.replicate 30 0 &&
      padded33 == [1, 2] ++ List.replicate 31 0 &&
      padded64 == [1, 2] ++ List.replicate 62 0
  | _ => _root_.Bool.false

/- error: toBytes requires a byte width from 1 through 1024 -/
#guard_msgs (substring := true) in
noctium_circuit rejectsZeroWidth where
  public value : Native
  output encoded : Bytes 0 := toBytes(value, 0)
end

/- error: toBytes requires Native or UInt -/
#guard_msgs (substring := true) in
noctium_circuit rejectsBool where
  public value : Bool
  output encoded : Bytes 1 := toBytes(value, 1)
end
