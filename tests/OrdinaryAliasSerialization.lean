import Noctium.Frontend
import Noctium.Semantics
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium

namespace OrdinaryAliasSerialization

noctium_field_type Amount := Field
noctium_field_type Count := Field
noctium_uint_type Small := UInt 7
noctium_uint_type OtherSmall := UInt 7

noctium_circuit fieldAliasRoundTrip where
  private amount : Amount
  let encoded : Bytes32 := serialize(amount, 32)
  output wire : Bytes32 := disclose(encoded)
  output result : Amount := disclose(deserialize(Amount, encoded))
end

noctium_circuit fieldAliasDecode where
  private encoded : Bytes32
  output result : Amount := disclose(deserialize(Amount, encoded))
end

noctium_circuit uintAliasRoundTrip where
  private amount : Small
  let encoded : Bytes 1 := serialize(amount, 1)
  output wire : Bytes 1 := disclose(encoded)
  output result : Small := disclose(deserialize(Small, encoded))
end

noctium_circuit uintAliasDecode where
  private encoded : Bytes 1
  output result : Small := disclose(deserialize(Small, encoded))
end

noctium_circuit rawFieldFromNominalWire where
  private amount : Amount
  output result : Native := disclose(deserialize(Native, serialize(amount, 32)))
end

noctium_circuit rawUIntFromNominalWire where
  private amount : Small
  output result : UInt 7 := disclose(deserialize(UInt 7, serialize(amount, 1)))
end

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_circuit rejectsFieldAliasRebrand where
  private encoded : Bytes32
  output result : Count := disclose(deserialize(Amount, encoded))
end

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_circuit rejectsFieldAliasErase where
  private encoded : Bytes32
  output result : Native := disclose(deserialize(Amount, encoded))
end

/- error: nominal UInt values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_circuit rejectsUIntAliasRebrand where
  private encoded : Bytes 1
  output result : OtherSmall := disclose(deserialize(Small, encoded))
end

/- error: nominal UInt values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_circuit rejectsUIntAliasErase where
  private encoded : Bytes 1
  output result : UInt 7 := disclose(deserialize(Small, encoded))
end

noctium_contract Codec where
  entry amountRoundTrip uses fieldAliasRoundTrip where
    return serialized : Bytes32 := wire
    return decoded : Amount := result
  end
  entry smallRoundTrip uses uintAliasRoundTrip where
    return serialized : Bytes 1 := wire
    return decoded : Small := result
  end
  entry rawFieldFromNominalWire uses rawFieldFromNominalWire where
    return decoded : Native := result
  end
  entry rawUIntFromNominalWire uses rawUIntFromNominalWire where
    return decoded : UInt 7 := result
  end
end

#guard Codec.entrypoints.all fun entrypoint =>
  match Backend.Zkir.lowerEntrypoint Codec.state entrypoint with
  | .ok _ => Bool.true
  | .error _ => Bool.false

private def aliasSerializationContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by alias serialization"
}

private def littleEndian (width value : Nat) : List Nat :=
  (List.range width).map fun index => value / (256 ^ index) % 256

#guard match fieldAliasRoundTrip.run aliasSerializationContext [("amount", .native 42)] with
  | .ok [("wire", .bytes 32 bytes), ("result", .native 42)] =>
    bytes == littleEndian 32 42
  | _ => Bool.false
#guard match fieldAliasDecode.run aliasSerializationContext
    [("encoded", .bytes 32 (littleEndian 32 (Field.modulus - 1)))] with
  | .ok [("result", .native value)] => value == Field.modulus - 1
  | _ => Bool.false
#guard match fieldAliasDecode.run aliasSerializationContext
    [("encoded", .bytes 32 (littleEndian 32 Field.modulus))] with
  | .error _ => Bool.true
  | _ => Bool.false
#guard match uintAliasRoundTrip.run aliasSerializationContext [("amount", .uint 127 42)] with
  | .ok [("wire", .bytes 1 [42]), ("result", .uint 127 42)] => Bool.true
  | _ => Bool.false
#guard match uintAliasDecode.run aliasSerializationContext [("encoded", .bytes 1 [127])] with
  | .ok [("result", .uint 127 127)] => Bool.true
  | _ => Bool.false
#guard match uintAliasDecode.run aliasSerializationContext [("encoded", .bytes 1 [128])] with
  | .error _ => Bool.true
  | _ => Bool.false

end OrdinaryAliasSerialization
