import Noctium.Authoring

open scoped Noctium

namespace ReadableNominalScalarSerialization

noctium_field_type Commitment := Field
noctium_field_type OtherField := Field
noctium_uint_type Quantity := UInt 7
noctium_uint_type OtherQuantity := UInt 7

noctium_witness_circuit transcode where
  private commitmentWire : Bytes 32
  private quantityWire : Bytes 1
  let commitment : Commitment := deserialize(Commitment, commitmentWire)
  let quantity : Quantity := deserialize(Quantity, quantityWire)
  output commitmentEncoding : Bytes 32 := disclose(serialize(commitment, 32))
  output quantityEncoding : Bytes 1 := disclose(serialize(quantity, 1))
end

noctium_contract Codec where
  entry transcode uses transcode where
    return commitment : Bytes 32 := commitmentEncoding
    return quantity : Bytes 1 := quantityEncoding
  end
end

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsRawField where
  public wire : Bytes 32
  output value : Native := deserialize(Commitment, wire)
end

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsOtherField where
  public wire : Bytes 32
  output value : OtherField := deserialize(Commitment, wire)
end

/- error: nominal UInt values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsOtherUInt where
  public wire : Bytes 1
  output value : OtherQuantity := deserialize(Quantity, wire)
end

end ReadableNominalScalarSerialization
