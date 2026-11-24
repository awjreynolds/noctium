import Noctium.Frontend
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium

noctium_circuit opaqueStringEquality where
  public a : OpaqueString
  public b : OpaqueString
  output equalValue : Bool := eq(a, b)
end

noctium_witness_circuit opaqueBytesEquality where
  public a : OpaqueBytes
  public b : OpaqueBytes
  output equalValue : Bool := eq(a, b)
end

noctium_contract OpaqueEquality where
  cell last : Bool
  entry recordString uses opaqueStringEquality where
    write last := equalValue
    return same : Bool := equalValue
  end
  entry recordBytes uses opaqueBytesEquality where
    write last := equalValue
    return same : Bool := equalValue
  end
end

#guard OpaqueEquality.entrypoints.all fun operation =>
  (Backend.Zkir.lowerEntrypoint OpaqueEquality.state operation).isOk

/-- readable witness expression type mismatch -/
#guard_msgs (substring := true) in
noctium_witness_circuit mixedOpaqueEquality where
  public a : OpaqueString
  public b : OpaqueBytes
  output same : Bool := eq(a, b)
end

/-- undisclosed private parameter 'a' -/
#guard_msgs (substring := true) in
noctium_witness_circuit hiddenOpaqueEquality where
  private a : OpaqueBytes
  public b : OpaqueBytes
  output same : Bool := eq(a, b)
end
