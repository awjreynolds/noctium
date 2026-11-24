import Noctium.Frontend

open scoped Noctium
open Noctium

namespace NominalUIntMaybeFixture

noctium_uint_type Amount := UInt 8
noctium_uint_type Other := UInt 8

noctium_witness_circuit nominalUIntMaybe where
  private amount : Amount
  let presentAmount := some(amount)
  let absentAmount := none(Amount)
  let absentOther := none(Other)
  let roundtrip : Amount := field(presentAmount, value)
  let canonical : Amount := field(absentAmount, value)
  let wrappedTuple := some(tuple(amount))
  let wrappedMaybe := tuple(presentAmount)
  let fromTuple : Amount := elementAt(field(wrappedTuple, value), 0)
  let fromMaybe : Amount := field(elementAt(wrappedMaybe, 0), value)
  prove eq(roundtrip, amount)
  prove eq(fromTuple, amount)
  prove eq(fromMaybe, amount)
  prove eq(canonical, cast(Amount, uint(0)))
  output presentChoice := disclose(presentAmount)
  output absentChoice := absentAmount
  output otherAbsent := absentOther
end

noctium_contract NominalUIntMaybeNative where
  entry consume uses nominalUIntMaybe arguments [amount] where
    return presentChoice
    return absentChoice
    return otherAbsent
  end
end

private def payloadIdentity (name : String) : List NominalUIntType :=
  NominalUIntMaybeNative.entrypoints.flatMap fun operation =>
    operation.returnViews.filter (·.name == name) |>.flatMap fun view =>
      view.nominalUIntFields.filter (·.path == ["value"]) |>.map (·.nominalUInt)

#guard payloadIdentity "presentChoice" == [Amount.nominalType] &&
  payloadIdentity "absentChoice" == [Amount.nominalType] &&
  payloadIdentity "otherAbsent" == [Other.nominalType]

/- error: nominal UInt values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsOther where
  public amount : Amount
  let constructed := tuple(some(amount))
  let wrong : Other := field(elementAt(constructed, 0), value)
  output result := wrong
end

end NominalUIntMaybeFixture
