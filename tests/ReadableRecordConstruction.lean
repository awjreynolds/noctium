import Noctium.Frontend
import Noctium.Midnight.QualifiedShieldedCoinInfo

open scoped Noctium
open Noctium
open Noctium.Helpers
open Noctium.Types

namespace ReadableRecordConstruction

private def readingWire : Helpers.Wire.Codec := {
  payload := .structure "ReadableRecordConstruction.Reading"
  frameBytes := 34
  composites := {structures := [{
    id := "ReadableRecordConstruction.Reading"
    fields := [
      {name := "reading", type := .scalar .native},
      {name := "count", type := .scalar (.uint 255)},
      {name := "active", type := .scalar .bool}
    ]
  }]}
}

noctium_witness observeActive(marker : Native) : Bool
noctium_witness observeCount(marker : Native) : UInt 8
noctium_witness observeReading(marker : Native) : Native

noctium_witness_circuit build using readingWire where
  public seed : Native
  let constructed := record(Payload readingWire, {
    active := witness observeActive(add(seed, 1)),
    count := witness observeCount(add(seed, 2)),
    reading := witness observeReading(add(seed, 3))
  })
  output result := disclose(constructed)
end

#guard build.__program.composites.structures.any fun declaration =>
  declaration.id == "ReadableRecordConstruction.Reading" &&
  declaration.fields.map (fun field => (field.name, field.type)) == [
    ("reading", .scalar .native), ("count", .scalar (.uint 255)),
    ("active", .scalar .bool)]

#guard (Noctium.Witness.compile build.__program
  "noctium.witness-circuit.ReadableRecordConstruction.build.v1").isOk

/- error: unknown record field 'x' -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsUnknownField using readingWire where
  public seed : Native
  output result := disclose(record(Payload readingWire, {
    active := true, count := uint(0), reading := 0, x := 0
  }))
end

/- error: duplicate record field 'count' -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsDuplicateField using readingWire where
  public seed : Native
  output result := disclose(record(Payload readingWire, {
    active := true, count := uint(0), count := uint(1), reading := 0
  }))
end

/- error: missing record field 'active' -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsMissingField using readingWire where
  public seed : Native
  output result := disclose(record(Payload readingWire, {
    count := uint(0), reading := 0
  }))
end

/- error: readable witness expression type mismatch -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsBadFieldType using readingWire where
  public seed : Native
  output result := disclose(record(Payload readingWire, {
    active := true, count := true, reading := 0
  }))
end

/- error: undisclosed private -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsUndisclosedPrivate using readingWire where
  public seed : Native
  output result := record(Payload readingWire, {
    active := witness observeActive(add(seed, 1)),
    count := witness observeCount(add(seed, 2)),
    reading := witness observeReading(add(seed, 3))
  })
end

end ReadableRecordConstruction

private def qualifiedCoinWire := Noctium.Midnight.QualifiedShieldedCoinInfo.codec

noctium_witness_circuit buildsQualifiedCoin using qualifiedCoinWire where
  public nonce : Bytes32
  public color : Bytes32
  public amount : UInt 128
  public position : UInt 64
  output result := record(Payload qualifiedCoinWire, {
    mt_index := position, value := amount, color := color, nonce := nonce
  })
end

noctium_contract ReadableRecordConstruction where
  entry build uses ReadableRecordConstruction.build where
    return result
  end
end
