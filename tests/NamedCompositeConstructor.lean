import Noctium.Frontend

open scoped Noctium
open Noctium
open Noctium.Helpers
open Noctium.Types

private def seedWire : Helpers.Wire.Codec := {
  payload := .structure "NamedCompositeConstructor.Payload"
  frameBytes := 6
  composites := {structures := [
    {
      id := "NamedCompositeConstructor.Position"
      fields := [
        {name := "amount", type := .scalar (.uint 255)},
        {name := "enabled", type := .scalar .bool},
        {name := "ignored", type := .scalar (.uint 255)}
      ]
    },
    {
      id := "NamedCompositeConstructor.Payload"
      fields := [
        {name := "position", type := .structure "NamedCompositeConstructor.Position"},
        {name := "extras", type := .tuple [.scalar (.uint 65535), .scalar (.uint 255)]}
      ]
    }
  ]}
}

noctium_circuit inspectNoInputs where
end

noctium_contract NamedCompositeConstructor where
  cell amount : UInt 8
  cell enabled : Bool
  cell count : UInt 16

  constructor(seed : Payload seedWire as {
    position := {amount := seededAmount, enabled := seededEnabled, ignored := _},
    extras := [seededCount, _]
  }) where
    initialize amount := seededAmount
    initialize enabled := seededEnabled
    initialize count := seededCount
  end

  entry inspect uses inspectNoInputs arguments [] where
    read amount as amountValue
    read enabled as enabledValue
    read count as countValue
    return amountResult : UInt 8 := amountValue
    return enabledResult : Bool := enabledValue
    return countResult : UInt 16 := countValue
  end
end

/- error: unknown constructor record pattern field -/
#guard_msgs (substring := true) in
noctium_contract RejectsUnknownNamedConstructorField where
  constructor(seed : Payload seedWire as {position := {missing := _}}) where
  end
end
