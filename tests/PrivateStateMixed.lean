import Noctium.Frontend

open scoped Noctium

namespace PrivateStateMixed

noctium_field_type Amount := Field
noctium_field_type Count := Field

private def receiptWire : Noctium.Helpers.Wire.Codec := {
  payload := .structure "MeterReceipt"
  frameBytes := 2
  composites := {structures := [{id := "MeterReceipt", fields := [
    {name := "amount", type := .scalar (.uint 255)},
    {name := "okay", type := .scalar .bool}
  ]}]}
}

noctium_private_state Wallet where
  cell saved : UInt 8
  cell enabled : Bool
  cell secret : JubjubScalar
  cell recipient : JubjubPoint
  cell receipt : Payload receiptWire
  cell amount : Amount
end

noctium_witness_circuit consume using receiptWire where
  public expected : UInt 8
  private replacement : JubjubScalar
  private replacementAmount : Amount
  read private Wallet.saved as previous
  read private Wallet.enabled as enabled
  read private Wallet.secret as secret
  read private Wallet.recipient as recipient
  read private Wallet.receipt as receipt
  read private Wallet.amount as previousAmount
  prove enabled
  prove eq(expected, add(previous, uint(1)))
  prove eq(jubjubMulGenerator(secret), recipient)
  prove eq(field(receipt, amount), expected)
  prove field(receipt, okay)
  stage Wallet.saved := expected
  stage Wallet.enabled := false
  stage Wallet.secret := replacement
  stage Wallet.recipient := jubjubMulGenerator(replacement)
  stage Wallet.receipt := record(Payload receiptWire, {amount := uint(3), okay := false})
  stage Wallet.amount := add(previousAmount, replacementAmount)
  read private Wallet.receipt as stagedReceipt
  read private Wallet.amount as stagedAmount
  prove eq(field(stagedReceipt, amount), uint(3))
  prove eq(field(stagedReceipt, okay), false)
  prove eq(cast(Native, stagedAmount), cast(Native, add(previousAmount, replacementAmount)))
  output approved : Bool := disclose(field(receipt, okay))
  output units : UInt 8 := expected
  output releasedAmount : Native := cast(Native, disclose(stagedAmount))
end

noctium_contract Meter where
  cell count : UInt 8
  entry advance uses consume where
    write count := units
    return accepted : Bool := approved
    return amountResult : Native := releasedAmount
  end
end

noctium_witness_circuit acceptsExplicitNativePrivateFieldStage where
  private raw : Native
  stage Wallet.amount := cast(Amount, raw)
end

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsImplicitNativePrivateFieldStage where
  private raw : Native
  stage Wallet.amount := raw
end

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsDistinctAliasPrivateFieldStage where
  private count : Count
  stage Wallet.amount := count
end

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsUndisclosedPrivateFieldOutput where
  read private Wallet.amount as amount
  output leaked : Native := amount
end

/-- error: private stage value does not match its declared Payload type -/
#guard_msgs in
noctium_witness_circuit badReceiptStage using receiptWire where
  stage Wallet.receipt := true
end

private def stageOnly : Noctium.Helpers.Program := {
  composites := receiptWire.composites
  declarations := [{
    id := ⟨0, 0⟩, name := "main", result := .unit
    body := [.stage "private" "receipt" (.composite receiptWire.payload)
      (.composite receiptWire.payload [.uint 255 3, .bool Bool.false]), .return none]
  }]
  exports := [{name := "main", target := ⟨0, 0⟩}]
}

#guard match Noctium.Control.compile stageOnly "main" with
  | .ok plan => (plan.getObjVal? "schemaVersion").toOption == some (Lean.toJson (2 : Nat))
  | .error _ => Bool.false

end PrivateStateMixed
