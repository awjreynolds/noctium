import Noctium.Frontend

open scoped Noctium

namespace PrivateStateMixed

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
end

noctium_witness_circuit consume using receiptWire where
  public expected : UInt 8
  private replacement : JubjubScalar
  read private Wallet.saved as previous
  read private Wallet.enabled as enabled
  read private Wallet.secret as secret
  read private Wallet.recipient as recipient
  read private Wallet.receipt as receipt
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
  read private Wallet.receipt as stagedReceipt
  prove eq(field(stagedReceipt, amount), uint(3))
  prove eq(field(stagedReceipt, okay), false)
  output approved : Bool := disclose(field(receipt, okay))
  output units : UInt 8 := expected
end

noctium_contract Meter where
  cell count : UInt 8
  entry advance uses consume where
    write count := units
    return accepted : Bool := approved
  end
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
