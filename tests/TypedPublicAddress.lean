/- PublicAddress source constructors keep address roles tied to the existing
native unshielded-spend tag. The plan still carries the established Bytes32
recipient and Bool contract tag. -/
import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Compiler
import Noctium.Disclosure
import Noctium.Frontend
import Noctium.Midnight.PublicAddress

open Lean
open scoped Noctium
open Noctium

private def contractAddressWire := Midnight.ContractAddress.codec

private def userAddressWire := Midnight.UserAddress.codec

private def zswapCoinPublicKeyWire : Helpers.Wire.Codec := {
  payload := .structure "Noctium.Midnight.ZswapCoinPublicKey"
  frameBytes := 32
  composites := {structures := [{
    id := "Noctium.Midnight.ZswapCoinPublicKey"
    fields := [{name := "bytes", type := .bytes 32}]
  }]}
}

noctium_witness_circuit typedContractAddressInputs using contractAddressWire where
  private color : Bytes32
  private amount : UInt 128
  private unshielded : Bool
  private contractValue : Payload contractAddressWire
  output contractRecipient : Bytes32 := disclose(encode(contractAddressWire, contractValue))
end

noctium_witness_circuit typedUserAddressInputs using userAddressWire where
  private color : Bytes32
  private amount : UInt 128
  private unshielded : Bool
  private userValue : Payload userAddressWire
  output userRecipient : Bytes32 := disclose(encode(userAddressWire, userValue))
end

noctium_witness_circuit typedShieldedKeyInputs using zswapCoinPublicKeyWire where
  private color : Bytes32
  private amount : UInt 128
  private unshielded : Bool
  private shieldedKey : Payload zswapCoinPublicKeyWire
  output shieldedRecipient : Bytes32 := disclose(encode(zswapCoinPublicKeyWire, shieldedKey))
end

noctium_contract TypedPublicAddress where
  entry sendToContract uses typedContractAddressInputs
      arguments [color, amount, unshielded, contractValue] where
    claimUnshieldedCoinSpendTo(disclose(color), disclose(amount), disclose(unshielded),
      publicAddressContract(contractRecipient))
  end

  entry sendToContractRaw uses typedContractAddressInputs
      arguments [color, amount, unshielded, contractValue] where
    claimUnshieldedCoinSpend(disclose(color), disclose(amount), disclose(unshielded),
      true, contractRecipient)
  end

  entry sendToUser uses typedUserAddressInputs
      arguments [color, amount, unshielded, userValue] where
    claimUnshieldedCoinSpendTo(disclose(color), disclose(amount), disclose(unshielded),
      publicAddressUser(userRecipient))
  end

  entry sendToUserRaw uses typedUserAddressInputs
      arguments [color, amount, unshielded, userValue] where
    claimUnshieldedCoinSpend(disclose(color), disclose(amount), disclose(unshielded),
      false, userRecipient)
  end
end

private def typedPublicAddressEntry (name : String) : Entrypoint :=
  (TypedPublicAddress.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

private def typedPublicAddressPlanJson (name : String) : Except String Json := do
  let selectedEntry := typedPublicAddressEntry name
  let plan ← (Backend.Impact.lower TypedPublicAddress.state selectedEntry).mapError (·.message)
  pure (Compiler.nativePlanJson TargetProfile.selected321 `TypedPublicAddress
    TypedPublicAddress.state none selectedEntry plan)

private def planOperations (name : String) : Except String Json := do
  let plan ← typedPublicAddressPlanJson name
  plan.getObjVal? "operations"

#guard match (typedPublicAddressEntry "sendToContract").effects with
  | [.claimUnshieldedCoinSpend _ _ _ (.bool tag) (.ref recipient)] =>
      tag == Bool.true && recipient == "contractRecipient"
  | _ => Bool.false

#guard match (typedPublicAddressEntry "sendToUser").effects with
  | [.claimUnshieldedCoinSpend _ _ _ (.bool tag) (.ref recipient)] =>
      tag == Bool.false && recipient == "userRecipient"
  | _ => Bool.false

#guard match planOperations "sendToContract", planOperations "sendToContractRaw" with
  | .ok typed, .ok raw => typed == raw
  | _, _ => Bool.false

#guard match planOperations "sendToUser", planOperations "sendToUserRaw" with
  | .ok typed, .ok raw => typed == raw
  | _, _ => Bool.false

#guard (Disclosure.entrypoint (typedPublicAddressEntry "sendToContract")).isOk
#guard (Disclosure.entrypoint (typedPublicAddressEntry "sendToUser")).isOk
#guard (Backend.Zkir.lowerPrunedEntrypoint TypedPublicAddress.state
  (typedPublicAddressEntry "sendToContract")).isOk
#guard (Backend.Zkir.lowerPrunedEntrypoint TypedPublicAddress.state
  (typedPublicAddressEntry "sendToUser")).isOk

/-- PublicAddress.contract expects ContractAddress, got UserAddress -/
#guard_msgs (substring := true) in
noctium_contract WrongTypedPublicAddressBranch where
  entry send uses typedUserAddressInputs
      arguments [color, amount, unshielded, userValue] where
    claimUnshieldedCoinSpendTo(color, amount, unshielded, publicAddressContract(userRecipient))
  end
end

/-- PublicAddress.user expects UserAddress, got ZswapCoinPublicKey -/
#guard_msgs (substring := true) in
noctium_contract WrongShieldedPublicAddress where
  entry send uses typedShieldedKeyInputs
      arguments [color, amount, unshielded, shieldedKey] where
    claimUnshieldedCoinSpendTo(color, amount, unshielded, publicAddressUser(shieldedRecipient))
  end
end

/-- claimUnshieldedCoinSpend tag must be true for ContractAddress -/
#guard_msgs (substring := true) in
noctium_contract WrongRawContractAddressTag where
  entry send uses typedContractAddressInputs arguments [color, amount, unshielded, contractValue] where
    claimUnshieldedCoinSpend(disclose(color), disclose(amount), disclose(unshielded), false, contractRecipient)
  end
end

/-- claimUnshieldedCoinSpend tag must be false for UserAddress -/
#guard_msgs (substring := true) in
noctium_contract WrongRawUserAddressTag where
  entry send uses typedUserAddressInputs arguments [color, amount, unshielded, userValue] where
    claimUnshieldedCoinSpend(disclose(color), disclose(amount), disclose(unshielded), true, userRecipient)
  end
end

/-- claimUnshieldedCoinSpend cannot use a ZswapCoinPublicKey recipient -/
#guard_msgs (substring := true) in
noctium_contract WrongRawShieldedRecipient where
  entry send uses typedShieldedKeyInputs arguments [color, amount, unshielded, shieldedKey] where
    claimUnshieldedCoinSpend(disclose(color), disclose(amount), disclose(unshielded), false, shieldedRecipient)
  end
end
