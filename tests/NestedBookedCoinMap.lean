import Noctium.Disclosure
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit nestedBookedCoinMapOwnerInputs where
  public owner : Bytes32
end

noctium_circuit nestedBookedCoinMapInputs where
  public owner : Bytes32
  public key : Bytes32
  private nonce : Bytes32
  private color : Bytes32
  private amount : UInt 128
  private isContract : Bool
  private recipient : Bytes32
end

noctium_contract NestedBookedCoinMap where
  tree coins : Bytes32 => Bytes32 => struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry initializeOwner uses nestedBookedCoinMapOwnerInputs where
    reset coins[owner]
  end

  entry store uses nestedBookedCoinMapInputs where
    insertShieldedCoinMap(coins[owner], key, disclose(nonce), disclose(color),
      disclose(amount), disclose(isContract), disclose(recipient))
  end
end

private def nestedBookedCoinMapEntry (name : String) : Entrypoint :=
  (NestedBookedCoinMap.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

private def nestedBookedCoinMapStore : Entrypoint :=
  nestedBookedCoinMapEntry "store"

#guard nestedBookedCoinMapStore.name == "store"
#guard nestedBookedCoinMapStore.circuit.inputs.map (·.name) ==
  ["owner", "key", "nonce", "color", "amount", "isContract", "recipient"]
#guard ((nestedBookedCoinMapEntry "initializeOwner").validate
  Capabilities.source NestedBookedCoinMap.state).isOk
#guard (nestedBookedCoinMapStore.validate
  Capabilities.source NestedBookedCoinMap.state).isOk
#guard (Disclosure.entrypoint nestedBookedCoinMapStore).isOk

#guard match NestedBookedCoinMap.state with
  | [{kind := .tree (.map (.bytes 32) (.map (.bytes 32)
      (.composite environment recordType))), ..}] =>
      (LedgerValueType.shieldedCoinRecordFields environment recordType).isOk
  | _ => Bool.false

#guard match (nestedBookedCoinMapEntry "initializeOwner").effects with
  | [.emptyMapPath "coins" [.mk (.bytes 32) (.ref "owner")]] => Bool.true
  | _ => Bool.false

#guard match nestedBookedCoinMapStore.effects with
  | [.insertShieldedCoinMap "coins" (.ref "key") _ _ _ _ _
      [.mk (.bytes 32) (.ref "owner")]] => Bool.true
  | _ => Bool.false

private def nestedBookedCoinMapPrivateOwner : Entrypoint :=
  {nestedBookedCoinMapStore with circuit :=
    {nestedBookedCoinMapStore.circuit with inputs :=
      nestedBookedCoinMapStore.circuit.inputs.map fun input =>
        if input.name == "owner" then {input with visibility := .«private»}
        else input}}

#guard match Disclosure.entrypoint nestedBookedCoinMapPrivateOwner with
  | .error diagnostic =>
      diagnostic.message.contains "undisclosed private parameter 'owner'"
  | .ok _ => Bool.false

private def nestedBookedCoinMapWrongOwnerKey : Entrypoint :=
  {nestedBookedCoinMapStore with effects := nestedBookedCoinMapStore.effects.map fun effect =>
    match effect with
      | .insertShieldedCoinMap state key nonce color amount isContract recipient _ =>
          .insertShieldedCoinMap state key nonce color amount isContract recipient
            [.mk .native (.native 0)]
      | _ => effect}

#guard match nestedBookedCoinMapWrongOwnerKey.validate
    Capabilities.source NestedBookedCoinMap.state with
  | .error diagnostic => diagnostic.message.contains "nested map key type mismatch"
  | .ok _ => Bool.false

private def nestedBookedCoinMapWrongOwnerSchema : List StateDecl :=
  NestedBookedCoinMap.state.map fun declaration =>
    match declaration.kind with
    | .tree (.map _ nested) =>
        {declaration with kind := .tree (.map .native nested)}
    | _ => declaration

#guard match nestedBookedCoinMapStore.validate
    Capabilities.source nestedBookedCoinMapWrongOwnerSchema with
  | .error diagnostic => diagnostic.message.contains "nested map key type mismatch"
  | .ok _ => Bool.false

private def nestedBookedCoinMapWrongValueState : List StateDecl :=
  NestedBookedCoinMap.state.map fun declaration =>
    match declaration.kind with
    | .tree (.map outerKey (.map innerKey (.composite ..))) =>
        {declaration with kind := .tree (.map outerKey (.map innerKey (.scalar .native)))}
    | _ => declaration

#guard match nestedBookedCoinMapStore.validate
    Capabilities.source nestedBookedCoinMapWrongValueState with
  | .error diagnostic =>
      diagnostic.message.contains "Bytes32-keyed Map with a qualified coin record value"
  | .ok _ => Bool.false
