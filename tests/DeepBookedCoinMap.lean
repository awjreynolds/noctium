import Noctium.Disclosure
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit deepBookedCoinMapParentInputs where
  public owner : Bytes32
  public group : Bytes32
end

noctium_circuit deepBookedCoinMapInputs where
  public owner : Bytes32
  public group : Bytes32
  public key : Bytes32
  private nonce : Bytes32
  private color : Bytes32
  private amount : UInt 128
  private isContract : Bool
  private recipient : Bytes32
end

noctium_contract DeepBookedCoinMap where
  tree coins : Bytes32 => Bytes32 => Bytes32 => struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry initializeParent uses deepBookedCoinMapParentInputs where
    reset coins[owner][group]
  end

  entry store uses deepBookedCoinMapInputs where
    insertShieldedCoinMap(coins[owner][group], key, disclose(nonce), disclose(color),
      disclose(amount), disclose(isContract), disclose(recipient))
  end
end

private def deepBookedCoinMapEntry (name : String) : Entrypoint :=
  (DeepBookedCoinMap.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

private def deepBookedCoinMapStore : Entrypoint := deepBookedCoinMapEntry "store"

#guard deepBookedCoinMapStore.circuit.inputs.map (·.name) ==
  ["owner", "group", "key", "nonce", "color", "amount", "isContract", "recipient"]
#guard ((deepBookedCoinMapEntry "initializeParent").validate
  Capabilities.source DeepBookedCoinMap.state).isOk
#guard (deepBookedCoinMapStore.validate Capabilities.source DeepBookedCoinMap.state).isOk
#guard (Disclosure.entrypoint deepBookedCoinMapStore).isOk

#guard match DeepBookedCoinMap.state with
  | [{kind := .tree (.map (.bytes 32) (.map (.bytes 32)
      (.map (.bytes 32) (.composite environment recordType)))), ..}] =>
      (LedgerValueType.shieldedCoinRecordFields environment recordType).isOk
  | _ => Bool.false

#guard match (deepBookedCoinMapEntry "initializeParent").effects with
  | [.emptyMapPath "coins"
      [.mk (.bytes 32) (.ref "owner"), .mk (.bytes 32) (.ref "group")]] => Bool.true
  | _ => Bool.false

#guard match deepBookedCoinMapStore.effects with
  | [.insertShieldedCoinMap "coins" (.ref "key") _ _ _ _ _
      [.mk (.bytes 32) (.ref "owner"), .mk (.bytes 32) (.ref "group")]] => Bool.true
  | _ => Bool.false

private def deepBookedCoinMapWrongParentKey : Entrypoint :=
  {deepBookedCoinMapStore with effects := deepBookedCoinMapStore.effects.map fun effect =>
    match effect with
      | .insertShieldedCoinMap state key nonce color amount isContract recipient _ =>
          .insertShieldedCoinMap state key nonce color amount isContract recipient
            [.mk .native (.native 1), .mk (.bytes 32) (.ref "group")]
      | _ => effect}

#guard match deepBookedCoinMapWrongParentKey.validate
    Capabilities.source DeepBookedCoinMap.state with
  | .error diagnostic => diagnostic.message.contains "nested map key type mismatch"
  | .ok _ => Bool.false

private def deepBookedCoinMapNativeParentState : List StateDecl :=
  DeepBookedCoinMap.state.map fun declaration =>
    match declaration.kind with
    | .tree (.map _ nested) =>
        {declaration with kind := .tree (.map .native nested)}
    | _ => declaration

private def deepBookedCoinMapNativeParentKey : Entrypoint :=
  {deepBookedCoinMapStore with effects := deepBookedCoinMapStore.effects.map fun effect =>
    match effect with
      | .insertShieldedCoinMap state key nonce color amount isContract recipient _ =>
          .insertShieldedCoinMap state key nonce color amount isContract recipient
            [.mk .native (.native 1), .mk (.bytes 32) (.ref "group")]
      | _ => effect}

#guard match deepBookedCoinMapNativeParentKey.validate
    Capabilities.source deepBookedCoinMapNativeParentState with
  | .error diagnostic => diagnostic.message.contains "parent keys must be Bytes32"
  | .ok _ => Bool.false

private def deepBookedCoinMapWrongCoinLayout : List StateDecl :=
  DeepBookedCoinMap.state.map fun declaration =>
    match declaration.kind with
    | .tree (.map ownerKey (.map groupKey (.map leafKey (.composite environment recordType)))) =>
        let structures := environment.structures.map fun recordDecl =>
          {recordDecl with fields := recordDecl.fields.map fun field =>
            if field.name == "value" then
              {field with type := .scalar (.uint (2 ^ 64 - 1))}
            else field}
        let coinValue := .composite {environment with structures := structures} recordType
        let schema := .map ownerKey (.map groupKey (.map leafKey coinValue))
        {declaration with kind := .tree schema}
    | _ => declaration

#guard match deepBookedCoinMapStore.validate
    Capabilities.source deepBookedCoinMapWrongCoinLayout with
  | .error diagnostic => diagnostic.message.contains "must be flat nonce: Bytes32"
  | .ok _ => Bool.false

private def deepBookedCoinMapSixParentState : List StateDecl :=
  DeepBookedCoinMap.state.map fun declaration =>
    match declaration.kind with
    | .tree (.map ownerKey (.map groupKey (.map leafKey (.composite environment recordType)))) =>
        let coinValue := .composite environment recordType
        let schema := .map ownerKey (.map groupKey
          (.map (.bytes 32) (.map (.bytes 32) (.map (.bytes 32)
            (.map (.bytes 32) (.map leafKey coinValue))))))
        {declaration with kind := .tree schema}
    | _ => declaration

private def deepBookedCoinMapSixParentKeys : List PathKey :=
  List.replicate 6 (.mk (.bytes 32) (.bytes32Literal []))

private def deepBookedCoinMapSixParentInsert : Entrypoint :=
  {deepBookedCoinMapStore with effects := deepBookedCoinMapStore.effects.map fun effect =>
    match effect with
      | .insertShieldedCoinMap state key nonce color amount isContract recipient _ =>
          .insertShieldedCoinMap state key nonce color amount isContract recipient
            deepBookedCoinMapSixParentKeys
      | _ => effect}

#guard match deepBookedCoinMapSixParentInsert.validate
    Capabilities.source deepBookedCoinMapSixParentState with
  | .error diagnostic => diagnostic.message.contains "exceeds five Maps"
  | .ok _ => Bool.false
