import Noctium.Backend.Impact
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

#guard match Backend.Impact.lower DeepBookedCoinMap.state deepBookedCoinMapStore with
  | .ok plan =>
      match plan.operations.filterMap fun operation =>
          match operation with
          | .insertShieldedCoinMap slot _ _ _ _ _ _ _ keys =>
              some (slot, keys, operation.fieldGroups.map List.length)
          | _ => none with
      | [(0, [_, _], [12, 6, 1, 6, 5, 11, 1, 2, 1, 1])] => Bool.true
      | _ => Bool.false
  | .error _ => Bool.false

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

private def deepBookedCoinMapWrapParents : Nat → LedgerValueType → LedgerValueType
  | 0, value => value
  | count + 1, value => .map (.bytes 32) (deepBookedCoinMapWrapParents count value)

private def deepBookedCoinMapParentState (parentCount : Nat) : List StateDecl :=
  DeepBookedCoinMap.state.map fun declaration =>
    match declaration.kind with
    | .tree (.map ownerKey (.map groupKey (.map leafKey (.composite environment recordType)))) =>
        let coinValue := .composite environment recordType
        let schema := .map ownerKey (.map groupKey
          (deepBookedCoinMapWrapParents (parentCount - 2) (.map leafKey coinValue)))
        {declaration with kind := .tree schema}
    | _ => declaration

private def deepBookedCoinMapParentKeys (count : Nat) : List PathKey :=
  List.replicate count (.mk (.bytes 32) (.bytes32Literal (List.replicate 32 0)))

private def deepBookedCoinMapInsertWithParents (count : Nat) : Entrypoint :=
  {deepBookedCoinMapStore with effects := deepBookedCoinMapStore.effects.map fun effect =>
    match effect with
      | .insertShieldedCoinMap state key nonce color amount isContract recipient _ =>
          .insertShieldedCoinMap state key nonce color amount isContract recipient
            (deepBookedCoinMapParentKeys count)
      | _ => effect}

private def deepBookedCoinMapFieldGroupOpcodes
    (groups : List (List Backend.Impact.Scalar)) : List Nat :=
  groups.map fun group => match group with
    | .native opcode :: _ => opcode
    | _ => 0

private def deepBookedCoinMapSixParentInsert : Entrypoint :=
  deepBookedCoinMapInsertWithParents 6

#guard (deepBookedCoinMapSixParentInsert.validate Capabilities.source
  (deepBookedCoinMapParentState 6)).isOk

#guard match Backend.Impact.lower (deepBookedCoinMapParentState 6)
    deepBookedCoinMapSixParentInsert with
  | .ok plan =>
      match plan.operations.filterMap fun operation =>
          match operation with
          | .insertShieldedCoinMap slot _ _ _ _ _ _ _ keys =>
              some (slot, keys, operation.fieldGroups)
          | _ => none with
      | [(slot, keys, groups)] =>
          slot == 0 && keys.length == 6 && groups.length == 51 &&
          groups.map List.length ==
            [1, 6, 5, 11, 1, 2, 1, 28, 6, 1, 1, 1,
              1, 24, 6, 1, 1, 1, 1, 20, 6, 1, 1, 1,
              1, 16, 6, 1, 1, 1, 1, 12, 6, 1, 1, 1,
              1, 8, 6, 1, 1, 1, 1, 4, 6, 1, 1, 1,
              5, 1, 1] &&
          deepBookedCoinMapFieldGroupOpcodes groups ==
            [0x32, 0x10, 0x61, 0x10, 0x40, 0x17,
              0x31, 0x56, 0x10, 0x40, 0x41, 0x91,
              0x31, 0x65, 0x10, 0x40, 0x41, 0xa1,
              0x31, 0x64, 0x10, 0x40, 0x41, 0xa1,
              0x31, 0x63, 0x10, 0x40, 0x41, 0xa1,
              0x31, 0x62, 0x10, 0x40, 0x41, 0xa1,
              0x31, 0x61, 0x10, 0x40, 0x41, 0xa1,
              0x31, 0x60, 0x10, 0x40, 0x41, 0xa1,
              0x10, 0x40, 0xa1]
      | _ => Bool.false
  | .error _ => Bool.false

private def deepBookedCoinMapFourteenParentInsert : Entrypoint :=
  deepBookedCoinMapInsertWithParents 14

#guard match Backend.Impact.lower (deepBookedCoinMapParentState 14)
    deepBookedCoinMapFourteenParentInsert with
  | .ok plan =>
      match plan.operations.filterMap fun operation =>
          match operation with
          | .insertShieldedCoinMap _ _ _ _ _ _ _ _ keys =>
              some (keys.length, operation.fieldGroups.length)
          | _ => none with
      | [(14, 99)] => Bool.true
      | _ => Bool.false
  | .error _ => Bool.false

private def deepBookedCoinMapFifteenParentInsert : Entrypoint :=
  deepBookedCoinMapInsertWithParents 15

#guard match deepBookedCoinMapFifteenParentInsert.validate Capabilities.source
    (deepBookedCoinMapParentState 15) with
  | .error diagnostic => diagnostic.message.contains "exceeds fourteen Maps"
  | .ok _ => Bool.false

#guard match Backend.Impact.lower (deepBookedCoinMapParentState 15)
    deepBookedCoinMapFifteenParentInsert with
  | .error diagnostic => diagnostic.message.contains "exceeds fourteen Maps"
  | .ok _ => Bool.false
