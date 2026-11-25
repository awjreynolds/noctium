import Noctium.Disclosure
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit fundedFourParentQualifiedCoinListOwnersInputs where
  public selectedOwner : Bytes32
  public selectedGroup : Bytes32
  public otherGroup : Bytes32
end

noctium_circuit fundedFourParentQualifiedCoinListInputs where
  public domain : Bytes32
  public owner : Bytes32
  public group : Bytes32
  private nonce : Bytes32
  private color : Bytes32
end

noctium_contract FundedFourParentQualifiedCoinList where
  tree pot : Bytes32 => struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }
  tree deepCoinLists : Bytes32 => Bytes32 => Bytes32 => Bytes32 => List struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry initializeOwners uses fundedFourParentQualifiedCoinListOwnersInputs where
    reset deepCoinLists[selectedOwner]
    reset deepCoinLists[selectedOwner][selectedGroup]
    reset deepCoinLists[selectedOwner][selectedGroup][selectedGroup]
    reset deepCoinLists[selectedOwner][selectedGroup][selectedGroup][selectedGroup]
    reset deepCoinLists[selectedOwner][selectedGroup][selectedGroup][otherGroup]
    reset deepCoinLists[selectedOwner][selectedGroup][otherGroup]
    reset deepCoinLists[selectedOwner][selectedGroup][otherGroup][selectedGroup]
    reset deepCoinLists[selectedOwner][otherGroup]
    reset deepCoinLists[selectedOwner][otherGroup][selectedGroup]
    reset deepCoinLists[selectedOwner][otherGroup][selectedGroup][selectedGroup]
  end

  entry tip uses fundedFourParentQualifiedCoinListInputs where
    readSelf as own
    mintShielded(domain, 5)
    receiveShieldedToMap(pot, disclose(nonce), disclose(color), 5)
    pushFrontCoin(deepCoinLists[owner][group][group][group],
      disclose(nonce), disclose(color), 5)
  end
end

private def fundedFourParentQualifiedCoinListEntry (name : String) : Entrypoint :=
  (FundedFourParentQualifiedCoinList.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

private def fundedFourParentQualifiedCoinListPath (owner : String) (groups : List String) :
    List String :=
  owner :: groups

private def fundedFourParentQualifiedCoinListPathNames (keys : List PathKey) : List String :=
  keys.map fun key =>
    match key with
    | .mk (.bytes 32) (.ref name) => name
    | _ => ""

#guard FundedFourParentQualifiedCoinList.entrypoints.length == 2
#guard ((fundedFourParentQualifiedCoinListEntry "initializeOwners").validate
  Capabilities.source FundedFourParentQualifiedCoinList.state).isOk
#guard ((fundedFourParentQualifiedCoinListEntry "tip").validate
  Capabilities.source FundedFourParentQualifiedCoinList.state).isOk
#guard (Disclosure.entrypoint
  (fundedFourParentQualifiedCoinListEntry "initializeOwners")).isOk
#guard (Disclosure.entrypoint
  (fundedFourParentQualifiedCoinListEntry "tip")).isOk

#guard (fundedFourParentQualifiedCoinListEntry "tip").circuit.inputs.map (·.name) ==
  ["domain", "owner", "group", "nonce", "color"]
#guard (fundedFourParentQualifiedCoinListEntry "tip").effectGuards.all Option.isNone

#guard ((fundedFourParentQualifiedCoinListEntry "initializeOwners").effects.filterMap
    fun (effect : Effect) =>
    match effect with
    | .emptyMapPath "deepCoinLists" keys =>
        some (_root_.Bool.false, fundedFourParentQualifiedCoinListPathNames keys)
    | .listReset "deepCoinLists" keys =>
        some (_root_.Bool.true, fundedFourParentQualifiedCoinListPathNames keys)
    | _ => none) == [
      (_root_.Bool.false, fundedFourParentQualifiedCoinListPath "selectedOwner" []),
      (_root_.Bool.false, fundedFourParentQualifiedCoinListPath "selectedOwner" ["selectedGroup"]),
      (_root_.Bool.false, fundedFourParentQualifiedCoinListPath "selectedOwner"
        ["selectedGroup", "selectedGroup"]),
      (_root_.Bool.true, fundedFourParentQualifiedCoinListPath "selectedOwner"
        ["selectedGroup", "selectedGroup", "selectedGroup"]),
      (_root_.Bool.true, fundedFourParentQualifiedCoinListPath "selectedOwner"
        ["selectedGroup", "selectedGroup", "otherGroup"]),
      (_root_.Bool.false, fundedFourParentQualifiedCoinListPath "selectedOwner"
        ["selectedGroup", "otherGroup"]),
      (_root_.Bool.true, fundedFourParentQualifiedCoinListPath "selectedOwner"
        ["selectedGroup", "otherGroup", "selectedGroup"]),
      (_root_.Bool.false, fundedFourParentQualifiedCoinListPath "selectedOwner" ["otherGroup"]),
      (_root_.Bool.false, fundedFourParentQualifiedCoinListPath "selectedOwner"
        ["otherGroup", "selectedGroup"]),
      (_root_.Bool.true, fundedFourParentQualifiedCoinListPath "selectedOwner"
        ["otherGroup", "selectedGroup", "selectedGroup"])
    ]

#guard match ((fundedFourParentQualifiedCoinListEntry "tip").effects.filterMap
    fun (effect : Effect) =>
    match effect with
    | .mintShielded domain amount => some (domain, amount)
    | _ => none) with
  | [(.ref "domain", .uint _ 5)] => Bool.true
  | _ => Bool.false

#guard match ((fundedFourParentQualifiedCoinListEntry "tip").effects.filterMap
    fun (effect : Effect) =>
    match effect with
    | .receiveShieldedToMap "pot" nonce color amount _ _ => some (nonce, color, amount)
    | _ => none) with
  | [(.disclose _ (.ref "nonce"), .disclose _ (.ref "color"), .uint _ 5)] => Bool.true
  | _ => Bool.false

#guard match ((fundedFourParentQualifiedCoinListEntry "tip").effects.filterMap
    fun (effect : Effect) =>
    match effect with
    | .pushFrontCoin "deepCoinLists" _ _ _ (.ref selfAddressName) keys =>
        some (selfAddressName, fundedFourParentQualifiedCoinListPathNames keys)
    | _ => none) with
  | [(selfAddressName,
      ["owner", "group", "group", "group"])] =>
      (fundedFourParentQualifiedCoinListEntry "tip").effects.any fun
        | .readContractAddress name => name == selfAddressName
        | _ => Bool.false
  | _ => Bool.false
