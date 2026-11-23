import Noctium.Disclosure
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit fundedSixParentQualifiedCoinMapsOwnersInputs where
  public selectedOwner : Bytes32
  public otherOwner : Bytes32
  public selectedGroup : Bytes32
  public otherGroup : Bytes32
end

noctium_circuit fundedSixParentQualifiedCoinMapsInputs where
  public domain : Bytes32
  public owner : Bytes32
  public group : Bytes32
  public key : Bytes32
  private nonce : Bytes32
  private color : Bytes32
end

noctium_contract FundedSixParentQualifiedCoinMaps where
  tree pot : Bytes32 => struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }
  tree coinSets : Bytes32 => Set struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }
  tree coinLists : Bytes32 => List struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }
  tree rootCoinMap : Bytes32 => struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }
  tree coinMaps : Bytes32 => Bytes32 => Bytes32 => Bytes32 => Bytes32 => Bytes32 => Bytes32 => struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry initializeOwners uses fundedSixParentQualifiedCoinMapsOwnersInputs where
    reset coinSets[selectedOwner]
    reset coinLists[selectedOwner]
    reset coinMaps[selectedOwner]
    reset coinSets[otherOwner]
    reset coinLists[otherOwner]
    reset coinMaps[otherOwner]
    reset coinMaps[selectedOwner][selectedGroup]
    reset coinMaps[selectedOwner][selectedGroup][selectedGroup]
    reset coinMaps[selectedOwner][selectedGroup][selectedGroup][selectedGroup]
    reset coinMaps[selectedOwner][selectedGroup][selectedGroup][selectedGroup][selectedGroup]
    reset coinMaps[selectedOwner][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup]
    reset coinMaps[selectedOwner][otherGroup]
    reset coinMaps[selectedOwner][otherGroup][otherGroup]
    reset coinMaps[selectedOwner][otherGroup][otherGroup][otherGroup]
    reset coinMaps[selectedOwner][otherGroup][otherGroup][otherGroup][otherGroup]
    reset coinMaps[selectedOwner][otherGroup][otherGroup][otherGroup][otherGroup][otherGroup]
    reset coinMaps[otherOwner][selectedGroup]
    reset coinMaps[otherOwner][selectedGroup][selectedGroup]
    reset coinMaps[otherOwner][selectedGroup][selectedGroup][selectedGroup]
    reset coinMaps[otherOwner][selectedGroup][selectedGroup][selectedGroup][selectedGroup]
    reset coinMaps[otherOwner][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup]
    reset coinMaps[otherOwner][otherGroup]
    reset coinMaps[otherOwner][otherGroup][otherGroup]
    reset coinMaps[otherOwner][otherGroup][otherGroup][otherGroup]
    reset coinMaps[otherOwner][otherGroup][otherGroup][otherGroup][otherGroup]
    reset coinMaps[otherOwner][otherGroup][otherGroup][otherGroup][otherGroup][otherGroup]
  end

  entry tip uses fundedSixParentQualifiedCoinMapsInputs where
    readSelf as own
    mintShielded(domain, 5)
    receiveShieldedToMap(pot, disclose(nonce), disclose(color), 5)
    insertShieldedCoinSet(coinSets[owner], disclose(nonce), disclose(color), 5)
    pushFrontCoin(coinLists[owner], disclose(nonce), disclose(color), 5)
    insertShieldedCoinMap(rootCoinMap, key, disclose(nonce), disclose(color), 5, true, own)
    insertShieldedCoinMap(
      coinMaps[owner][group][group][group][group][group], key,
      disclose(nonce), disclose(color), 5, true, own)
  end
end

private def fundedSixParentQualifiedCoinMapsEntry (name : String) : Entrypoint :=
  (FundedSixParentQualifiedCoinMaps.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

private def fundedSixParentCoinMapPrefix (owner group : String) (depth : Nat) : List String :=
  owner :: List.replicate depth group

#guard FundedSixParentQualifiedCoinMaps.entrypoints.length == 2
#guard ((fundedSixParentQualifiedCoinMapsEntry "initializeOwners").validate
  Capabilities.source FundedSixParentQualifiedCoinMaps.state).isOk
#guard ((fundedSixParentQualifiedCoinMapsEntry "tip").validate
  Capabilities.source FundedSixParentQualifiedCoinMaps.state).isOk
#guard (Disclosure.entrypoint
  (fundedSixParentQualifiedCoinMapsEntry "initializeOwners")).isOk
#guard (Disclosure.entrypoint
  (fundedSixParentQualifiedCoinMapsEntry "tip")).isOk

#guard (fundedSixParentQualifiedCoinMapsEntry "tip").circuit.inputs.map (·.name) ==
  ["domain", "owner", "group", "key", "nonce", "color"]

#guard ((fundedSixParentQualifiedCoinMapsEntry "initializeOwners").effects.filterMap
    (fun (effect : Effect) =>
      match effect with
      | .emptyMapPath "coinMaps" keys => some (keys.map fun key =>
          match key with
          | .mk (.bytes 32) (.ref name) => name
          | _ => "")
      | _ => none)) == [ fundedSixParentCoinMapPrefix "selectedOwner" "selectedGroup" 0
     , fundedSixParentCoinMapPrefix "otherOwner" "otherGroup" 0
     , fundedSixParentCoinMapPrefix "selectedOwner" "selectedGroup" 1
     , fundedSixParentCoinMapPrefix "selectedOwner" "selectedGroup" 2
     , fundedSixParentCoinMapPrefix "selectedOwner" "selectedGroup" 3
     , fundedSixParentCoinMapPrefix "selectedOwner" "selectedGroup" 4
     , fundedSixParentCoinMapPrefix "selectedOwner" "selectedGroup" 5
     , fundedSixParentCoinMapPrefix "selectedOwner" "otherGroup" 1
     , fundedSixParentCoinMapPrefix "selectedOwner" "otherGroup" 2
     , fundedSixParentCoinMapPrefix "selectedOwner" "otherGroup" 3
     , fundedSixParentCoinMapPrefix "selectedOwner" "otherGroup" 4
     , fundedSixParentCoinMapPrefix "selectedOwner" "otherGroup" 5
     , fundedSixParentCoinMapPrefix "otherOwner" "selectedGroup" 1
     , fundedSixParentCoinMapPrefix "otherOwner" "selectedGroup" 2
     , fundedSixParentCoinMapPrefix "otherOwner" "selectedGroup" 3
     , fundedSixParentCoinMapPrefix "otherOwner" "selectedGroup" 4
     , fundedSixParentCoinMapPrefix "otherOwner" "selectedGroup" 5
     , fundedSixParentCoinMapPrefix "otherOwner" "otherGroup" 1
     , fundedSixParentCoinMapPrefix "otherOwner" "otherGroup" 2
     , fundedSixParentCoinMapPrefix "otherOwner" "otherGroup" 3
     , fundedSixParentCoinMapPrefix "otherOwner" "otherGroup" 4
     , fundedSixParentCoinMapPrefix "otherOwner" "otherGroup" 5 ]

#guard match ((fundedSixParentQualifiedCoinMapsEntry "tip").effects.filterMap
    fun (effect : Effect) =>
    match effect with
    | .insertShieldedCoinMap .. => some effect
    | _ => none) with
  | [ .insertShieldedCoinMap "rootCoinMap" (.ref "key")
      (.disclose _ (.ref "nonce")) (.disclose _ (.ref "color")) _ (.bool Bool.true)
      (.ref "own") []
    , .insertShieldedCoinMap "coinMaps" (.ref "key")
      (.disclose _ (.ref "nonce")) (.disclose _ (.ref "color")) _ (.bool Bool.true)
      (.ref "own")
      [ .mk (.bytes 32) (.ref "owner")
      , .mk (.bytes 32) (.ref "group")
      , .mk (.bytes 32) (.ref "group")
      , .mk (.bytes 32) (.ref "group")
      , .mk (.bytes 32) (.ref "group")
      , .mk (.bytes 32) (.ref "group") ] ] => Bool.true
  | _ => Bool.false
#guard (fundedSixParentQualifiedCoinMapsEntry "tip").effectGuards.all Option.isNone
