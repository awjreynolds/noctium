import Noctium.Disclosure
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit fundedDeepQualifiedCoinMapsOwnersInputs where
  public selectedOwner : Bytes32
  public otherOwner : Bytes32
  public selectedGroup : Bytes32
  public otherGroup : Bytes32
end

noctium_circuit fundedDeepQualifiedCoinMapsInputs where
  public domain : Bytes32
  public owner : Bytes32
  public group : Bytes32
  public key : Bytes32
  private nonce : Bytes32
  private color : Bytes32
end

noctium_contract FundedDeepQualifiedCoinMaps where
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
  tree coinMaps : Bytes32 => Bytes32 => Bytes32 => struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry initializeOwners uses fundedDeepQualifiedCoinMapsOwnersInputs where
    reset coinSets[selectedOwner]
    reset coinLists[selectedOwner]
    reset coinMaps[selectedOwner]
    reset coinMaps[selectedOwner][selectedGroup]
    reset coinMaps[selectedOwner][otherGroup]
    reset coinSets[otherOwner]
    reset coinLists[otherOwner]
    reset coinMaps[otherOwner]
    reset coinMaps[otherOwner][selectedGroup]
    reset coinMaps[otherOwner][otherGroup]
  end

  entry tip uses fundedDeepQualifiedCoinMapsInputs where
    readSelf as own
    mintShielded(domain, 5)
    receiveShieldedToMap(pot, disclose(nonce), disclose(color), 5)
    insertShieldedCoinSet(coinSets[owner], disclose(nonce), disclose(color), 5)
    pushFrontCoin(coinLists[owner], disclose(nonce), disclose(color), 5)
    insertShieldedCoinMap(rootCoinMap, key, disclose(nonce), disclose(color), 5, true, own)
    insertShieldedCoinMap(coinMaps[owner][group], key, disclose(nonce), disclose(color), 5,
      true, own)
  end
end

private def fundedDeepQualifiedCoinMapsEntry (name : String) : Entrypoint :=
  (FundedDeepQualifiedCoinMaps.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

#guard FundedDeepQualifiedCoinMaps.entrypoints.length == 2
#guard ((fundedDeepQualifiedCoinMapsEntry "initializeOwners").validate
  Capabilities.source FundedDeepQualifiedCoinMaps.state).isOk
#guard ((fundedDeepQualifiedCoinMapsEntry "tip").validate
  Capabilities.source FundedDeepQualifiedCoinMaps.state).isOk
#guard (Disclosure.entrypoint
  (fundedDeepQualifiedCoinMapsEntry "initializeOwners")).isOk
#guard (Disclosure.entrypoint
  (fundedDeepQualifiedCoinMapsEntry "tip")).isOk

#guard match (fundedDeepQualifiedCoinMapsEntry "initializeOwners").effects with
  | [ .emptyMapPath "coinSets" [.mk (.bytes 32) (.ref "selectedOwner")]
    , .listReset "coinLists" [.mk (.bytes 32) (.ref "selectedOwner")]
    , .emptyMapPath "coinMaps" [.mk (.bytes 32) (.ref "selectedOwner")]
    , .emptyMapPath "coinMaps"
        [.mk (.bytes 32) (.ref "selectedOwner"), .mk (.bytes 32) (.ref "selectedGroup")]
    , .emptyMapPath "coinMaps"
        [.mk (.bytes 32) (.ref "selectedOwner"), .mk (.bytes 32) (.ref "otherGroup")]
    , .emptyMapPath "coinSets" [.mk (.bytes 32) (.ref "otherOwner")]
    , .listReset "coinLists" [.mk (.bytes 32) (.ref "otherOwner")]
    , .emptyMapPath "coinMaps" [.mk (.bytes 32) (.ref "otherOwner")]
    , .emptyMapPath "coinMaps"
        [.mk (.bytes 32) (.ref "otherOwner"), .mk (.bytes 32) (.ref "selectedGroup")]
    , .emptyMapPath "coinMaps"
        [.mk (.bytes 32) (.ref "otherOwner"), .mk (.bytes 32) (.ref "otherGroup")] ] => Bool.true
  | _ => Bool.false

#guard (fundedDeepQualifiedCoinMapsEntry "tip").circuit.inputs.map (·.name) ==
  ["domain", "owner", "group", "key", "nonce", "color"]
#guard match ((fundedDeepQualifiedCoinMapsEntry "tip").effects.filterMap
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
      [.mk (.bytes 32) (.ref "owner"), .mk (.bytes 32) (.ref "group")] ] => Bool.true
  | _ => Bool.false
#guard (fundedDeepQualifiedCoinMapsEntry "tip").effectGuards.all Option.isNone
