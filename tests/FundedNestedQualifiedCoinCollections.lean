import Noctium.Disclosure
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit fundedNestedQualifiedCoinCollectionsOwnersInputs where
  public selectedOwner : Bytes32
  public otherOwner : Bytes32
end

noctium_circuit fundedNestedQualifiedCoinCollectionsInputs where
  public domain : Bytes32
  public owner : Bytes32
  private nonce : Bytes32
  private color : Bytes32
end

noctium_contract FundedNestedQualifiedCoinCollections where
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

  entry initializeOwners uses fundedNestedQualifiedCoinCollectionsOwnersInputs where
    reset coinSets[selectedOwner]
    reset coinLists[selectedOwner]
    reset coinSets[otherOwner]
    reset coinLists[otherOwner]
  end

  entry tip uses fundedNestedQualifiedCoinCollectionsInputs where
    mintShielded(domain, 5)
    receiveShieldedToMap(pot, disclose(nonce), disclose(color), 5)
    insertShieldedCoinSet(coinSets[owner], disclose(nonce), disclose(color), 5)
    pushFrontCoin(coinLists[owner], disclose(nonce), disclose(color), 5)
  end
end

private def fundedNestedQualifiedCoinCollectionsEntry (name : String) : Entrypoint :=
  (FundedNestedQualifiedCoinCollections.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

#guard FundedNestedQualifiedCoinCollections.entrypoints.length == 2
#guard ((fundedNestedQualifiedCoinCollectionsEntry "initializeOwners").validate
  Capabilities.source FundedNestedQualifiedCoinCollections.state).isOk
#guard ((fundedNestedQualifiedCoinCollectionsEntry "tip").validate
  Capabilities.source FundedNestedQualifiedCoinCollections.state).isOk
#guard (Disclosure.entrypoint
  (fundedNestedQualifiedCoinCollectionsEntry "initializeOwners")).isOk
#guard (Disclosure.entrypoint
  (fundedNestedQualifiedCoinCollectionsEntry "tip")).isOk

#guard match (fundedNestedQualifiedCoinCollectionsEntry "initializeOwners").effects with
  | [ .emptyMapPath "coinSets" [.mk (.bytes 32) (.ref "selectedOwner")]
    , .listReset "coinLists" [.mk (.bytes 32) (.ref "selectedOwner")]
    , .emptyMapPath "coinSets" [.mk (.bytes 32) (.ref "otherOwner")]
    , .listReset "coinLists" [.mk (.bytes 32) (.ref "otherOwner")] ] => Bool.true
  | _ => Bool.false

#guard (fundedNestedQualifiedCoinCollectionsEntry "tip").effectGuards.all Option.isNone
