import Noctium.Disclosure
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit fundedTwoParentQualifiedCoinListOwnersInputs where
  public selectedOwner : Bytes32
  public otherOwner : Bytes32
  public selectedGroup : Bytes32
  public otherGroup : Bytes32
end

noctium_circuit fundedTwoParentQualifiedCoinListInputs where
  public domain : Bytes32
  public owner : Bytes32
  public group : Bytes32
  public key : Bytes32
  private nonce : Bytes32
  private color : Bytes32
end

noctium_contract FundedTwoParentQualifiedCoinList where
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
  tree deepCoinLists : Bytes32 => Bytes32 => List struct Coin {
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

  entry initializeOwners uses fundedTwoParentQualifiedCoinListOwnersInputs where
    reset coinSets[selectedOwner]
    reset coinLists[selectedOwner]
    reset coinSets[otherOwner]
    reset coinLists[otherOwner]
    reset deepCoinLists[selectedOwner]
    reset deepCoinLists[selectedOwner][selectedGroup]
    reset deepCoinLists[selectedOwner][otherGroup]
    reset deepCoinLists[otherOwner]
    reset deepCoinLists[otherOwner][selectedGroup]
    reset deepCoinLists[otherOwner][otherGroup]
    reset coinMaps[selectedOwner]
    reset coinMaps[selectedOwner][selectedGroup]
    reset coinMaps[selectedOwner][otherGroup]
    reset coinMaps[otherOwner]
    reset coinMaps[otherOwner][selectedGroup]
    reset coinMaps[otherOwner][otherGroup]
  end

  entry tip uses fundedTwoParentQualifiedCoinListInputs where
    readSelf as own
    mintShielded(domain, 5)
    receiveShieldedToMap(pot, disclose(nonce), disclose(color), 5)
    insertShieldedCoinSet(coinSets[owner], disclose(nonce), disclose(color), 5)
    pushFrontCoin(coinLists[owner], disclose(nonce), disclose(color), 5)
    pushFrontCoin(deepCoinLists[owner][group], disclose(nonce), disclose(color), 5)
    insertShieldedCoinMap(rootCoinMap, key, disclose(nonce), disclose(color), 5, true, own)
    insertShieldedCoinMap(coinMaps[owner][group], key, disclose(nonce), disclose(color), 5,
      true, own)
  end
end

private def fundedTwoParentQualifiedCoinListEntry (name : String) : Entrypoint :=
  (FundedTwoParentQualifiedCoinList.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

#guard FundedTwoParentQualifiedCoinList.entrypoints.length == 2
#guard ((fundedTwoParentQualifiedCoinListEntry "initializeOwners").validate
  Capabilities.source FundedTwoParentQualifiedCoinList.state).isOk
#guard ((fundedTwoParentQualifiedCoinListEntry "tip").validate
  Capabilities.source FundedTwoParentQualifiedCoinList.state).isOk
#guard (Disclosure.entrypoint
  (fundedTwoParentQualifiedCoinListEntry "initializeOwners")).isOk
#guard (Disclosure.entrypoint
  (fundedTwoParentQualifiedCoinListEntry "tip")).isOk

#guard (fundedTwoParentQualifiedCoinListEntry "tip").circuit.inputs.map (·.name) ==
  ["domain", "owner", "group", "key", "nonce", "color"]
#guard match ((fundedTwoParentQualifiedCoinListEntry "tip").effects.filterMap
    fun (effect : Effect) =>
    match effect with
    | .pushFrontCoin "deepCoinLists" _ _ _ _ keys => some keys
    | _ => none) with
  | [[.mk (.bytes 32) (.ref "owner"), .mk (.bytes 32) (.ref "group")]] => Bool.true
  | _ => Bool.false
#guard (fundedTwoParentQualifiedCoinListEntry "tip").effectGuards.all Option.isNone
