import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Disclosure
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit fourParentQualifiedCoinListPathInputs where
  public first : Bytes32
  public second : Bytes32
  public third : Bytes32
  public fourth : Bytes32
  public siblingThird : Bytes32
  public siblingFourth : Bytes32
end

noctium_circuit fourParentQualifiedCoinListPushInputs where
  public first : Bytes32
  public second : Bytes32
  public third : Bytes32
  public fourth : Bytes32
  private nonce : Bytes32
  private color : Bytes32
  private amount : UInt 128
end

noctium_circuit fourParentQualifiedCoinListPushToInputs where
  public first : Bytes32
  public second : Bytes32
  public third : Bytes32
  public fourth : Bytes32
  private nonce : Bytes32
  private color : Bytes32
  private amount : UInt 128
  public isContract : Bool
  public recipient : Bytes32
end

noctium_contract FourParentQualifiedCoinList where
  tree coinLists : Bytes32 => Bytes32 => Bytes32 => Bytes32 => List struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry initializePaths uses fourParentQualifiedCoinListPathInputs where
    reset coinLists[first]
    reset coinLists[first][second]
    reset coinLists[first][second][third]
    reset coinLists[first][second][siblingThird]
    reset coinLists[first][second][third][fourth]
    reset coinLists[first][second][third][siblingFourth]
    reset coinLists[first][second][siblingThird][fourth]
  end

  entry pushCoin uses fourParentQualifiedCoinListPushInputs where
    pushFrontCoin(coinLists[first][second][third][fourth],
      disclose(nonce), disclose(color), disclose(amount))
  end

  entry pushCoinTo uses fourParentQualifiedCoinListPushToInputs where
    pushFrontCoin(coinLists[first][second][third][fourth],
      disclose(nonce), disclose(color), disclose(amount), isContract, recipient)
  end
end

private def fourParentQualifiedCoinListEntry (name : String) : Entrypoint :=
  (FourParentQualifiedCoinList.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

#guard ((fourParentQualifiedCoinListEntry "initializePaths").validate
  Capabilities.source FourParentQualifiedCoinList.state).isOk
#guard ((fourParentQualifiedCoinListEntry "pushCoin").validate
  Capabilities.source FourParentQualifiedCoinList.state).isOk
#guard ((fourParentQualifiedCoinListEntry "pushCoinTo").validate
  Capabilities.source FourParentQualifiedCoinList.state).isOk
#guard (Disclosure.entrypoint
  (fourParentQualifiedCoinListEntry "initializePaths")).isOk
#guard (Disclosure.entrypoint
  (fourParentQualifiedCoinListEntry "pushCoin")).isOk
#guard (Disclosure.entrypoint
  (fourParentQualifiedCoinListEntry "pushCoinTo")).isOk

#guard match (fourParentQualifiedCoinListEntry "pushCoin").effects with
  | [.readContractAddress addressName,
      .pushFrontCoin "coinLists" _ _ _ (.ref selfAddressName)
        [ .mk (.bytes 32) (.ref "first"), .mk (.bytes 32) (.ref "second")
        , .mk (.bytes 32) (.ref "third"), .mk (.bytes 32) (.ref "fourth") ]] =>
      addressName == selfAddressName
  | _ => Bool.false

#guard match (fourParentQualifiedCoinListEntry "pushCoinTo").effects with
  | [.pushFrontCoinTo "coinLists" _ _ _ _ _
        [ .mk (.bytes 32) (.ref "first"), .mk (.bytes 32) (.ref "second")
        , .mk (.bytes 32) (.ref "third"), .mk (.bytes 32) (.ref "fourth") ]] =>
      Bool.true
  | _ => Bool.false

#guard match Backend.Impact.lower FourParentQualifiedCoinList.state
    (fourParentQualifiedCoinListEntry "pushCoin") with
  | .ok plan =>
      plan.operations.any fun
        | .listPushFrontCoin 0 keys _ _ _ _ _ => keys.length == 4
        | _ => Bool.false
  | .error _ => Bool.false

#guard match Backend.Impact.lower FourParentQualifiedCoinList.state
    (fourParentQualifiedCoinListEntry "pushCoinTo") with
  | .ok plan =>
      plan.operations.any fun
        | .listPushFrontCoinTo 0 keys _ _ _ _ _ _ _ => keys.length == 4
        | _ => Bool.false
  | .error _ => Bool.false

#guard (Backend.Zkir.lowerPrunedEntrypoint FourParentQualifiedCoinList.state
  (fourParentQualifiedCoinListEntry "pushCoin")).isOk
#guard (Backend.Zkir.lowerPrunedEntrypoint FourParentQualifiedCoinList.state
  (fourParentQualifiedCoinListEntry "pushCoinTo")).isOk

noctium_circuit fiveParentQualifiedCoinListPushInputs where
  public first : Bytes32
  public second : Bytes32
  public third : Bytes32
  public fourth : Bytes32
  public fifth : Bytes32
  private nonce : Bytes32
  private color : Bytes32
  private amount : UInt 128
end

/-- error: pushFrontCoin supports a qualified coin List under at most four Bytes32-keyed Maps -/
#guard_msgs (substring := true) in
noctium_contract FiveParentQualifiedCoinList where
  tree coinLists : Bytes32 => Bytes32 => Bytes32 => Bytes32 => Bytes32 =>
      List struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry pushCoin uses fiveParentQualifiedCoinListPushInputs where
    pushFrontCoin(coinLists[first][second][third][fourth][fifth],
      disclose(nonce), disclose(color), disclose(amount))
  end
end
