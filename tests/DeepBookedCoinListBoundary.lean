import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Disclosure
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit deepBookedCoinListPathInputs where
  public owner : Bytes32
  public group : Bytes32
  public leaf : Bytes32
  public siblingLeaf : Bytes32
end

noctium_circuit deepBookedCoinListPushInputs where
  public owner : Bytes32
  public group : Bytes32
  public leaf : Bytes32
  private nonce : Bytes32
  private color : Bytes32
  private amount : UInt 128
end

noctium_contract DeepBookedCoinListBoundary where
  tree coinLists :
    Bytes32 => Bytes32 => Bytes32 => Bytes32 =>
    Bytes32 => Bytes32 => Bytes32 => Bytes32 =>
    Bytes32 => Bytes32 => Bytes32 => Bytes32 =>
    Bytes32 => List struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry initializePaths uses deepBookedCoinListPathInputs where
    reset coinLists[owner]
    reset coinLists[owner][group]
    reset coinLists[owner][group][group]
    reset coinLists[owner][group][group][group]
    reset coinLists[owner][group][group][group][group]
    reset coinLists[owner][group][group][group][group][group]
    reset coinLists[owner][group][group][group][group][group][group]
    reset coinLists[owner][group][group][group][group][group][group][group]
    reset coinLists[owner][group][group][group][group][group][group][group][group]
    reset coinLists[owner][group][group][group][group][group][group][group][group][group]
    reset coinLists[owner][group][group][group][group][group][group][group][group][group][group]
    reset coinLists[owner][group][group][group][group][group][group][group][group][group][group][group]
    reset coinLists[owner][group][group][group][group][group][group][group][group][group][group][group][leaf]
    reset coinLists[owner][group][group][group][group][group][group][group][group][group][group][group][siblingLeaf]
  end

  entry pushCoin uses deepBookedCoinListPushInputs where
    pushFrontCoin(coinLists[owner][group][group][group][group][group][group][group][group][group][group][group][leaf], disclose(nonce), disclose(color), disclose(amount))
  end
end

private def deepBookedCoinListEntry (name : String) : Entrypoint :=
  (DeepBookedCoinListBoundary.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

private def deepBookedCoinListPush : Entrypoint :=
  deepBookedCoinListEntry "pushCoin"

#guard ((deepBookedCoinListEntry "initializePaths").validate
  Capabilities.source DeepBookedCoinListBoundary.state).isOk
#guard (deepBookedCoinListPush.validate
  Capabilities.source DeepBookedCoinListBoundary.state).isOk
#guard (Disclosure.entrypoint (deepBookedCoinListEntry "initializePaths")).isOk
#guard (Disclosure.entrypoint deepBookedCoinListPush).isOk

#guard match Backend.Impact.lower DeepBookedCoinListBoundary.state deepBookedCoinListPush with
  | .ok plan =>
      plan.operations.any fun
        | .listPushFrontCoin 0 keys _ _ _ _ _ => keys.length == 13
        | _ => Bool.false
  | .error _ => Bool.false
#guard (Backend.Zkir.lowerPrunedEntrypoint DeepBookedCoinListBoundary.state
  deepBookedCoinListPush).isOk

noctium_circuit fourteenParentQualifiedCoinListInputs where
  public owner : Bytes32
  public group : Bytes32
  public leaf : Bytes32
  private nonce : Bytes32
  private color : Bytes32
  private amount : UInt 128
end

/-- error: pushFrontCoin supports a qualified coin List under at most 13 Bytes32-keyed Maps -/
#guard_msgs (substring := true) in
noctium_contract FourteenParentQualifiedCoinList where
  tree coinLists :
    Bytes32 => Bytes32 => Bytes32 => Bytes32 =>
    Bytes32 => Bytes32 => Bytes32 => Bytes32 =>
    Bytes32 => Bytes32 => Bytes32 => Bytes32 =>
    Bytes32 => Bytes32 => List struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry pushCoin uses fourteenParentQualifiedCoinListInputs where
    pushFrontCoin(coinLists[owner][group][group][group][group][group][group][group][group][group][group][group][group][leaf], disclose(nonce), disclose(color), disclose(amount))
  end
end
