import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Disclosure
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit deepBookedCoinSetPathInputs where
  public owner : Bytes32
  public group : Bytes32
  public leaf : Bytes32
  public siblingLeaf : Bytes32
end

noctium_circuit deepBookedCoinSetInsertInputs where
  public owner : Bytes32
  public group : Bytes32
  public leaf : Bytes32
  private nonce : Bytes32
  private color : Bytes32
  private amount : UInt 128
end

noctium_circuit deepBookedCoinSetInsertToInputs where
  public owner : Bytes32
  public group : Bytes32
  public leaf : Bytes32
  private nonce : Bytes32
  private color : Bytes32
  private amount : UInt 128
  private isContract : Bool
  private recipient : Bytes32
end

noctium_contract DeepBookedCoinSetBoundary where
  tree coinSets :
    Bytes32 => Bytes32 => Bytes32 => Bytes32 =>
    Bytes32 => Bytes32 => Bytes32 => Bytes32 =>
    Bytes32 => Bytes32 => Bytes32 => Bytes32 =>
    Bytes32 => Bytes32 => Set struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry initializePaths uses deepBookedCoinSetPathInputs where
    reset coinSets[owner]
    reset coinSets[owner][group]
    reset coinSets[owner][group][group]
    reset coinSets[owner][group][group][group]
    reset coinSets[owner][group][group][group][group]
    reset coinSets[owner][group][group][group][group][group]
    reset coinSets[owner][group][group][group][group][group][group]
    reset coinSets[owner][group][group][group][group][group][group][group]
    reset coinSets[owner][group][group][group][group][group][group][group][group]
    reset coinSets[owner][group][group][group][group][group][group][group][group][group]
    reset coinSets[owner][group][group][group][group][group][group][group][group][group][group]
    reset coinSets[owner][group][group][group][group][group][group][group][group][group][group][group]
    reset coinSets[owner][group][group][group][group][group][group][group][group][group][group][group][group]
    reset coinSets[owner][group][group][group][group][group][group][group][group][group][group][group][group][leaf]
    reset coinSets[owner][group][group][group][group][group][group][group][group][group][group][group][group][siblingLeaf]
  end

  entry insertCoin uses deepBookedCoinSetInsertInputs where
    insertShieldedCoinSet(
      coinSets[owner][group][group][group][group][group][group][group][group][group][group][group][group][leaf],
      disclose(nonce), disclose(color), disclose(amount))
  end

  entry insertCoinTo uses deepBookedCoinSetInsertToInputs where
    insertShieldedCoinSet(
      coinSets[owner][group][group][group][group][group][group][group][group][group][group][group][group][leaf],
      disclose(nonce), disclose(color), disclose(amount),
      disclose(isContract), disclose(recipient))
  end
end

private def deepBookedCoinSetEntry (name : String) : Entrypoint :=
  (DeepBookedCoinSetBoundary.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

private def deepBookedCoinSetInsert : Entrypoint :=
  deepBookedCoinSetEntry "insertCoin"

private def deepBookedCoinSetInsertTo : Entrypoint :=
  deepBookedCoinSetEntry "insertCoinTo"

#guard (deepBookedCoinSetEntry "initializePaths").circuit.inputs.map (·.name) ==
  ["owner", "group", "leaf", "siblingLeaf"]
#guard deepBookedCoinSetInsert.circuit.inputs.map (·.name) ==
  ["owner", "group", "leaf", "nonce", "color", "amount"]
#guard deepBookedCoinSetInsertTo.circuit.inputs.map (·.name) ==
  ["owner", "group", "leaf", "nonce", "color", "amount", "isContract", "recipient"]

#guard ((deepBookedCoinSetEntry "initializePaths").validate
  Capabilities.source DeepBookedCoinSetBoundary.state).isOk
#guard (deepBookedCoinSetInsert.validate
  Capabilities.source DeepBookedCoinSetBoundary.state).isOk
#guard (deepBookedCoinSetInsertTo.validate
  Capabilities.source DeepBookedCoinSetBoundary.state).isOk
#guard (Disclosure.entrypoint (deepBookedCoinSetEntry "initializePaths")).isOk
#guard (Disclosure.entrypoint deepBookedCoinSetInsert).isOk
#guard (Disclosure.entrypoint deepBookedCoinSetInsertTo).isOk

#guard match deepBookedCoinSetInsert.effects with
  | [ .readContractAddress selfAddressName
    , .insertShieldedCoinSet "coinSets" _ _ _ (.ref addressName) keys ] =>
      selfAddressName == addressName && keys.length == 14
  | _ => Bool.false

#guard match deepBookedCoinSetInsertTo.effects with
  | [ .insertShieldedCoinSetTo "coinSets" _ _ _ _ _
        [ .mk (.bytes 32) (.ref "owner"), .mk (.bytes 32) (.ref "group")
        , .mk (.bytes 32) (.ref "group"), .mk (.bytes 32) (.ref "group")
        , .mk (.bytes 32) (.ref "group"), .mk (.bytes 32) (.ref "group")
        , .mk (.bytes 32) (.ref "group"), .mk (.bytes 32) (.ref "group")
        , .mk (.bytes 32) (.ref "group"), .mk (.bytes 32) (.ref "group")
        , .mk (.bytes 32) (.ref "group"), .mk (.bytes 32) (.ref "group")
        , .mk (.bytes 32) (.ref "group"), .mk (.bytes 32) (.ref "leaf") ] ] =>
      Bool.true
  | _ => Bool.false

#guard match Backend.Impact.lower DeepBookedCoinSetBoundary.state deepBookedCoinSetInsert with
  | .ok plan =>
      plan.operations.any fun
        | .insertShieldedCoinSet 0 _ _ _ _ keys => keys.length == 14
        | _ => Bool.false
  | .error _ => Bool.false
#guard match Backend.Impact.lower DeepBookedCoinSetBoundary.state deepBookedCoinSetInsertTo with
  | .ok plan =>
      plan.operations.any fun
        | .insertShieldedCoinSetTo 0 _ _ _ _ _ _ keys => keys.length == 14
        | _ => Bool.false
  | .error _ => Bool.false
#guard (Backend.Zkir.lowerPrunedEntrypoint DeepBookedCoinSetBoundary.state
  deepBookedCoinSetInsert).isOk
#guard (Backend.Zkir.lowerPrunedEntrypoint DeepBookedCoinSetBoundary.state
  deepBookedCoinSetInsertTo).isOk

/-- error: insertShieldedCoinSet supports at most fourteen Bytes32 Map parents -/
#guard_msgs (substring := true) in
noctium_contract TooDeepBookedCoinSetBoundary where
  tree coinSets :
    Bytes32 => Bytes32 => Bytes32 => Bytes32 =>
    Bytes32 => Bytes32 => Bytes32 => Bytes32 =>
    Bytes32 => Bytes32 => Bytes32 => Bytes32 =>
    Bytes32 => Bytes32 => Bytes32 => Set struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry insertTooDeep uses deepBookedCoinSetInsertInputs where
    insertShieldedCoinSet(
      coinSets[owner][group][group][group][group][group][group][group][group][group][group][group][group][group][leaf],
      disclose(nonce), disclose(color), disclose(amount))
  end
end
