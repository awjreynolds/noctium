import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Disclosure
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit deepQualifiedCoinSetPathInputs where
  public first : Bytes32
  public second : Bytes32
  public third : Bytes32
  public fourth : Bytes32
  public fifth : Bytes32
  public siblingSecond : Bytes32
  public siblingFifth : Bytes32
end

noctium_circuit deepQualifiedCoinSetInputs where
  public first : Bytes32
  public second : Bytes32
  private nonce : Bytes32
  private color : Bytes32
  private amount : UInt 128
end

noctium_circuit deepQualifiedCoinSetToInputs where
  public first : Bytes32
  public second : Bytes32
  public third : Bytes32
  public fourth : Bytes32
  public fifth : Bytes32
  private nonce : Bytes32
  private color : Bytes32
  private amount : UInt 128
  private isContract : Bool
  private recipient : Bytes32
end

noctium_contract DeepQualifiedCoinSet where
  tree coinSets2 : Bytes32 => Bytes32 => Set struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }
  tree coinSets5 : Bytes32 => Bytes32 => Bytes32 => Bytes32 => Bytes32 => Set struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry initializePaths uses deepQualifiedCoinSetPathInputs where
    reset coinSets2[first]
    reset coinSets2[first][second]
    reset coinSets2[first][siblingSecond]
    reset coinSets5[first]
    reset coinSets5[first][second]
    reset coinSets5[first][second][third]
    reset coinSets5[first][second][third][fourth]
    reset coinSets5[first][second][third][fourth][fifth]
    reset coinSets5[first][second][third][fourth][siblingFifth]
  end

  entry insertAtDepth2 uses deepQualifiedCoinSetInputs where
    insertShieldedCoinSet(
      coinSets2[first][second], disclose(nonce), disclose(color), disclose(amount))
  end

  entry insertAtDepth5To uses deepQualifiedCoinSetToInputs where
    insertShieldedCoinSet(
      coinSets5[first][second][third][fourth][fifth],
      disclose(nonce), disclose(color), disclose(amount),
      disclose(isContract), disclose(recipient))
  end
end

private def deepQualifiedCoinSetEntry (name : String) : Entrypoint :=
  (DeepQualifiedCoinSet.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

#guard ((deepQualifiedCoinSetEntry "initializePaths").validate
  Capabilities.source DeepQualifiedCoinSet.state).isOk
#guard ((deepQualifiedCoinSetEntry "insertAtDepth2").validate
  Capabilities.source DeepQualifiedCoinSet.state).isOk
#guard ((deepQualifiedCoinSetEntry "insertAtDepth5To").validate
  Capabilities.source DeepQualifiedCoinSet.state).isOk
#guard (Disclosure.entrypoint (deepQualifiedCoinSetEntry "initializePaths")).isOk
#guard (Disclosure.entrypoint (deepQualifiedCoinSetEntry "insertAtDepth2")).isOk
#guard (Disclosure.entrypoint (deepQualifiedCoinSetEntry "insertAtDepth5To")).isOk

#guard match (deepQualifiedCoinSetEntry "insertAtDepth2").effects with
  | [ .readContractAddress addressName
    , .insertShieldedCoinSet "coinSets2" _ _ _ (.ref selfAddressName)
        [ .mk (.bytes 32) (.ref "first"), .mk (.bytes 32) (.ref "second") ] ] =>
      addressName == selfAddressName
  | _ => Bool.false

#guard match (deepQualifiedCoinSetEntry "insertAtDepth5To").effects with
  | [ .insertShieldedCoinSetTo "coinSets5" _ _ _ _ _
        [ .mk (.bytes 32) (.ref "first"), .mk (.bytes 32) (.ref "second")
        , .mk (.bytes 32) (.ref "third"), .mk (.bytes 32) (.ref "fourth")
        , .mk (.bytes 32) (.ref "fifth") ] ] => Bool.true
  | _ => Bool.false

#guard (Backend.Impact.lower DeepQualifiedCoinSet.state
  (deepQualifiedCoinSetEntry "insertAtDepth2")).isOk
#guard (Backend.Impact.lower DeepQualifiedCoinSet.state
  (deepQualifiedCoinSetEntry "insertAtDepth5To")).isOk
#guard (Backend.Zkir.lowerPrunedEntrypoint DeepQualifiedCoinSet.state
  (deepQualifiedCoinSetEntry "insertAtDepth2")).isOk
#guard (Backend.Zkir.lowerPrunedEntrypoint DeepQualifiedCoinSet.state
  (deepQualifiedCoinSetEntry "insertAtDepth5To")).isOk
