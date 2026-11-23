import Noctium.Disclosure
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit twoParentQualifiedCoinListPathInputs where
  public owner : Bytes32
  public bucket : Bytes32
end

noctium_circuit twoParentQualifiedCoinListPushInputs where
  public owner : Bytes32
  public bucket : Bytes32
  private nonce : Bytes32
  private color : Bytes32
  private amount : UInt 128
end

noctium_contract TwoParentQualifiedCoinList where
  tree coinLists : Bytes32 => Bytes32 => List struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry initializeList uses twoParentQualifiedCoinListPathInputs where
    member coinLists[owner] as ownerPresent
    if eq(ownerPresent, false) then {
      insert coinLists[owner] := emptyMap
    } else {
    }
    reset coinLists[owner][bucket]
  end

  entry pushCoin uses twoParentQualifiedCoinListPushInputs where
    pushFrontCoin(coinLists[owner][bucket], disclose(nonce), disclose(color), disclose(amount))
  end
end

private def twoParentQualifiedCoinListEntry (name : String) : Entrypoint :=
  (TwoParentQualifiedCoinList.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

#guard ((twoParentQualifiedCoinListEntry "initializeList").validate
  Capabilities.source TwoParentQualifiedCoinList.state).isOk
#guard ((twoParentQualifiedCoinListEntry "pushCoin").validate
  Capabilities.source TwoParentQualifiedCoinList.state).isOk
#guard (Disclosure.entrypoint (twoParentQualifiedCoinListEntry "initializeList")).isOk
#guard (Disclosure.entrypoint (twoParentQualifiedCoinListEntry "pushCoin")).isOk
#guard (twoParentQualifiedCoinListEntry "initializeList").effects.any fun
  | .listReset "coinLists"
      [.mk (.bytes 32) (.ref "owner"), .mk (.bytes 32) (.ref "bucket")] => Bool.true
  | _ => Bool.false
#guard match (twoParentQualifiedCoinListEntry "pushCoin").effects with
  | [.readContractAddress _,
      .pushFrontCoin "coinLists" _ _ _ _
        [.mk (.bytes 32) (.ref "owner"), .mk (.bytes 32) (.ref "bucket")]] => Bool.true
  | _ => Bool.false
