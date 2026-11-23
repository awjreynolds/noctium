import Noctium.Disclosure
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit nestedQualifiedCoinListOwnerInputs where
  public owner : Bytes32
end

noctium_circuit nestedQualifiedCoinListPushInputs where
  public owner : Bytes32
  private nonce : Bytes32
  private color : Bytes32
  private amount : UInt 128
end

noctium_circuit nestedQualifiedCoinListRecipientInputs where
  public owner : Bytes32
  private nonce : Bytes32
  private color : Bytes32
  private amount : UInt 128
  public isContract : Bool
  public recipient : Bytes32
end

noctium_contract NestedQualifiedCoinList where
  tree coinLists : Bytes32 => List struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry initializeOwner uses nestedQualifiedCoinListOwnerInputs where
    reset coinLists[owner]
  end

  entry pushCoin uses nestedQualifiedCoinListPushInputs where
    pushFrontCoin(coinLists[owner], disclose(nonce), disclose(color), disclose(amount))
  end

  entry pushCoinTo uses nestedQualifiedCoinListRecipientInputs where
    pushFrontCoin(coinLists[owner], disclose(nonce), disclose(color), disclose(amount),
      isContract, recipient)
  end
end

private def nestedQualifiedCoinListEntry (name : String) : Entrypoint :=
  (NestedQualifiedCoinList.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

#guard ((nestedQualifiedCoinListEntry "initializeOwner").validate
  Capabilities.source NestedQualifiedCoinList.state).isOk
#guard ((nestedQualifiedCoinListEntry "pushCoin").validate
  Capabilities.source NestedQualifiedCoinList.state).isOk
#guard (Disclosure.entrypoint (nestedQualifiedCoinListEntry "pushCoin")).isOk

#guard
  let selectedEntry := nestedQualifiedCoinListEntry "pushCoin"
  let inputs := selectedEntry.circuit.inputs.map fun input =>
    if input.name == "owner" then {input with visibility := Noctium.Visibility.private} else input
  !(Disclosure.entrypoint {selectedEntry with circuit := {selectedEntry.circuit with inputs}}).isOk

#guard match (nestedQualifiedCoinListEntry "initializeOwner").effects with
  | [.listReset "coinLists" [.mk (.bytes 32) (.ref "owner")]] => Bool.true
  | _ => Bool.false

#guard match (nestedQualifiedCoinListEntry "pushCoin").effects with
  | [.readContractAddress addressName,
      .pushFrontCoin "coinLists" _ _ _ (.ref selfAddressName)
        [.mk (.bytes 32) (.ref "owner")]] =>
      addressName == selfAddressName
  | _ => Bool.false

#guard (nestedQualifiedCoinListEntry "pushCoin").effectGuards.all Option.isNone
