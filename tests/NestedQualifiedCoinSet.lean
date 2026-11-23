import Noctium.Disclosure
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit nestedQualifiedCoinSetOwnerInputs where
  public owner : Bytes32
end

noctium_circuit nestedQualifiedCoinSetInputs where
  public owner : Bytes32
  private nonce : Bytes32
  private color : Bytes32
  private amount : UInt 128
end

noctium_circuit nestedQualifiedCoinSetToInputs where
  public owner : Bytes32
  private nonce : Bytes32
  private color : Bytes32
  private amount : UInt 128
  private isContract : Bool
  private recipient : Bytes32
end

noctium_contract NestedQualifiedCoinSet where
  tree coinSets : Bytes32 => Set struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry initializeOwner uses nestedQualifiedCoinSetOwnerInputs where
    reset coinSets[owner]
  end

  entry insertCoin uses nestedQualifiedCoinSetInputs where
    insertShieldedCoinSet(coinSets[owner], disclose(nonce), disclose(color), disclose(amount))
  end

  entry insertCoinTo uses nestedQualifiedCoinSetToInputs where
    insertShieldedCoinSet(coinSets[owner], disclose(nonce), disclose(color), disclose(amount),
      disclose(isContract), disclose(recipient))
  end
end

private def nestedQualifiedCoinSetEntry (name : String) : Entrypoint :=
  (NestedQualifiedCoinSet.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

#guard ((nestedQualifiedCoinSetEntry "initializeOwner").validate
  Capabilities.source NestedQualifiedCoinSet.state).isOk
#guard ((nestedQualifiedCoinSetEntry "insertCoin").validate
  Capabilities.source NestedQualifiedCoinSet.state).isOk
#guard ((nestedQualifiedCoinSetEntry "insertCoinTo").validate
  Capabilities.source NestedQualifiedCoinSet.state).isOk
#guard (Disclosure.entrypoint (nestedQualifiedCoinSetEntry "initializeOwner")).isOk
#guard (Disclosure.entrypoint (nestedQualifiedCoinSetEntry "insertCoin")).isOk
#guard (Disclosure.entrypoint (nestedQualifiedCoinSetEntry "insertCoinTo")).isOk

#guard match NestedQualifiedCoinSet.state with
  | [{kind := .tree (.map (.bytes 32) (.shieldedCoinSet environment recordType)), ..}] =>
      (LedgerValueType.shieldedCoinRecordFields environment recordType).isOk
  | _ => Bool.false

#guard match (nestedQualifiedCoinSetEntry "initializeOwner").effects with
  | [.emptyMapPath "coinSets" [.mk (.bytes 32) (.ref "owner")]] => Bool.true
  | _ => Bool.false

#guard match (nestedQualifiedCoinSetEntry "insertCoin").effects with
  | [.readContractAddress addressName,
      .insertShieldedCoinSet "coinSets" _ _ _ (.ref selfAddressName)
        [.mk (.bytes 32) (.ref "owner")]] => addressName == selfAddressName
  | _ => Bool.false

#guard match (nestedQualifiedCoinSetEntry "insertCoinTo").effects with
  | [.insertShieldedCoinSetTo "coinSets" _ _ _ _ _
      [.mk (.bytes 32) (.ref "owner")]] => Bool.true
  | _ => Bool.false

private def nestedQualifiedCoinSetPrivateOwnerProbe : Entrypoint :=
  let operation := nestedQualifiedCoinSetEntry "insertCoin"
  {operation with circuit := {operation.circuit with
    inputs := operation.circuit.inputs.map fun input =>
      if input.name == "owner" then
        {input with visibility := .«private»}
      else input}}

#guard match Disclosure.entrypoint nestedQualifiedCoinSetPrivateOwnerProbe with
  | .error diagnostic => diagnostic.message.contains "undisclosed private parameter 'owner'"
  | .ok _ => Bool.false
