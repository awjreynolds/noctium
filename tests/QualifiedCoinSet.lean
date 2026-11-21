import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Compiler
import Noctium.Disclosure
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit qualifiedCoinSetInputs where
  private nonce : Bytes32
  private color : Bytes32
  private amount : UInt 128
end

noctium_contract QualifiedCoinSet where
  set coinSet : struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry insertCoin uses qualifiedCoinSetInputs where
    insertShieldedCoinSet(coinSet, disclose(nonce), disclose(color), disclose(amount))
  end
end

private def qualifiedCoinSetEntry : Entrypoint :=
  match QualifiedCoinSet.entrypoints with
  | found :: _ => found
  | [] => {name := "missing", circuit := {name := "missing"}}

#guard qualifiedCoinSetEntry.name == "insertCoin"
#guard qualifiedCoinSetEntry.effects.length == 2
#guard qualifiedCoinSetEntry.effectGuards.length == 2 &&
  qualifiedCoinSetEntry.effectGuards.all Option.isNone
#guard match qualifiedCoinSetEntry.effects with
  | [.readContractAddress addressName,
      .insertShieldedCoinSet "coinSet" _ _ _ (.ref selfAddressName)] =>
      addressName == "noctium_coin_set_address_0" && addressName == selfAddressName
  | _ => Bool.false
#guard (Disclosure.entrypoint qualifiedCoinSetEntry).isOk
#guard (qualifiedCoinSetEntry.validate Capabilities.source QualifiedCoinSet.state).isOk

#guard match QualifiedCoinSet.state with
  | [{kind := .tree (.shieldedCoinSet environment recordType), ..}] =>
      (LedgerValueType.shieldedCoinRecordFields environment recordType).isOk
  | _ => Bool.false

private def hasPinnedQualifiedCoinSetGroups (operation : Backend.Impact.Op) : _root_.Bool :=
  match operation.fieldGroups with
  | [ [Expr.native 0x70, Expr.native 1, Expr.native 1, Expr.native 0]
    , [Expr.native 0x34]
    , [Expr.native 0x10, Expr.native 1, Expr.native 1, Expr.native 32,
        Expr.bytesField _ 0, Expr.bytesField _ 1]
    , [Expr.native 0x61, Expr.native 1, Expr.native 1, Expr.native 1, Expr.native index]
    , [Expr.native 0x10, Expr.native 1, Expr.native 3, Expr.native 32, Expr.native 32,
        Expr.native 16, Expr.bytesField _ 0, Expr.bytesField _ 1, Expr.bytesField _ 0,
        Expr.bytesField _ 1, Expr.cast .native (.disclose _ (.ref "amount"))]
    , [Expr.native 0x40]
    , [Expr.native 0x17, Expr.native 91]
    , [Expr.native 0x11, Expr.native 0]
    , [Expr.native 0x91]
    , [Expr.native 0xa1] ] => index == Field.modulus - 1
  | _ => Bool.false

#guard match Backend.Impact.lower QualifiedCoinSet.state qualifiedCoinSetEntry with
  | .ok plan =>
      let writes := plan.operations.filter fun operation =>
        match operation with
        | .insertShieldedCoinSet .. => Bool.true
        | _ => Bool.false
      match writes with
      | [operation] =>
          plan.operations.length == 2 &&
          operation.fieldGroups.map List.length == [4, 1, 6, 5, 11, 1, 2, 2, 1, 1] &&
          hasPinnedQualifiedCoinSetGroups operation
      | _ => Bool.false
  | .error _ => Bool.false

private def qualifiedCoinSetWrongState : List StateDecl :=
  QualifiedCoinSet.state.map fun declaration =>
    {declaration with kind := .tree (.set (.bytes 32))}

#guard match qualifiedCoinSetEntry.validate Capabilities.source qualifiedCoinSetWrongState with
  | .error diagnostic => diagnostic.message.contains "root record Set"
  | .ok _ => Bool.false

private def qualifiedCoinSetGuarded : Entrypoint :=
  {qualifiedCoinSetEntry with effectGuards := [none, some (.bool Bool.true)]}

#guard match qualifiedCoinSetGuarded.validate Capabilities.source QualifiedCoinSet.state with
  | .error _ => Bool.true
  | .ok _ => Bool.false

#guard (Backend.Zkir.lowerPrunedEntrypoint QualifiedCoinSet.state qualifiedCoinSetEntry).isOk
