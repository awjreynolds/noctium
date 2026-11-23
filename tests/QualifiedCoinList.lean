import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Compiler
import Noctium.Disclosure
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit qualifiedCoinListInputs where
  private nonce : Bytes32
  private color : Bytes32
  private amount : UInt 128
end

noctium_contract QualifiedCoinList where
  list coinList : struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry «pushFrontCoin» uses qualifiedCoinListInputs where
    pushFrontCoin(coinList, disclose(nonce), disclose(color), disclose(amount))
  end
end

private def qualifiedCoinListEntry : Entrypoint :=
  match QualifiedCoinList.entrypoints with
  | found :: _ => found
  | [] => {name := "missing", circuit := {name := "missing"}}

private def qualifiedCoinListU8PushMatches
    (group : List Backend.Impact.Scalar) (expected : Nat) : _root_.Bool :=
  match group with
  | [.native 0x10, .native 1, .native 1, .native 1, .native value] => value == expected
  | _ => Bool.false

private def qualifiedCoinListNativeOpcodeMatches
    (group : List Backend.Impact.Scalar) (expected : Nat) : _root_.Bool :=
  match group with
  | [.native opcode] => opcode == expected
  | _ => Bool.false

private def qualifiedCoinListRootPathMatches
    (group : List Backend.Impact.Scalar) (slot : Nat) : _root_.Bool :=
  match group with
  | [.native 0x70, .native 1, .native 1, .native value] => value == slot
  | _ => Bool.false

#guard qualifiedCoinListEntry.name == "pushFrontCoin"
#guard qualifiedCoinListEntry.effects.length == 2
#guard qualifiedCoinListEntry.effectGuards.length == 2 &&
  qualifiedCoinListEntry.effectGuards.all Option.isNone
#guard match qualifiedCoinListEntry.effects with
  | [.readContractAddress addressName,
      .pushFrontCoin "coinList" _ _ _ (.ref selfAddressName) []] =>
      addressName == "noctium_coin_list_address_0" && addressName == selfAddressName
  | _ => Bool.false
#guard (Disclosure.entrypoint qualifiedCoinListEntry).isOk
#guard (qualifiedCoinListEntry.validate Capabilities.source QualifiedCoinList.state).isOk

#guard match QualifiedCoinList.state with
  | [{kind := .tree (.list environment recordType), ..}] =>
      match LedgerValueType.shieldedCoinRecordFields environment recordType with
      | .ok fields => fields == [
          ("nonce", .bytes 32), ("color", .bytes 32),
          ("value", .uint (2 ^ 128 - 1)), ("mtIndex", .uint (2 ^ 64 - 1))]
      | .error _ => Bool.false
  | _ => Bool.false

#guard match Backend.Impact.lower QualifiedCoinList.state qualifiedCoinListEntry with
  | .ok plan =>
      match plan.operations with
      | [.readContractAddress _,
          .listPushFrontCoin slot keys schema nonce color amount commitment] =>
          let groups := Backend.Impact.Op.fieldGroups
            (.listPushFrontCoin slot keys schema nonce color amount commitment)
          slot == 0 && keys.isEmpty && schema != Lean.Json.null &&
          groups.map List.length == [4, 1, 4, 2, 5, 5, 1, 6, 5, 11, 1, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1] &&
          qualifiedCoinListRootPathMatches (groups[0]?.getD []) 0 &&
          qualifiedCoinListNativeOpcodeMatches (groups[6]?.getD []) 0x37 &&
          qualifiedCoinListNativeOpcodeMatches (groups[12]?.getD []) 0xa1 &&
          qualifiedCoinListNativeOpcodeMatches (groups[16]?.getD []) 0xa1 &&
          qualifiedCoinListNativeOpcodeMatches (groups[20]?.getD []) 0xa2 &&
          qualifiedCoinListNativeOpcodeMatches ((groups[4]?.getD []).take 1) 0x11 &&
          qualifiedCoinListU8PushMatches (groups[5]?.getD []) 0 &&
          qualifiedCoinListU8PushMatches (groups[14]?.getD []) 2 &&
          qualifiedCoinListU8PushMatches (groups[18]?.getD []) 1
      | _ => Bool.false
  | .error _ => Bool.false

private def qualifiedCoinListWrongState : List StateDecl :=
  QualifiedCoinList.state.map fun declaration =>
    {declaration with kind := .cell (.bytes 32)}

#guard match qualifiedCoinListEntry.validate Capabilities.source qualifiedCoinListWrongState with
  | .error diagnostic => diagnostic.message.contains "root List"
  | .ok _ => Bool.false

private def qualifiedCoinListGuarded : Entrypoint :=
  {qualifiedCoinListEntry with effectGuards := [none, some (.bool Bool.true)]}

#guard match qualifiedCoinListGuarded.validate Capabilities.source QualifiedCoinList.state with
  | .error _ => Bool.true
  | .ok _ => Bool.false

#guard (Backend.Zkir.lowerPrunedEntrypoint QualifiedCoinList.state qualifiedCoinListEntry).isOk
