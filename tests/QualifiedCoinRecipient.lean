import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Compiler
import Noctium.Disclosure
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit qualifiedCoinRecipientInputs where
  private nonce : Bytes32
  private color : Bytes32
  private amount : UInt 128
  public isContract : Bool
  public recipient : Bytes32
end

noctium_contract QualifiedCoinRecipient where
  cell coinSlot : struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  set coinSet : struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  list coinList : struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry writeCellTo uses qualifiedCoinRecipientInputs where
    writeShieldedCoinCell(coinSlot, disclose(nonce), disclose(color), disclose(amount),
      disclose(isContract), disclose(recipient))
  end

  entry insertSetTo uses qualifiedCoinRecipientInputs where
    insertShieldedCoinSet(coinSet, disclose(nonce), disclose(color), disclose(amount),
      disclose(isContract), disclose(recipient))
  end

  entry pushListTo uses qualifiedCoinRecipientInputs where
    pushFrontCoin(coinList, disclose(nonce), disclose(color), disclose(amount),
      disclose(isContract), disclose(recipient))
  end
end

private def qualifiedCoinRecipientEntries : List Entrypoint :=
  QualifiedCoinRecipient.entrypoints

#guard qualifiedCoinRecipientEntries.length == 3

private def qualifiedCellRecipientEntry : Entrypoint :=
  match qualifiedCoinRecipientEntries with
  | found :: _ => found
  | [] => {name := "missing", circuit := {name := "missing"}}

private def qualifiedSetRecipientEntry : Entrypoint :=
  match qualifiedCoinRecipientEntries with
  | _ :: found :: _ => found
  | _ => {name := "missing", circuit := {name := "missing"}}

private def qualifiedListRecipientEntry : Entrypoint :=
  match qualifiedCoinRecipientEntries with
  | _ :: _ :: found :: _ => found
  | _ => {name := "missing", circuit := {name := "missing"}}

#guard qualifiedCellRecipientEntry.effects.length == 1
#guard match qualifiedCellRecipientEntry.effects with
  | [.writeShieldedCoinCellTo ..] => _root_.Bool.true
  | _ => _root_.Bool.false
#guard qualifiedSetRecipientEntry.effects.length == 1
#guard match qualifiedSetRecipientEntry.effects with
  | [.insertShieldedCoinSetTo ..] => _root_.Bool.true
  | _ => _root_.Bool.false
#guard qualifiedListRecipientEntry.effects.length == 1
#guard match qualifiedListRecipientEntry.effects with
  | [.pushFrontCoinTo ..] => _root_.Bool.true
  | _ => _root_.Bool.false

#guard (Disclosure.entrypoint qualifiedCellRecipientEntry).isOk
#guard (Disclosure.entrypoint qualifiedSetRecipientEntry).isOk
#guard (Disclosure.entrypoint qualifiedListRecipientEntry).isOk
#guard (qualifiedCellRecipientEntry.validate Capabilities.source QualifiedCoinRecipient.state).isOk
#guard (qualifiedSetRecipientEntry.validate Capabilities.source QualifiedCoinRecipient.state).isOk
#guard (qualifiedListRecipientEntry.validate Capabilities.source QualifiedCoinRecipient.state).isOk

#guard qualifiedCellRecipientEntry.effectGuards.length == 1 &&
  qualifiedCellRecipientEntry.effectGuards.all Option.isNone
#guard qualifiedSetRecipientEntry.effectGuards.length == 1 &&
  qualifiedSetRecipientEntry.effectGuards.all Option.isNone
#guard qualifiedListRecipientEntry.effectGuards.length == 1 &&
  qualifiedListRecipientEntry.effectGuards.all Option.isNone

private def qualifiedCoinRecipientGuarded : Entrypoint :=
  {qualifiedCellRecipientEntry with effectGuards := [some (.bool Bool.true)]}

#guard match qualifiedCoinRecipientGuarded.validate Capabilities.source QualifiedCoinRecipient.state with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false

#guard match Backend.Impact.lower QualifiedCoinRecipient.state qualifiedCellRecipientEntry with
  | .ok plan =>
      match plan.operations.filterMap fun operation =>
          match operation with
          | .writeShieldedCoinCellTo slot _ _ _ _ _ _ =>
              some (slot, operation.fieldGroups.map List.length)
          | _ => none with
      | [(0, widths)] => widths == [5, 1, 6, 5, 11, 1, 2, 1]
      | _ => _root_.Bool.false
  | .error _ => _root_.Bool.false

#guard match Backend.Impact.lower QualifiedCoinRecipient.state qualifiedSetRecipientEntry with
  | .ok plan =>
      match plan.operations.filterMap fun operation =>
          match operation with
          | .insertShieldedCoinSetTo slot _ _ _ _ _ _ [] =>
              some (slot, operation.fieldGroups.map List.length)
          | _ => none with
      | [(1, widths)] => widths == [4, 1, 6, 5, 11, 1, 2, 2, 1, 1]
      | _ => _root_.Bool.false
  | .error _ => _root_.Bool.false

#guard match Backend.Impact.lower QualifiedCoinRecipient.state qualifiedListRecipientEntry with
  | .ok plan =>
      match plan.operations.filterMap fun operation =>
          match operation with
          | .listPushFrontCoinTo slot keys _ _ _ _ _ _ _ =>
              some (slot, keys, operation.fieldGroups.map List.length)
          | _ => none with
      | [(2, [], widths)] => widths ==
          [4, 1, 4, 2, 5, 5, 1, 6, 5, 11, 1, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1]
      | _ => _root_.Bool.false
  | .error _ => _root_.Bool.false

#guard (Backend.Zkir.lowerPrunedEntrypoint QualifiedCoinRecipient.state qualifiedCellRecipientEntry).isOk
#guard (Backend.Zkir.lowerPrunedEntrypoint QualifiedCoinRecipient.state qualifiedSetRecipientEntry).isOk
#guard (Backend.Zkir.lowerPrunedEntrypoint QualifiedCoinRecipient.state qualifiedListRecipientEntry).isOk
