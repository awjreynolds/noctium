import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Compiler
import Noctium.Disclosure
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit qualifiedCoinCellInputs where
  private nonce : Bytes32
  private color : Bytes32
  private amount : UInt 128
end

noctium_circuit qualifiedCoinCellNoInputs where
end

noctium_circuit qualifiedCoinCellResetInputs where
  public enabled : Bool
end

noctium_contract QualifiedCoinCell where
  cell coinSlot : struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry writeCoin uses qualifiedCoinCellInputs where
    writeShieldedCoinCell(coinSlot, disclose(nonce), disclose(color), disclose(amount))
  end
end

noctium_contract QualifiedCoinCellReset where
  cell marker : Native
  cell coinSlot : struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry clear uses qualifiedCoinCellNoInputs where
    reset coinSlot
  end

  entry guardedClear uses qualifiedCoinCellResetInputs where
    when enabled reset coinSlot
  end
end

private def qualifiedCoinCellEntry : Entrypoint :=
  match QualifiedCoinCell.entrypoints with
  | found :: _ => found
  | [] => {name := "missing", circuit := {name := "missing"}}

private def qualifiedCoinCellResetEntry (name : String) : Entrypoint :=
  match QualifiedCoinCellReset.entrypoints.find? (·.name == name) with
  | some found => found
  | none => {name := "missing", circuit := {name := "missing"}}

#guard qualifiedCoinCellEntry.name == "writeCoin"
#guard qualifiedCoinCellEntry.effects.length == 2
#guard qualifiedCoinCellEntry.effectGuards.length == 2 &&
  qualifiedCoinCellEntry.effectGuards.all Option.isNone
#guard match qualifiedCoinCellEntry.effects with
  | [.readContractAddress addressName,
      .writeShieldedCoinCell "coinSlot" _ _ _ (.ref selfAddressName)] =>
      addressName == "noctium_coin_cell_address_0" && addressName == selfAddressName
  | _ => Bool.false
#guard (Disclosure.entrypoint qualifiedCoinCellEntry).isOk
#guard (qualifiedCoinCellEntry.validate Capabilities.source QualifiedCoinCell.state).isOk

#guard match QualifiedCoinCell.state with
  | [{kind := .tree (.composite environment recordType), ..}] =>
      match Backend.Impact.recordSchema environment recordType with
      | .ok schema => schema != Lean.Json.null
      | .error _ => Bool.false
  | _ => Bool.false

#guard match Backend.Impact.lower QualifiedCoinCell.state qualifiedCoinCellEntry with
  | .ok plan =>
      let writes := plan.operations.filter fun operation =>
        match operation with
        | .writeShieldedCoinCell .. => Bool.true
        | _ => Bool.false
      match writes with
      | [operation] =>
          plan.operations.length == 2 &&
          operation.fieldGroups.map List.length == [5, 1, 6, 5, 11, 1, 2, 1]
      | _ => Bool.false
  | .error _ => Bool.false

private def qualifiedCoinCellWrongState : List StateDecl :=
  QualifiedCoinCell.state.map fun declaration =>
    {declaration with kind := .cell (.bytes 32)}

#guard match qualifiedCoinCellEntry.validate Capabilities.source qualifiedCoinCellWrongState with
  | .error diagnostic => diagnostic.message.contains "root composite Cell"
  | .ok _ => Bool.false

private def qualifiedCoinCellGuarded : Entrypoint :=
  {qualifiedCoinCellEntry with effectGuards := [none, some (.bool Bool.true)]}

#guard match qualifiedCoinCellGuarded.validate Capabilities.source QualifiedCoinCell.state with
  | .error _ => Bool.true
  | .ok _ => Bool.false

#guard (Backend.Zkir.lowerPrunedEntrypoint QualifiedCoinCell.state qualifiedCoinCellEntry).isOk

private def qualifiedCoinCellClear := qualifiedCoinCellResetEntry "clear"
private def qualifiedCoinCellGuardedClear := qualifiedCoinCellResetEntry "guardedClear"

private def isZeroQualifiedCoinFields (values : List LedgerFieldExpr) : _root_.Bool :=
  match values with
  | [.mk (.bytes 32) (.bytes32Literal nonce),
      .mk (.bytes 32) (.bytes32Literal color),
      .mk (.uint amountMaximum) (.uint _ value),
      .mk (.uint indexMaximum) (.uint _ index)] =>
        nonce == List.replicate 32 0 && color == List.replicate 32 0 &&
        amountMaximum == 2 ^ 128 - 1 && value == 0 &&
        indexMaximum == 2 ^ 64 - 1 && index == 0
  | _ => Bool.false

#guard match qualifiedCoinCellClear.effects with
  | [.writeCompositePath "coinSlot" [] (.structure recordId) values] =>
      recordId == "QualifiedCoinCellReset.Coin" && isZeroQualifiedCoinFields values
  | _ => Bool.false
#guard match qualifiedCoinCellClear.effectGuards with
  | [none] => Bool.true
  | _ => Bool.false
#guard (qualifiedCoinCellClear.validate Capabilities.source QualifiedCoinCellReset.state).isOk
#guard match qualifiedCoinCellClear.effects with
  | [.writeCompositePath slot keys type (.mk (.bytes 32) _ :: rest)] =>
      let forged := {qualifiedCoinCellClear with effects := [
        .writeCompositePath slot keys type
          (.mk (.bytes 32) (.bytes32Literal (1 :: List.replicate 31 0)) :: rest)]}
      (forged.validate Capabilities.source QualifiedCoinCellReset.state).isOk == Bool.false
  | _ => Bool.false
#guard match qualifiedCoinCellClear.validate
    {Capabilities.source with stateCells := Bool.false} QualifiedCoinCellReset.state with
  | .error diagnostic => diagnostic.message == "target lacks state cells"
  | .ok _ => Bool.false
#guard (qualifiedCoinCellClear.validate
    {Capabilities.source with stateMaps := Bool.false} QualifiedCoinCellReset.state).isOk

private def qualifiedCoinCellSealedState : List StateDecl :=
  QualifiedCoinCellReset.state.map fun declaration =>
    if declaration.name == "coinSlot" then {declaration with «sealed» := Bool.true}
    else declaration

#guard match qualifiedCoinCellClear.validate Capabilities.source qualifiedCoinCellSealedState with
  | .error diagnostic =>
      diagnostic.message == "sealed state 'coinSlot' cannot be written by an entrypoint"
  | .ok _ => Bool.false

private def qualifiedCoinCellResetType : Types.CompositeType :=
  match QualifiedCoinCellReset.state with
  | [_, {kind := .tree (.composite _ type), ..}] => type
  | _ => .structure "missing"

private def qualifiedCoinCellResetBefore : LedgerState := {
  trees := [("coinSlot", .composite qualifiedCoinCellResetType [
    .bytes 32 (List.replicate 32 1),
    .bytes 32 (List.replicate 32 2),
    .uint (2 ^ 128 - 1) 3,
    .uint (2 ^ 64 - 1) 4])]
}

private def qualifiedCoinCellResetZero : LedgerValue := .composite qualifiedCoinCellResetType [
  .bytes 32 (List.replicate 32 0),
  .bytes 32 (List.replicate 32 0),
  .uint (2 ^ 128 - 1) 0,
  .uint (2 ^ 64 - 1) 0]

private def qualifiedCoinCellResetContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by composite Cell reset"
}

#guard match Entrypoint.run qualifiedCoinCellResetContext qualifiedCoinCellClear []
    qualifiedCoinCellResetBefore with
  | .ok (_, after) => after.trees.lookup "coinSlot" == some qualifiedCoinCellResetZero
  | .error _ => Bool.false

#guard match Entrypoint.run qualifiedCoinCellResetContext qualifiedCoinCellGuardedClear
    [("enabled", .bool Bool.false)] qualifiedCoinCellResetBefore with
  | .ok (_, after) => after.trees.lookup "coinSlot" == qualifiedCoinCellResetBefore.trees.lookup "coinSlot"
  | .error _ => Bool.false

#guard match Entrypoint.run qualifiedCoinCellResetContext qualifiedCoinCellGuardedClear
    [("enabled", .bool Bool.true)] qualifiedCoinCellResetBefore with
  | .ok (_, after) => after.trees.lookup "coinSlot" == some qualifiedCoinCellResetZero
  | .error _ => Bool.false

private def qualifiedCoinCellResetNativePlan : Except Diagnostic Backend.Impact.Plan :=
  Backend.Impact.lower QualifiedCoinCellReset.state qualifiedCoinCellClear

#guard match qualifiedCoinCellResetNativePlan with
  | .ok plan =>
    match plan.operations, plan.activityGuards with
    | [.push (.field (.native 1)) Bool.false, .pushFields schema values Bool.true, .insert 1],
      [] =>
        isZeroQualifiedCoinFields values && plan.fieldGroups.length == 3 &&
        match QualifiedCoinCellReset.state with
        | [_, {kind := .tree (.composite environment type), ..}] =>
          match Backend.Impact.recordSchema environment type with
          | .ok expectedSchema =>
            schema == expectedSchema &&
              match Backend.Impact.Op.fields (.pushFields schema values Bool.true) with
              | .native 0x11 :: .native 1 :: .native 4 :: .native 32 ::
                  .native 32 :: .native 16 :: .native 8 :: _ => Bool.true
              | _ => Bool.false
          | .error _ => Bool.false
        | _ => Bool.false
    | _, _ => Bool.false
  | .error _ => Bool.false

#guard match qualifiedCoinCellResetNativePlan with
  | .ok plan =>
    match Backend.Impact.Plan.toJson qualifiedCoinCellResetContext [] plan with
    | .ok (.arr operations) => operations.size == 3
    | _ => Bool.false
  | .error _ => Bool.false

#guard match Backend.Impact.lower QualifiedCoinCellReset.state qualifiedCoinCellGuardedClear with
  | .ok plan =>
    match plan.activityGuards with
    | [none, none, some (.ref "enabled"), some (.ref "enabled"), some (.ref "enabled")] =>
      match plan.operations.drop 2 with
      | [.push (.field (.native 1)) Bool.false, .pushFields _ _ Bool.true, .insert 1] =>
        Bool.true
      | _ => Bool.false
    | _ => Bool.false
  | .error _ => Bool.false
