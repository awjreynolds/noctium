import Noctium.Backend.Impact
import Noctium.Compiler
import Noctium.Disclosure
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit nestedShieldedReceiveInputs where
  public owner : Bytes32
  private nonce : Bytes32
  private color : Bytes32
  private amount : UInt 128
end

noctium_contract NestedShieldedReceive where
  tree coinMaps : Bytes32 => Bytes32 => struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry receive uses nestedShieldedReceiveInputs where
    receiveShieldedToMap(coinMaps[owner], disclose(nonce), disclose(color), disclose(amount))
  end
end

private def nestedShieldedReceiveEntry : Entrypoint :=
  match NestedShieldedReceive.entrypoints with
  | found :: _ => found
  | [] => {name := "missing", circuit := {name := "missing"}}

#guard (nestedShieldedReceiveEntry.validate Capabilities.source NestedShieldedReceive.state).isOk
#guard (Disclosure.entrypoint nestedShieldedReceiveEntry).isOk
#guard nestedShieldedReceiveEntry.effectGuards.all Option.isNone

#guard match nestedShieldedReceiveEntry.effects with
  | [ .memberPath "coinMaps" _
        [.mk (.bytes 32) (.ref "owner"), .mk (.bytes 32) (.disclose _ (.ref "nonce"))]
    , .require _
    , .readContractAddress _
    , .receiveShieldedToMap "coinMaps" _ _ _ _
        [.mk (.bytes 32) (.ref "owner")] ] => Bool.true
  | _ => Bool.false

#guard match Backend.Impact.lower NestedShieldedReceive.state nestedShieldedReceiveEntry with
  | .ok plan =>
      let receives := plan.operations.filter fun operation =>
        match operation with
        | .receiveShieldedToMap .. => Bool.true
        | _ => Bool.false
      match receives with
      | [operation] => operation.fieldGroups.length == 16 &&
          match operation.fieldGroups[6]? with
          | some [Expr.native 0x71, Expr.native 1, Expr.native 1, Expr.native 0,
              Expr.native 1, Expr.native 32,
              Expr.bytesField (.ref "owner") 0, Expr.bytesField (.ref "owner") 1] => Bool.true
          | _ => Bool.false
      | _ => Bool.false
  | .error _ => Bool.false

private def nestedShieldedReceivePlanJson : Except String Lean.Json := do
  let lowered := Backend.Impact.lower NestedShieldedReceive.state nestedShieldedReceiveEntry
  let plan ← lowered.mapError (·.message)
  pure (Compiler.nativePlanJson TargetProfile.selected321 `NestedShieldedReceive
    NestedShieldedReceive.state none nestedShieldedReceiveEntry plan)

#guard match nestedShieldedReceivePlanJson with
  | .ok plan =>
      match (plan.getObjVal? "operations").toOption with
      | some (.arr operations) => operations.any fun operation =>
          operation.getObjValD "op" == Lean.toJson ("receiveShieldedToMap" : String) &&
          match operation.getObjValD "keys" with
          | .arr #[key] => key.getObjValD "alignment" == Lean.toJson ("bytes32" : String) &&
              (key.getObjVal? "expression").isOk
          | _ => Bool.false
      | _ => Bool.false
  | .error _ => Bool.false

#guard match nestedShieldedReceiveEntry.effects.find? (fun effect => match effect with
    | .receiveShieldedToMap .. => Bool.true
    | _ => Bool.false) with
  | some (.receiveShieldedToMap name nonce color amount selfAddress _) =>
    let invalidDeclarations := NestedShieldedReceive.state.map fun declaration =>
      match declaration.kind with
      | .tree (.map _ child) => {declaration with kind := .tree (.map (.uint 255) child)}
      | _ => declaration
    let effect := Effect.receiveShieldedToMap name nonce color amount selfAddress
      [.mk (.uint 255) (.uint 255 1)]
    match Backend.Impact.appendEffect invalidDeclarations effect {} with
    | .error message => message == "qualified coin Map parent keys must be Bytes32"
    | .ok _ => Bool.false
  | _ => Bool.false

noctium_circuit nestedShieldedReceiveTooDeepInputs where
  public owner : Bytes32
  public group : Bytes32
  private nonce : Bytes32
  private color : Bytes32
  private amount : UInt 128
end

/- error: receiveShieldedToMap supports at most one Bytes32 parent Map key -/
#guard_msgs (substring := true) in
noctium_contract NestedShieldedReceiveTooDeep where
  tree coinMaps : Bytes32 => Bytes32 => Bytes32 => struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry receive uses nestedShieldedReceiveTooDeepInputs where
    receiveShieldedToMap(coinMaps[owner][group], disclose(nonce), disclose(color), disclose(amount))
  end
end
