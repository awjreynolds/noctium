import Noctium.Backend.Impact
import Noctium.Compiler
import Noctium.Disclosure
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit shieldedReceiveInputs where
  private nonce : Bytes32
  private color : Bytes32
  private amount : UInt 128
end

noctium_contract ShieldedReceive where
  tree pot : Bytes32 => struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry tip uses shieldedReceiveInputs where
    receiveShieldedToMap(pot, disclose(nonce), disclose(color), disclose(amount))
  end
end

private def shieldedReceiveEntry : Entrypoint :=
  match ShieldedReceive.entrypoints with
  | found :: _ => found
  | [] => {name := "missing", circuit := {name := "missing"}}

#guard shieldedReceiveEntry.effects.length == 4
#guard shieldedReceiveEntry.effectGuards.length == 4 &&
  shieldedReceiveEntry.effectGuards.all Option.isNone
#guard match shieldedReceiveEntry.effects with
  | [.memberPath "pot" _ [_], .require _, .readContractAddress _,
      .receiveShieldedToMap "pot" _ _ _ _ []] => Bool.true
  | _ => Bool.false
#guard (Disclosure.entrypoint shieldedReceiveEntry).isOk
#guard (shieldedReceiveEntry.validate Capabilities.source ShieldedReceive.state).isOk

#guard match ShieldedReceive.state with
  | [{kind := .tree (.map _ (.composite environment recordType)), ..}] =>
      match Backend.Impact.recordSchema environment recordType with
      | .ok schema => schema != Lean.Json.null
      | .error _ => Bool.false
  | _ => Bool.false

private def shieldedReceiveWrongState : List StateDecl :=
  ShieldedReceive.state.map fun declaration =>
    match declaration.kind with
    | .tree (.map keyTy (.composite environment (.structure typeId))) =>
        let structures := environment.structures.map fun structDecl =>
          if structDecl.id == typeId then
            {structDecl with fields := structDecl.fields.map fun field =>
              if field.name == "value" then
                {field with type := .scalar (.uint (2 ^ 64 - 1))}
              else field}
          else structDecl
        {declaration with kind := .tree (.map keyTy
          (.composite {environment with structures} (.structure typeId)))}
    | _ => declaration

#guard match shieldedReceiveEntry.validate Capabilities.source shieldedReceiveWrongState with
  | .error diagnostic => diagnostic.message.contains "shielded coin map record must be flat"
  | .ok _ => Bool.false

private def hasCompactReceiveIndex (operation : Backend.Impact.Op) : _root_.Bool :=
  match operation.fieldGroups[6]? with
  | some [Expr.native 0x70, Expr.native 1, Expr.native 1, Expr.native 0] => Bool.true
  | _ => Bool.false

#guard match Backend.Impact.lower ShieldedReceive.state shieldedReceiveEntry with
  | .ok plan =>
      let receives := plan.operations.filter fun operation =>
        match operation with
        | .receiveShieldedToMap .. => Bool.true
        | _ => Bool.false
      match receives with
      | [operation] => operation.fieldGroups.length == 16 &&
          hasCompactReceiveIndex operation
      | _ => Bool.false
  | .error _ => Bool.false

private def shieldedReceiveUndisclosed : Entrypoint :=
  {shieldedReceiveEntry with effects := shieldedReceiveEntry.effects.map fun effect =>
    match effect with
    | .receiveShieldedToMap state _ _ amount selfAddress keys =>
        .receiveShieldedToMap state (.ref "nonce") (.ref "color") amount selfAddress keys
    | other => other}

#guard match Disclosure.entrypoint shieldedReceiveUndisclosed with
  | .error diagnostic => diagnostic.message.contains "undisclosed private parameter 'nonce'"
  | .ok _ => Bool.false

private def receiveBytes (byte : Nat) : Value := .bytes 32 (List.replicate 32 byte)

private def shieldedReceiveInputValues : EvalEnv := [
  ("nonce", receiveBytes 1),
  ("color", receiveBytes 2),
  ("amount", .uint (2 ^ 128 - 1) 5)
]

private def shieldedReceiveContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by shielded receive fixture"
}

private def shieldedReceiveDuplicateState : LedgerState := {
  trees := [("pot", .map [
    (receiveBytes 1, .composite (.structure "ShieldedReceive.Coin") [
      receiveBytes 1,
      receiveBytes 2,
      .uint (2 ^ 128 - 1) 5,
      .uint (2 ^ 64 - 1) 0
    ])
  ])]
}

#guard match Entrypoint.run shieldedReceiveContext shieldedReceiveEntry
    shieldedReceiveInputValues shieldedReceiveDuplicateState with
  | .error message => message == "state transition guard failed"
  | .ok _ => Bool.false

#guard match Entrypoint.run
    {shieldedReceiveContext with ownContractAddress := some (List.replicate 32 3)}
    shieldedReceiveEntry shieldedReceiveInputValues
    {trees := [("pot", .map [])]} with
  | .error message =>
      message == "reference evaluator cannot determine the native shielded receive index"
  | .ok _ => Bool.false
