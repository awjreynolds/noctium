import Noctium.Backend.Impact
import Noctium.Compiler
import Noctium.Disclosure
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit partialReceiveInputs where
  public domain : Bytes32
  private nonce : Bytes32
  private color : Bytes32
end

noctium_circuit partialSpendInputs where
  private nonce : Bytes32
  private sendAmount : UInt 128
  private recipient : Bytes32
end

noctium_contract ShieldedMapPartialSpend where
  tree pot : Bytes32 => struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry tip uses partialReceiveInputs where
    mintShielded(domain, 5)
    receiveShieldedToMap(pot, disclose(nonce), disclose(color), 5)
  end

  entry spend uses partialSpendInputs where
    sendShieldedFromMap(pot, disclose(nonce), disclose(sendAmount), disclose(recipient))
  end
end

private def partialSpendEntry : Entrypoint :=
  match ShieldedMapPartialSpend.entrypoints with
  | _ :: found :: _ => found
  | _ => {name := "missing", circuit := {name := "missing"}}

private def isReference {ty : Ty} (value : Expr ty) (name : String) : _root_.Bool :=
  match value with
  | .ref found => found == name
  | _ => _root_.Bool.false

private def isDisclosedReference {ty : Ty} (value : Expr ty) (name : String) : _root_.Bool :=
  match value with
  | .disclose _ released => isReference released name
  | _ => _root_.Bool.false

private def isDisclosedPathReference (key : PathKey) (name : String) : _root_.Bool :=
  match key with
  | .mk (.bytes 32) value => isDisclosedReference value name
  | _ => _root_.Bool.false

private def sendsRecordedCoin (effect : Effect) : _root_.Bool :=
  match effect with
  | .sendShieldedFromMap state nonce color inputAmount sendAmount recipient address =>
      state == "pot" &&
      isReference nonce "noctium_send_coin_0_nonce" &&
      isReference color "noctium_send_coin_0_color" &&
      isReference inputAmount "noctium_send_coin_0_value" &&
      isDisclosedReference sendAmount "sendAmount" &&
      isDisclosedReference recipient "recipient" &&
      isReference address "noctium_send_address_2"
  | _ => _root_.Bool.false

private def receivesUsingSendAddress (effect : Effect) : _root_.Bool :=
  match effect with
  | .receiveShieldedToMap state _ _ _ address _ =>
      state == "pot" && isReference address "noctium_send_address_2"
  | _ => _root_.Bool.false

#guard partialSpendEntry.name == "spend"
#guard partialSpendEntry.effects.length == 8
#guard partialSpendEntry.effectGuards.length == 8 &&
  partialSpendEntry.effectGuards.all Option.isNone
#guard match partialSpendEntry.effects with
  | [.readCompositePath "pot" _ [nonceKey] _ fields, .require _,
      .readContractAddress _, send, .removePath "pot" [removeKey],
      .memberPath "pot" _ [_], .require _, receive] =>
        isDisclosedPathReference nonceKey "nonce" &&
        isDisclosedPathReference removeKey "nonce" &&
        fields.map Prod.snd == [Ty.bytes 32, Ty.bytes 32,
          Ty.uint (2 ^ 128 - 1), Ty.uint (2 ^ 64 - 1)] &&
        fields.map Prod.fst == [
          "noctium_send_coin_0_nonce",
          "noctium_send_coin_0_color",
          "noctium_send_coin_0_value",
          "noctium_send_coin_0_mtIndex"] &&
        sendsRecordedCoin send && receivesUsingSendAddress receive
  | _ => _root_.Bool.false
#guard (Disclosure.entrypoint partialSpendEntry).isOk
#guard (partialSpendEntry.validate Capabilities.source ShieldedMapPartialSpend.state).isOk

#guard match Backend.Impact.lower ShieldedMapPartialSpend.state partialSpendEntry with
  | .ok plan =>
      match plan.operations.filter (fun operation =>
        match operation with
        | .sendShieldedFromMap .. | .mapRemove .. | .receiveShieldedToMap .. => _root_.Bool.true
        | _ => _root_.Bool.false) with
      | [.sendShieldedFromMap .., .mapRemove slot _, .receiveShieldedToMap receiveSlot ..] =>
          slot == receiveSlot &&
          (plan.operations.filter (fun operation =>
            match operation with
            | .readContractAddress _ => _root_.Bool.true
            | _ => _root_.Bool.false)).length == 1 &&
          (plan.operations.find? (fun operation =>
            match operation with
            | .sendShieldedFromMap .. => _root_.Bool.true
            | _ => _root_.Bool.false)).map (·.fieldGroups.length) == some 18 &&
          (plan.operations.find? (fun operation =>
            match operation with
            | .receiveShieldedToMap .. => _root_.Bool.true
            | _ => _root_.Bool.false)).map (·.fieldGroups.length) == some 16
      | _ => _root_.Bool.false
  | .error _ => _root_.Bool.false

private def partialBytes (byte : Nat) : Value := .bytes 32 (List.replicate 32 byte)

private def partialInputs : EvalEnv := [
  ("nonce", partialBytes 1),
  ("sendAmount", .uint (2 ^ 128 - 1) 2),
  ("recipient", partialBytes 2)]

private def partialState : LedgerState := {
  trees := [("pot", .map [
    (partialBytes 1, .composite (.structure "ShieldedMapPartialSpend.Coin") [
      partialBytes 1,
      partialBytes 3,
      .uint (2 ^ 128 - 1) 5,
      .uint (2 ^ 64 - 1) 0])])]
}

private def partialContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by partial shielded send fixture"
  ownContractAddress := some (List.replicate 32 4)
}

#guard match Entrypoint.run partialContext partialSpendEntry partialInputs partialState with
  | .error message => message == "reference evaluator cannot determine the native shielded change index"
  | .ok _ => _root_.Bool.false
