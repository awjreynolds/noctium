import Noctium.Backend.Impact
import Noctium.Compiler
import Noctium.Disclosure
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit immediateChangeInputs where
  public domain : Bytes32
  private nonce : Bytes32
  private color : Bytes32
  private sendAmount : UInt 128
  private recipient : Bytes32
end

noctium_contract ShieldedImmediateChange where
  tree pot : Bytes32 => struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry splitImmediateShielded uses immediateChangeInputs where
    mintShielded(domain, 5)
    receiveShieldedToMap(pot, disclose(nonce), disclose(color), 5)
    sendShieldedFromMap(pot, disclose(nonce), disclose(sendAmount), disclose(recipient))
  end
end

private def immediateChangeEntry : Entrypoint :=
  ShieldedImmediateChange.entrypoints.find? (·.name == "splitImmediateShielded") |>.getD
    {name := "missing", circuit := {name := "missing"}}

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

private def receivesMintedCoin (effect : Effect) : _root_.Bool :=
  match effect with
  | .receiveShieldedToMap state nonce color amount address _ =>
      state == "pot" &&
      isDisclosedReference nonce "nonce" &&
      isDisclosedReference color "color" &&
      (match amount with
        | .uint maximum 5 => maximum == 2 ^ 128 - 1
        | _ => _root_.Bool.false) &&
      isReference address "noctium_receive_address_1"
  | _ => _root_.Bool.false

private def sendsRecordedCoin (effect : Effect) : _root_.Bool :=
  match effect with
  | .sendShieldedFromMap state nonce color inputAmount sendAmount recipient address =>
      state == "pot" &&
      isReference nonce "noctium_send_coin_5_nonce" &&
      isReference color "noctium_send_coin_5_color" &&
      isReference inputAmount "noctium_send_coin_5_value" &&
      isDisclosedReference sendAmount "sendAmount" &&
      isDisclosedReference recipient "recipient" &&
      isReference address "noctium_send_address_7"
  | _ => _root_.Bool.false

private def receivesBookedChange (effect : Effect) : _root_.Bool :=
  match effect with
  | .receiveShieldedToMap state _ color _ address _ =>
      state == "pot" &&
      isReference color "noctium_send_coin_5_color" &&
      isReference address "noctium_send_address_7"
  | _ => _root_.Bool.false

#guard immediateChangeEntry.name == "splitImmediateShielded"
#guard immediateChangeEntry.effects.length == 13
#guard immediateChangeEntry.effectGuards.length == 13 &&
  immediateChangeEntry.effectGuards.all Option.isNone
#guard match immediateChangeEntry.effects with
  | [.mintShielded .., .memberPath "pot" _ [initialKey], .require _,
      .readContractAddress _, initialReceive, .readCompositePath "pot" _ [readKey] _ fields,
      .require _, .readContractAddress _, send, .removePath "pot" [removeKey],
      .memberPath "pot" _ [_], .require _, changeReceive] =>
        isDisclosedPathReference initialKey "nonce" &&
        receivesMintedCoin initialReceive &&
        isDisclosedPathReference readKey "nonce" &&
        isDisclosedPathReference removeKey "nonce" &&
        fields.map Prod.fst == [
          "noctium_send_coin_5_nonce",
          "noctium_send_coin_5_color",
          "noctium_send_coin_5_value",
          "noctium_send_coin_5_mtIndex"] &&
        fields.map Prod.snd == [Ty.bytes 32, Ty.bytes 32,
          Ty.uint (2 ^ 128 - 1), Ty.uint (2 ^ 64 - 1)] &&
        sendsRecordedCoin send && receivesBookedChange changeReceive
  | _ => _root_.Bool.false
#guard (Disclosure.entrypoint immediateChangeEntry).isOk
#guard (immediateChangeEntry.validate Capabilities.source ShieldedImmediateChange.state).isOk

#guard match Backend.Impact.lower ShieldedImmediateChange.state immediateChangeEntry with
  | .ok plan =>
      match plan.operations.filter (fun operation =>
        match operation with
        | .receiveShieldedToMap .. | .sendShieldedFromMap .. | .mapRemove .. => _root_.Bool.true
        | _ => _root_.Bool.false) with
      | [.receiveShieldedToMap inputSlot .., send@(.sendShieldedFromMap ..),
          .mapRemove removeSlot _, .receiveShieldedToMap changeSlot ..] =>
          inputSlot == removeSlot && removeSlot == changeSlot &&
          send.fieldGroups.length == 18
      | _ => _root_.Bool.false
  | .error _ => _root_.Bool.false
