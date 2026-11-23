import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit rawShieldedSpendTipInputs where
  public domain : Bytes32
  private nonce : Bytes32
  private color : Bytes32
end

noctium_circuit rawShieldedSpendInputs where
  private nonce : Bytes32
  private recipient : Bytes32
  private inputNullifier : Bytes32
  private outputCommitment : Bytes32
end

noctium_contract FundedRawShieldedSpend where
  tree pot : Bytes32 => struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry tip uses rawShieldedSpendTipInputs where
    mintShielded(domain, 5)
    receiveShieldedToMap(pot, disclose(nonce), disclose(color), 5)
  end

  entry spendRaw uses rawShieldedSpendInputs where
    member pot[disclose(nonce)] as present
    require present
    claimShielded(nullifier, disclose(inputNullifier))
    claimShielded(spend, disclose(outputCommitment))
    remove pot[disclose(nonce)]
  end
end

#guard match FundedRawShieldedSpend.entrypoints.find? (·.name == "spendRaw") with
  | some operation =>
    match operation.effects with
    | [.memberPath "pot" _ [_], .require _,
       .claimShielded .nullifier (.disclose _ (.ref inputNullifier)),
       .claimShielded .spend (.disclose _ (.ref outputCommitment)),
       .removePath "pot" [_]] =>
      inputNullifier == "inputNullifier" && outputCommitment == "outputCommitment" &&
      (Backend.Zkir.lowerEntrypoint FundedRawShieldedSpend.state operation).isOk
    | _ => _root_.Bool.false
  | none => _root_.Bool.false
