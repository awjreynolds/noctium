-- SPDX-License-Identifier: MIT
-- Copyright (c) 2025 Zeppelin Group Ltd
-- Adapted from OpenZeppelin Compact Contracts, ConfidentialFungibleToken.
-- Reference: f85f1a23685c6bbedfc8c2589ae3aa128aff7c46.
import Noctium.Frontend

open scoped Noctium

namespace OpenZeppelinPort

noctium_witness freshSeed() : Bytes32
noctium_witness plaintextBalance(c1 : JubjubPoint, c2 : JubjubPoint) : UInt 248

noctium_private_state Wallet where
  cell accountSecret : Bytes32
  cell encryptionSecret : Bytes32
end

noctium_witness_circuit registerAccount where
  read private Wallet.accountSecret as accountSecret
  read private Wallet.encryptionSecret as encryptionSecret
  public accountId : Bytes32
  public pk : JubjubPoint
  let identity : JubjubPoint := jubjubFromCoordinates(0, 1)
  let derivedAccountId : Bytes32 := persistentHash32(accountSecret)
  let encryptionScalar : JubjubScalar := jubjubScalarFromNative(degradeToNative(
    persistentHashVector32([bytes32("ElGamal:secretToScalar"), encryptionSecret])))
  let derivedPk : JubjubPoint := jubjubMulGenerator(encryptionScalar)
  prove eq(accountId, derivedAccountId)
  prove eq(pk, derivedPk)
  prove eq(eq(derivedPk, identity), false)
  output keyX : Native := disclose(jubjubX(derivedPk))
  output keyY : Native := disclose(jubjubY(derivedPk))
end

noctium_witness_circuit creditPending where
  private recipient : Bytes32
  private value : UInt 128
  public recipientPk : JubjubPoint
  public previousC1X : Native
  public previousC1Y : Native
  public previousC2X : Native
  public previousC2Y : Native
  public epoch : UInt 64
  let seed : Bytes32 := witness freshSeed()
  let key : JubjubPoint := recipientPk
  let previousC1 : JubjubPoint := jubjubFromCoordinates(previousC1X, previousC1Y)
  let previousC2 : JubjubPoint := jubjubFromCoordinates(previousC2X, previousC2Y)
  let valueField : Native := cast(Native, value)
  let valuePoint : JubjubPoint := jubjubMulGenerator(jubjubScalarFromNative(valueField))
  let countHash : Bytes32 := persistentHashNative(cast(Native, epoch))
  let balanceR : JubjubScalar := jubjubScalarFromNative(degradeToNative(
    persistentHashVector32([seed, bytes32("credit_balance"), recipient, countHash])))
  let memoR : JubjubScalar := jubjubScalarFromNative(degradeToNative(
    persistentHashVector32([seed, bytes32("credit_memo"), recipient, countHash])))
  prove eq(eq(jubjubScalarToNative(balanceR), 0), false)
  prove eq(eq(jubjubScalarToNative(memoR), 0), false)
  prove eq(eq(recipient, bytes32("")), false)
  let nextC1 : JubjubPoint := jubjubAdd(previousC1, jubjubMulGenerator(balanceR))
  let nextC2 : JubjubPoint := jubjubAdd(
    jubjubAdd(previousC2, valuePoint), jubjubMul(key, balanceR))
  let ephemeral : JubjubPoint := jubjubMulGenerator(memoR)
  let shared : JubjubPoint := jubjubMul(key, memoR)
  let memoDigest : Bytes32 := persistentHashPoint(shared)
  let memoMask : Native := degradeToNative(persistentHashVector32([
    memoDigest, bytes32("OZ_CFT_ecdh_memo_v1")]))
  let memoValue : Native := add(valueField, memoMask)
  output nextC1X : Native := disclose(jubjubX(nextC1))
  output nextC1Y : Native := disclose(jubjubY(nextC1))
  output nextC2X : Native := disclose(jubjubX(nextC2))
  output nextC2Y : Native := disclose(jubjubY(nextC2))
  output memoX : Native := disclose(jubjubX(ephemeral))
  output memoY : Native := disclose(jubjubY(ephemeral))
  output memoAmount : Native := disclose(memoValue)
end

noctium_witness_circuit sweepPending where
  read private Wallet.accountSecret as accountSecret
  read private Wallet.encryptionSecret as encryptionSecret
  public accountId : Bytes32
  public balanceC1X : Native
  public balanceC1Y : Native
  public balanceC2X : Native
  public balanceC2Y : Native
  public pendingC1X : Native
  public pendingC1Y : Native
  public pendingC2X : Native
  public pendingC2Y : Native
  let identity : JubjubPoint := jubjubFromCoordinates(0, 1)
  let derivedAccountId : Bytes32 := persistentHash32(accountSecret)
  let encryptionScalar : JubjubScalar := jubjubScalarFromNative(degradeToNative(
    persistentHashVector32([bytes32("ElGamal:secretToScalar"), encryptionSecret])))
  let derivedPk : JubjubPoint := jubjubMulGenerator(encryptionScalar)
  let balanceC1 : JubjubPoint := jubjubFromCoordinates(balanceC1X, balanceC1Y)
  let balanceC2 : JubjubPoint := jubjubFromCoordinates(balanceC2X, balanceC2Y)
  let pendingC1 : JubjubPoint := jubjubFromCoordinates(pendingC1X, pendingC1Y)
  let pendingC2 : JubjubPoint := jubjubFromCoordinates(pendingC2X, pendingC2Y)
  let nextC1 : JubjubPoint := jubjubAdd(balanceC1, pendingC1)
  let nextC2 : JubjubPoint := jubjubAdd(balanceC2, pendingC2)
  prove eq(accountId, derivedAccountId)
  prove eq(eq(derivedPk, identity), false)
  output keyX : Native := disclose(jubjubX(derivedPk))
  output keyY : Native := disclose(jubjubY(derivedPk))
  output nextC1X : Native := disclose(jubjubX(nextC1))
  output nextC1Y : Native := disclose(jubjubY(nextC1))
  output nextC2X : Native := disclose(jubjubX(nextC2))
  output nextC2Y : Native := disclose(jubjubY(nextC2))
end

noctium_witness_circuit transferValue where
  read private Wallet.accountSecret as accountSecret
  read private Wallet.encryptionSecret as encryptionSecret
  public accountId : Bytes32
  public recipient : Bytes32
  private value : UInt 128
  public recipientPk : JubjubPoint
  public balanceC1X : Native
  public balanceC1Y : Native
  public balanceC2X : Native
  public balanceC2Y : Native
  public pendingC1X : Native
  public pendingC1Y : Native
  public pendingC2X : Native
  public pendingC2Y : Native
  public epoch : UInt 64
  let seed : Bytes32 := witness freshSeed()
  let plaintext : UInt 248 := witness plaintextBalance(
    jubjubFromCoordinates(balanceC1X, balanceC1Y),
    jubjubFromCoordinates(balanceC2X, balanceC2Y))
  let identity : JubjubPoint := jubjubFromCoordinates(0, 1)
  let derivedAccountId : Bytes32 := persistentHash32(accountSecret)
  let encryptionScalar : JubjubScalar := jubjubScalarFromNative(degradeToNative(
    persistentHashVector32([bytes32("ElGamal:secretToScalar"), encryptionSecret])))
  let ownerPk : JubjubPoint := jubjubMulGenerator(encryptionScalar)
  let ownerC1 : JubjubPoint := jubjubFromCoordinates(balanceC1X, balanceC1Y)
  let ownerC2 : JubjubPoint := jubjubFromCoordinates(balanceC2X, balanceC2Y)
  let recipientC1 : JubjubPoint := jubjubFromCoordinates(pendingC1X, pendingC1Y)
  let recipientC2 : JubjubPoint := jubjubFromCoordinates(pendingC2X, pendingC2Y)
  let valueField : Native := cast(Native, value)
  let remaining : UInt 248 := sub(plaintext, cast(UInt 248, value))
  let valuePoint : JubjubPoint := jubjubMulGenerator(jubjubScalarFromNative(valueField))
  let debitHash : Bytes32 := persistentHashVector32([
    seed, bytes32("debit_balance")])
  let debitR : JubjubScalar := jubjubScalarFromNative(degradeToNative(debitHash))
  prove eq(eq(jubjubScalarToNative(debitR), 0), false)
  let nextOwnerC1 : JubjubPoint := jubjubAdd(ownerC1, jubjubNeg(jubjubMulGenerator(debitR)))
  let nextOwnerC2 : JubjubPoint := jubjubAdd(ownerC2,
    jubjubNeg(jubjubAdd(valuePoint, jubjubMul(ownerPk, debitR))))
  let recovered : JubjubPoint := jubjubAdd(nextOwnerC2,
    jubjubNeg(jubjubMul(nextOwnerC1, encryptionScalar)))
  let remainingPoint : JubjubPoint := jubjubMulGenerator(
    jubjubScalarFromNative(cast(Native, remaining)))
  let countHash : Bytes32 := persistentHashNative(cast(Native, epoch))
  let creditR : JubjubScalar := jubjubScalarFromNative(degradeToNative(
    persistentHashVector32([seed, bytes32("credit_balance"), recipient, countHash])))
  prove eq(eq(jubjubScalarToNative(creditR), 0), false)
  let nextRecipientC1 : JubjubPoint := jubjubAdd(
    recipientC1, jubjubMulGenerator(creditR))
  let nextRecipientC2 : JubjubPoint := jubjubAdd(
    jubjubAdd(recipientC2, valuePoint), jubjubMul(recipientPk, creditR))
  let memoR : JubjubScalar := jubjubScalarFromNative(degradeToNative(
    persistentHashVector32([seed, bytes32("credit_memo"), recipient, countHash])))
  prove eq(eq(jubjubScalarToNative(memoR), 0), false)
  let ephemeral : JubjubPoint := jubjubMulGenerator(memoR)
  let shared : JubjubPoint := jubjubMul(recipientPk, memoR)
  let memoDigest : Bytes32 := persistentHashPoint(shared)
  let memoMask : Native := degradeToNative(persistentHashVector32([
    memoDigest, bytes32("OZ_CFT_ecdh_memo_v1")]))
  let memoValue : Native := add(valueField, memoMask)
  prove eq(accountId, derivedAccountId)
  prove eq(eq(ownerPk, identity), false)
  prove eq(eq(recipientPk, identity), false)
  prove eq(jubjubAdd(ownerC2,
    jubjubNeg(jubjubMul(ownerC1, encryptionScalar))),
    jubjubMulGenerator(jubjubScalarFromNative(cast(Native, plaintext))))
  prove eq(recovered, remainingPoint)
  prove eq(eq(recipient, bytes32("")), false)
  output ownerKeyX : Native := disclose(jubjubX(ownerPk))
  output ownerKeyY : Native := disclose(jubjubY(ownerPk))
  output nextOwnerC1X : Native := disclose(jubjubX(nextOwnerC1))
  output nextOwnerC1Y : Native := disclose(jubjubY(nextOwnerC1))
  output nextOwnerC2X : Native := disclose(jubjubX(nextOwnerC2))
  output nextOwnerC2Y : Native := disclose(jubjubY(nextOwnerC2))
  output nextRecipientC1X : Native := disclose(jubjubX(nextRecipientC1))
  output nextRecipientC1Y : Native := disclose(jubjubY(nextRecipientC1))
  output nextRecipientC2X : Native := disclose(jubjubX(nextRecipientC2))
  output nextRecipientC2Y : Native := disclose(jubjubY(nextRecipientC2))
  output memoX : Native := disclose(jubjubX(ephemeral))
  output memoY : Native := disclose(jubjubY(ephemeral))
  output memoAmount : Native := disclose(memoValue)
end

noctium_witness_circuit debitBalance where
  read private Wallet.accountSecret as accountSecret
  read private Wallet.encryptionSecret as encryptionSecret
  public accountId : Bytes32
  private value : UInt 128
  public balanceC1X : Native
  public balanceC1Y : Native
  public balanceC2X : Native
  public balanceC2Y : Native
  let seed : Bytes32 := witness freshSeed()
  let plaintext : UInt 248 := witness plaintextBalance(
    jubjubFromCoordinates(balanceC1X, balanceC1Y),
    jubjubFromCoordinates(balanceC2X, balanceC2Y))
  let identity : JubjubPoint := jubjubFromCoordinates(0, 1)
  let derivedAccountId : Bytes32 := persistentHash32(accountSecret)
  let encryptionScalar : JubjubScalar := jubjubScalarFromNative(degradeToNative(
    persistentHashVector32([bytes32("ElGamal:secretToScalar"), encryptionSecret])))
  let ownerPk : JubjubPoint := jubjubMulGenerator(encryptionScalar)
  let ownerC1 : JubjubPoint := jubjubFromCoordinates(balanceC1X, balanceC1Y)
  let ownerC2 : JubjubPoint := jubjubFromCoordinates(balanceC2X, balanceC2Y)
  let remaining : UInt 248 := sub(plaintext, cast(UInt 248, value))
  let valueField : Native := cast(Native, value)
  let valuePoint : JubjubPoint := jubjubMulGenerator(jubjubScalarFromNative(valueField))
  let debitHash : Bytes32 := persistentHashVector32([
    seed, bytes32("debit_balance")])
  let debitR : JubjubScalar := jubjubScalarFromNative(degradeToNative(debitHash))
  let nextC1 : JubjubPoint := jubjubAdd(ownerC1, jubjubNeg(jubjubMulGenerator(debitR)))
  let nextC2 : JubjubPoint := jubjubAdd(ownerC2,
    jubjubNeg(jubjubAdd(valuePoint, jubjubMul(ownerPk, debitR))))
  let recovered : JubjubPoint := jubjubAdd(nextC2,
    jubjubNeg(jubjubMul(nextC1, encryptionScalar)))
  let remainingPoint : JubjubPoint := jubjubMulGenerator(
    jubjubScalarFromNative(cast(Native, remaining)))
  prove eq(accountId, derivedAccountId)
  prove eq(eq(ownerPk, identity), false)
  prove eq(eq(jubjubScalarToNative(debitR), 0), false)
  prove eq(jubjubAdd(ownerC2,
    jubjubNeg(jubjubMul(ownerC1, encryptionScalar))),
    jubjubMulGenerator(jubjubScalarFromNative(cast(Native, plaintext))))
  prove eq(recovered, remainingPoint)
  output keyX : Native := disclose(jubjubX(ownerPk))
  output keyY : Native := disclose(jubjubY(ownerPk))
  output nextC1X : Native := disclose(jubjubX(nextC1))
  output nextC1Y : Native := disclose(jubjubY(nextC1))
  output nextC2X : Native := disclose(jubjubX(nextC2))
  output nextC2Y : Native := disclose(jubjubY(nextC2))
end

noctium_witness_circuit approveEscrow where
  read private Wallet.accountSecret as accountSecret
  read private Wallet.encryptionSecret as encryptionSecret
  public accountId : Bytes32
  public spender : Bytes32
  private value : UInt 128
  public spenderPk : JubjubPoint
  public balanceC1 : JubjubPoint
  public balanceC2 : JubjubPoint
  public previousOwnerC1 : JubjubPoint
  public previousOwnerC2 : JubjubPoint
  let identity : JubjubPoint := jubjubFromCoordinates(0, 1)
  let derivedAccountId : Bytes32 := persistentHash32(accountSecret)
  let encryptionScalar : JubjubScalar := jubjubScalarFromNative(degradeToNative(
    persistentHashVector32([bytes32("ElGamal:secretToScalar"), encryptionSecret])))
  let ownerPk : JubjubPoint := jubjubMulGenerator(encryptionScalar)
  let refundedC1 : JubjubPoint := jubjubAdd(balanceC1, previousOwnerC1)
  let refundedC2 : JubjubPoint := jubjubAdd(balanceC2, previousOwnerC2)
  let plaintext : UInt 248 := witness plaintextBalance(refundedC1, refundedC2)
  let remaining : UInt 248 := sub(plaintext, cast(UInt 248, value))
  let valueField : Native := cast(Native, value)
  let valuePoint : JubjubPoint := jubjubMulGenerator(jubjubScalarFromNative(valueField))
  let seed : Bytes32 := witness freshSeed()
  let debitR : JubjubScalar := jubjubScalarFromNative(degradeToNative(
    persistentHashVector32([seed, bytes32("approve_debit")])))
  let spenderR : JubjubScalar := jubjubScalarFromNative(degradeToNative(
    persistentHashVector32([seed, bytes32("approve_spender_ct")])))
  let ownerR : JubjubScalar := jubjubScalarFromNative(degradeToNative(
    persistentHashVector32([seed, bytes32("approve_owner_ct")])))
  let ownerMemoR : JubjubScalar := jubjubScalarFromNative(degradeToNative(
    persistentHashVector32([seed, bytes32("approve_owner_memo")])))
  prove eq(eq(jubjubScalarToNative(debitR), 0), false)
  prove eq(eq(jubjubScalarToNative(spenderR), 0), false)
  prove eq(eq(jubjubScalarToNative(ownerR), 0), false)
  prove eq(eq(jubjubScalarToNative(ownerMemoR), 0), false)
  let newBalanceC1 : JubjubPoint := jubjubAdd(
    refundedC1, jubjubNeg(jubjubMulGenerator(debitR)))
  let newBalanceC2 : JubjubPoint := jubjubAdd(refundedC2,
    jubjubNeg(jubjubAdd(valuePoint, jubjubMul(ownerPk, debitR))))
  let recovered : JubjubPoint := jubjubAdd(newBalanceC2,
    jubjubNeg(jubjubMul(newBalanceC1, encryptionScalar)))
  let remainingPoint : JubjubPoint := jubjubMulGenerator(
    jubjubScalarFromNative(cast(Native, remaining)))
  let spenderC1 : JubjubPoint := jubjubMulGenerator(spenderR)
  let spenderC2 : JubjubPoint := jubjubAdd(
    valuePoint, jubjubMul(spenderPk, spenderR))
  let ownerC1 : JubjubPoint := jubjubMulGenerator(ownerR)
  let ownerC2 : JubjubPoint := jubjubAdd(valuePoint, jubjubMul(ownerPk, ownerR))
  let ownerMemoEphemeral : JubjubPoint := jubjubMulGenerator(ownerMemoR)
  let ownerMemoShared : JubjubPoint := jubjubMul(ownerPk, ownerMemoR)
  let ownerMemoDigest : Bytes32 := persistentHashPoint(ownerMemoShared)
  let ownerMemoMask : Native := degradeToNative(persistentHashVector32([
    ownerMemoDigest, bytes32("OZ_CFT_escrow_owner_v1")]))
  let ownerMemoCiphertext : Native := add(valueField, ownerMemoMask)
  prove eq(accountId, derivedAccountId)
  prove eq(eq(ownerPk, identity), false)
  prove eq(eq(spenderPk, identity), false)
  prove eq(jubjubAdd(refundedC2,
    jubjubNeg(jubjubMul(refundedC1, encryptionScalar))),
    jubjubMulGenerator(jubjubScalarFromNative(cast(Native, plaintext))))
  prove eq(recovered, remainingPoint)
  output ownerKeyX : Native := disclose(jubjubX(ownerPk))
  output ownerKeyY : Native := disclose(jubjubY(ownerPk))
  output nextBalanceC1X : Native := disclose(jubjubX(newBalanceC1))
  output nextBalanceC1Y : Native := disclose(jubjubY(newBalanceC1))
  output nextBalanceC2X : Native := disclose(jubjubX(newBalanceC2))
  output nextBalanceC2Y : Native := disclose(jubjubY(newBalanceC2))
  output spenderCtC1X : Native := disclose(jubjubX(spenderC1))
  output spenderCtC1Y : Native := disclose(jubjubY(spenderC1))
  output spenderCtC2X : Native := disclose(jubjubX(spenderC2))
  output spenderCtC2Y : Native := disclose(jubjubY(spenderC2))
  output ownerCtC1X : Native := disclose(jubjubX(ownerC1))
  output ownerCtC1Y : Native := disclose(jubjubY(ownerC1))
  output ownerCtC2X : Native := disclose(jubjubX(ownerC2))
  output ownerCtC2Y : Native := disclose(jubjubY(ownerC2))
  output ownerMemoEphemeralX : Native := disclose(jubjubX(ownerMemoEphemeral))
  output ownerMemoEphemeralY : Native := disclose(jubjubY(ownerMemoEphemeral))
  output ownerMemoAmount : Native := disclose(ownerMemoCiphertext)
end

noctium_circuit allowanceView where
  public owner : Bytes32
  public spender : Bytes32
end

noctium_witness_circuit transferFromEscrow where
  read private Wallet.accountSecret as accountSecret
  read private Wallet.encryptionSecret as encryptionSecret
  public fromAddress : Bytes32
  public spenderId : Bytes32
  public to : Bytes32
  private value : UInt 128
  public ownerPk : JubjubPoint
  public spenderC1 : JubjubPoint
  public spenderC2 : JubjubPoint
  public ownerC1 : JubjubPoint
  public ownerC2 : JubjubPoint
  public spendEpoch : UInt 64
  public recipientPk : JubjubPoint
  public pendingC1 : JubjubPoint
  public pendingC2 : JubjubPoint
  public creditEpoch : UInt 64
  let derivedSpenderId : Bytes32 := persistentHash32(accountSecret)
  let encryptionScalar : JubjubScalar := jubjubScalarFromNative(degradeToNative(
    persistentHashVector32([bytes32("ElGamal:secretToScalar"), encryptionSecret])))
  let derivedSpenderPk : JubjubPoint := jubjubMulGenerator(encryptionScalar)
  prove eq(spenderId, derivedSpenderId)
  let plaintextWide : UInt 248 := witness plaintextBalance(spenderC1, spenderC2)
  let escrowAmount : UInt 128 := cast(UInt 128, plaintextWide)
  prove eq(jubjubAdd(spenderC2,
    jubjubNeg(jubjubMul(spenderC1, encryptionScalar))),
    jubjubMulGenerator(jubjubScalarFromNative(cast(Native, escrowAmount))))
  let spendSeed : Bytes32 := witness freshSeed()
  let remaining : UInt 128 := sub(escrowAmount, value)
  let valueField : Native := cast(Native, value)
  let valuePoint : JubjubPoint := jubjubMulGenerator(jubjubScalarFromNative(valueField))
  let spendEpochBytes : Bytes32 := toBytes32(cast(Native, spendEpoch))
  let spenderR : JubjubScalar := jubjubScalarFromNative(degradeToNative(
    persistentHashVector32([spendSeed, bytes32("spend_escrow_spender"), fromAddress,
      spenderId, spendEpochBytes])))
  let ownerR : JubjubScalar := jubjubScalarFromNative(degradeToNative(
    persistentHashVector32([spendSeed, bytes32("spend_escrow_owner"), fromAddress,
      spenderId, spendEpochBytes])))
  let ownerMemoR : JubjubScalar := jubjubScalarFromNative(degradeToNative(
    persistentHashVector32([spendSeed, bytes32("spend_owner_memo"), fromAddress,
      spenderId, spendEpochBytes])))
  let nextSpenderC1 : JubjubPoint := jubjubAdd(
    spenderC1, jubjubNeg(jubjubMulGenerator(spenderR)))
  let nextSpenderC2 : JubjubPoint := jubjubAdd(spenderC2,
    jubjubNeg(jubjubAdd(valuePoint, jubjubMul(derivedSpenderPk, spenderR))))
  let nextOwnerC1 : JubjubPoint := jubjubAdd(
    ownerC1, jubjubNeg(jubjubMulGenerator(ownerR)))
  let nextOwnerC2 : JubjubPoint := jubjubAdd(ownerC2,
    jubjubNeg(jubjubAdd(valuePoint, jubjubMul(ownerPk, ownerR))))
  let ownerMemoEphemeral : JubjubPoint := jubjubMulGenerator(ownerMemoR)
  let ownerMemoShared : JubjubPoint := jubjubMul(ownerPk, ownerMemoR)
  let ownerMemoDigest : Bytes32 := persistentHashPoint(ownerMemoShared)
  let ownerMemoMask : Native := degradeToNative(persistentHashVector32([
    ownerMemoDigest, bytes32("OZ_CFT_escrow_owner_v1")]))
  let ownerMemoCiphertext : Native := add(cast(Native, remaining), ownerMemoMask)
  let spendRecovered : JubjubPoint := jubjubAdd(nextSpenderC2,
    jubjubNeg(jubjubMul(nextSpenderC1, encryptionScalar)))
  let remainingPoint : JubjubPoint := jubjubMulGenerator(
    jubjubScalarFromNative(cast(Native, remaining)))
  let creditSeed : Bytes32 := witness freshSeed()
  let creditCountHash : Bytes32 := persistentHashNative(cast(Native, creditEpoch))
  let creditR : JubjubScalar := jubjubScalarFromNative(degradeToNative(
    persistentHashVector32([creditSeed, bytes32("credit_balance"), to, creditCountHash])))
  let creditMemoR : JubjubScalar := jubjubScalarFromNative(degradeToNative(
    persistentHashVector32([creditSeed, bytes32("credit_memo"), to, creditCountHash])))
  let nextPendingC1 : JubjubPoint := jubjubAdd(pendingC1, jubjubMulGenerator(creditR))
  let nextPendingC2 : JubjubPoint := jubjubAdd(
    jubjubAdd(pendingC2, valuePoint), jubjubMul(recipientPk, creditR))
  let creditMemoEphemeral : JubjubPoint := jubjubMulGenerator(creditMemoR)
  let creditMemoShared : JubjubPoint := jubjubMul(recipientPk, creditMemoR)
  let creditMemoDigest : Bytes32 := persistentHashPoint(creditMemoShared)
  let creditMemoMask : Native := degradeToNative(persistentHashVector32([
    creditMemoDigest, bytes32("OZ_CFT_ecdh_memo_v1")]))
  let creditMemoCiphertext : Native := add(valueField, creditMemoMask)
  prove eq(spendRecovered, remainingPoint)
  output spenderKeyX : Native := disclose(jubjubX(derivedSpenderPk))
  output spenderKeyY : Native := disclose(jubjubY(derivedSpenderPk))
  output nextSpenderC1X : Native := disclose(jubjubX(nextSpenderC1))
  output nextSpenderC1Y : Native := disclose(jubjubY(nextSpenderC1))
  output nextSpenderC2X : Native := disclose(jubjubX(nextSpenderC2))
  output nextSpenderC2Y : Native := disclose(jubjubY(nextSpenderC2))
  output nextOwnerC1X : Native := disclose(jubjubX(nextOwnerC1))
  output nextOwnerC1Y : Native := disclose(jubjubY(nextOwnerC1))
  output nextOwnerC2X : Native := disclose(jubjubX(nextOwnerC2))
  output nextOwnerC2Y : Native := disclose(jubjubY(nextOwnerC2))
  output ownerMemoEphemeralX : Native := disclose(jubjubX(ownerMemoEphemeral))
  output ownerMemoEphemeralY : Native := disclose(jubjubY(ownerMemoEphemeral))
  output ownerMemoAmount : Native := disclose(ownerMemoCiphertext)
  output nextPendingC1X : Native := disclose(jubjubX(nextPendingC1))
  output nextPendingC1Y : Native := disclose(jubjubY(nextPendingC1))
  output nextPendingC2X : Native := disclose(jubjubX(nextPendingC2))
  output nextPendingC2Y : Native := disclose(jubjubY(nextPendingC2))
  output memoX : Native := disclose(jubjubX(creditMemoEphemeral))
  output memoY : Native := disclose(jubjubY(creditMemoEphemeral))
  output memoAmount : Native := disclose(creditMemoCiphertext)
end

noctium_witness_circuit burnFromEscrow where
  read private Wallet.accountSecret as accountSecret
  read private Wallet.encryptionSecret as encryptionSecret
  public fromAddress : Bytes32
  public spenderId : Bytes32
  private value : UInt 128
  public ownerPk : JubjubPoint
  public spenderC1 : JubjubPoint
  public spenderC2 : JubjubPoint
  public ownerC1 : JubjubPoint
  public ownerC2 : JubjubPoint
  public spendEpoch : UInt 64
  let derivedSpenderId : Bytes32 := persistentHash32(accountSecret)
  let encryptionScalar : JubjubScalar := jubjubScalarFromNative(degradeToNative(
    persistentHashVector32([bytes32("ElGamal:secretToScalar"), encryptionSecret])))
  let derivedSpenderPk : JubjubPoint := jubjubMulGenerator(encryptionScalar)
  prove eq(spenderId, derivedSpenderId)
  let plaintextWide : UInt 248 := witness plaintextBalance(spenderC1, spenderC2)
  let escrowAmount : UInt 128 := cast(UInt 128, plaintextWide)
  prove eq(jubjubAdd(spenderC2,
    jubjubNeg(jubjubMul(spenderC1, encryptionScalar))),
    jubjubMulGenerator(jubjubScalarFromNative(cast(Native, escrowAmount))))
  let spendSeed : Bytes32 := witness freshSeed()
  let remaining : UInt 128 := sub(escrowAmount, value)
  let valueField : Native := cast(Native, value)
  let valuePoint : JubjubPoint := jubjubMulGenerator(jubjubScalarFromNative(valueField))
  let spendEpochBytes : Bytes32 := toBytes32(cast(Native, spendEpoch))
  let spenderR : JubjubScalar := jubjubScalarFromNative(degradeToNative(
    persistentHashVector32([spendSeed, bytes32("spend_escrow_spender"), fromAddress,
      spenderId, spendEpochBytes])))
  let ownerR : JubjubScalar := jubjubScalarFromNative(degradeToNative(
    persistentHashVector32([spendSeed, bytes32("spend_escrow_owner"), fromAddress,
      spenderId, spendEpochBytes])))
  let ownerMemoR : JubjubScalar := jubjubScalarFromNative(degradeToNative(
    persistentHashVector32([spendSeed, bytes32("spend_owner_memo"), fromAddress,
      spenderId, spendEpochBytes])))
  let nextSpenderC1 : JubjubPoint := jubjubAdd(
    spenderC1, jubjubNeg(jubjubMulGenerator(spenderR)))
  let nextSpenderC2 : JubjubPoint := jubjubAdd(spenderC2,
    jubjubNeg(jubjubAdd(valuePoint, jubjubMul(derivedSpenderPk, spenderR))))
  let nextOwnerC1 : JubjubPoint := jubjubAdd(
    ownerC1, jubjubNeg(jubjubMulGenerator(ownerR)))
  let nextOwnerC2 : JubjubPoint := jubjubAdd(ownerC2,
    jubjubNeg(jubjubAdd(valuePoint, jubjubMul(ownerPk, ownerR))))
  let ownerMemoEphemeral : JubjubPoint := jubjubMulGenerator(ownerMemoR)
  let ownerMemoShared : JubjubPoint := jubjubMul(ownerPk, ownerMemoR)
  let ownerMemoDigest : Bytes32 := persistentHashPoint(ownerMemoShared)
  let ownerMemoMask : Native := degradeToNative(persistentHashVector32([
    ownerMemoDigest, bytes32("OZ_CFT_escrow_owner_v1")]))
  let ownerMemoCiphertext : Native := add(cast(Native, remaining), ownerMemoMask)
  let spendRecovered : JubjubPoint := jubjubAdd(nextSpenderC2,
    jubjubNeg(jubjubMul(nextSpenderC1, encryptionScalar)))
  let remainingPoint : JubjubPoint := jubjubMulGenerator(
    jubjubScalarFromNative(cast(Native, remaining)))
  prove eq(spendRecovered, remainingPoint)
  output spenderKeyX : Native := disclose(jubjubX(derivedSpenderPk))
  output spenderKeyY : Native := disclose(jubjubY(derivedSpenderPk))
  output nextSpenderC1X : Native := disclose(jubjubX(nextSpenderC1))
  output nextSpenderC1Y : Native := disclose(jubjubY(nextSpenderC1))
  output nextSpenderC2X : Native := disclose(jubjubX(nextSpenderC2))
  output nextSpenderC2Y : Native := disclose(jubjubY(nextSpenderC2))
  output nextOwnerC1X : Native := disclose(jubjubX(nextOwnerC1))
  output nextOwnerC1Y : Native := disclose(jubjubY(nextOwnerC1))
  output nextOwnerC2X : Native := disclose(jubjubX(nextOwnerC2))
  output nextOwnerC2Y : Native := disclose(jubjubY(nextOwnerC2))
  output ownerMemoEphemeralX : Native := disclose(jubjubX(ownerMemoEphemeral))
  output ownerMemoEphemeralY : Native := disclose(jubjubY(ownerMemoEphemeral))
  output ownerMemoAmount : Native := disclose(ownerMemoCiphertext)
end

noctium_witness_circuit clearMemoInput expose checkedCircuit where
  read private Wallet.accountSecret as accountSecret
  read private Wallet.encryptionSecret as encryptionSecret
  public accountId : Bytes32
  public expectedEpoch : UInt 64
  let derivedAccountId : Bytes32 := persistentHash32(accountSecret)
  let encryptionScalar : JubjubScalar := jubjubScalarFromNative(degradeToNative(
    persistentHashVector32([bytes32("ElGamal:secretToScalar"), encryptionSecret])))
  let derivedPk : JubjubPoint := jubjubMulGenerator(encryptionScalar)
  prove eq(accountId, derivedAccountId)
  output keyX : Native := disclose(jubjubX(derivedPk))
  output keyY : Native := disclose(jubjubY(derivedPk))
end

noctium_circuit accountView where
  public account : Bytes32
end

noctium_circuit noViewInputs where
end

noctium_circuit accountSecretInput where
  private secret : Bytes32
end

noctium_contract ConfidentialToken where
  tree encryptionKeys : Bytes32 => struct JubjubKey {
    x : Native
    y : Native
  }
  tree balances : Bytes32 => struct SpendableCiphertext {
    c1x : Native
    c1y : Native
    c2x : Native
    c2y : Native
  }
  tree pending : Bytes32 => struct PendingCiphertext {
    c1x : Native
    c1y : Native
    c2x : Native
    c2y : Native
  }
  tree memos : Bytes32 => List struct Memo {
    ephemeralX : Native
    ephemeralY : Native
    amount : Native
  }
  tree creditEpochs : Bytes32 => Counter
  cell initialized : Bool
  cell totalSupply : UInt 128
  tree escrow : Bytes32 => Bytes32 => struct EscrowEntry {
    spenderCtC1X : Native
    spenderCtC1Y : Native
    spenderCtC2X : Native
    spenderCtC2Y : Native
    ownerCtC1X : Native
    ownerCtC1Y : Native
    ownerCtC2X : Native
    ownerCtC2Y : Native
    ownerMemoEphemeralX : Native
    ownerMemoEphemeralY : Native
    ownerMemoAmount : Native
  }
  tree escrowSpendEpochs : Bytes32 => Bytes32 => Counter
  sealed cell name : OpaqueString
  sealed cell symbol : OpaqueString
  sealed cell decimals : UInt 8

  constructor(name_ : OpaqueString, symbol_ : OpaqueString, decimals_ : UInt 8) where
    initialize name := name_
    initialize symbol := symbol_
    initialize decimals := decimals_
    initialize initialized := true
  end

  entry registerWithKey uses registerAccount where
    read initialized as isInitialized
    require eq(isInitialized, true)
    member encryptionKeys[disclose(accountId)] as alreadyRegistered
    require eq(alreadyRegistered, false)
    insert encryptionKeys[disclose(accountId)] := fields(result.keyX, result.keyY)
    insert balances[disclose(accountId)] := fields(0, 1, 0, 1)
    insert pending[disclose(accountId)] := fields(0, 1, 0, 1)
    return caller : Bytes32 := accountId
  end

  entry mint uses creditPending arguments [recipient, value] where
    read initialized as isInitialized
    require eq(isInitialized, true)
    member encryptionKeys[disclose(recipient)] as registered
    require eq(registered, true)
    read encryptionKeys[disclose(recipient)] as recipientKey
    require eq(recipientKey_x, jubjubX(recipientPk))
    require eq(recipientKey_y, jubjubY(recipientPk))
    read pending[disclose(recipient)] as previousPending
    require eq(previousPending_c1x, previousC1X)
    require eq(previousPending_c1y, previousC1Y)
    require eq(previousPending_c2x, previousC2X)
    require eq(previousPending_c2y, previousC2Y)
    member memos[disclose(recipient)] as memoListPresent
    if eq(memoListPresent, false) then {
      reset memos[disclose(recipient)]
    } else {
    }
    member creditEpochs[disclose(recipient)] as epochPresent
    if eq(epochPresent, false) then {
      reset creditEpochs[disclose(recipient)]
    } else {
    }
    increment creditEpochs[disclose(recipient)] by 1
    read creditEpochs[disclose(recipient)] as actualEpoch
    require eq(actualEpoch, epoch)
    pushFront memos[disclose(recipient)] := fields(
      result.memoX, result.memoY, result.memoAmount)
    write pending[disclose(recipient)] := fields(
      result.nextC1X, result.nextC1Y, result.nextC2X, result.nextC2Y)
    read totalSupply as oldSupply
    write totalSupply := disclose(cast(UInt 128, add(oldSupply, value)))
  end

  entry sweep uses sweepPending where
    read initialized as isInitialized
    require eq(isInitialized, true)
    member encryptionKeys[disclose(accountId)] as registered
    require eq(registered, true)
    read encryptionKeys[disclose(accountId)] as storedKey
    require eq(storedKey_x, result.keyX)
    require eq(storedKey_y, result.keyY)
    read balances[disclose(accountId)] as oldBalance
    require eq(oldBalance_c1x, balanceC1X)
    require eq(oldBalance_c1y, balanceC1Y)
    require eq(oldBalance_c2x, balanceC2X)
    require eq(oldBalance_c2y, balanceC2Y)
    read pending[disclose(accountId)] as oldPending
    require eq(oldPending_c1x, pendingC1X)
    require eq(oldPending_c1y, pendingC1Y)
    require eq(oldPending_c2x, pendingC2X)
    require eq(oldPending_c2y, pendingC2Y)
    write balances[disclose(accountId)] := fields(
      result.nextC1X, result.nextC1Y, result.nextC2X, result.nextC2Y)
    write pending[disclose(accountId)] := fields(0, 1, 0, 1)
    return caller : Bytes32 := accountId
  end

  entry transfer uses transferValue where
    read initialized as isInitialized
    require eq(isInitialized, true)
    member encryptionKeys[disclose(accountId)] as senderRegistered
    require eq(senderRegistered, true)
    member encryptionKeys[disclose(recipient)] as recipientRegistered
    require eq(recipientRegistered, true)
    require eq(eq(accountId, recipient), false)
    read encryptionKeys[disclose(accountId)] as senderKey
    require eq(senderKey_x, result.ownerKeyX)
    require eq(senderKey_y, result.ownerKeyY)
    read encryptionKeys[disclose(recipient)] as recipientKey
    require eq(recipientKey_x, jubjubX(recipientPk))
    require eq(recipientKey_y, jubjubY(recipientPk))
    read balances[disclose(accountId)] as oldBalance
    require eq(oldBalance_c1x, balanceC1X)
    require eq(oldBalance_c1y, balanceC1Y)
    require eq(oldBalance_c2x, balanceC2X)
    require eq(oldBalance_c2y, balanceC2Y)
    read pending[disclose(recipient)] as oldPending
    require eq(oldPending_c1x, pendingC1X)
    require eq(oldPending_c1y, pendingC1Y)
    require eq(oldPending_c2x, pendingC2X)
    require eq(oldPending_c2y, pendingC2Y)
    member memos[disclose(recipient)] as memoListPresent
    if eq(memoListPresent, false) then {
      reset memos[disclose(recipient)]
    } else {
    }
    member creditEpochs[disclose(recipient)] as epochPresent
    if eq(epochPresent, false) then {
      reset creditEpochs[disclose(recipient)]
    } else {
    }
    increment creditEpochs[disclose(recipient)] by 1
    read creditEpochs[disclose(recipient)] as actualEpoch
    require eq(actualEpoch, epoch)
    write balances[disclose(accountId)] := fields(
      result.nextOwnerC1X, result.nextOwnerC1Y,
      result.nextOwnerC2X, result.nextOwnerC2Y)
    write pending[disclose(recipient)] := fields(
      result.nextRecipientC1X, result.nextRecipientC1Y,
      result.nextRecipientC2X, result.nextRecipientC2Y)
    pushFront memos[disclose(recipient)] := fields(
      result.memoX, result.memoY, result.memoAmount)
    return caller : Bytes32 := accountId
  end

  entry _move uses transferValue where
    read initialized as isInitialized
    require eq(isInitialized, true)
    member encryptionKeys[disclose(accountId)] as senderRegistered
    require eq(senderRegistered, true)
    member encryptionKeys[disclose(recipient)] as recipientRegistered
    require eq(recipientRegistered, true)
    read encryptionKeys[disclose(accountId)] as senderKey
    require eq(senderKey_x, result.ownerKeyX)
    require eq(senderKey_y, result.ownerKeyY)
    read encryptionKeys[disclose(recipient)] as recipientKey
    require eq(recipientKey_x, jubjubX(recipientPk))
    require eq(recipientKey_y, jubjubY(recipientPk))
    read balances[disclose(accountId)] as oldBalance
    require eq(oldBalance_c1x, balanceC1X)
    require eq(oldBalance_c1y, balanceC1Y)
    require eq(oldBalance_c2x, balanceC2X)
    require eq(oldBalance_c2y, balanceC2Y)
    read pending[disclose(recipient)] as oldPending
    require eq(oldPending_c1x, pendingC1X)
    require eq(oldPending_c1y, pendingC1Y)
    require eq(oldPending_c2x, pendingC2X)
    require eq(oldPending_c2y, pendingC2Y)
    member memos[disclose(recipient)] as memoListPresent
    if eq(memoListPresent, false) then {
      reset memos[disclose(recipient)]
    } else {
    }
    member creditEpochs[disclose(recipient)] as epochPresent
    if eq(epochPresent, false) then {
      reset creditEpochs[disclose(recipient)]
    } else {
    }
    increment creditEpochs[disclose(recipient)] by 1
    read creditEpochs[disclose(recipient)] as actualEpoch
    require eq(actualEpoch, epoch)
    write balances[disclose(accountId)] := fields(
      result.nextOwnerC1X, result.nextOwnerC1Y,
      result.nextOwnerC2X, result.nextOwnerC2Y)
    write pending[disclose(recipient)] := fields(
      result.nextRecipientC1X, result.nextRecipientC1Y,
      result.nextRecipientC2X, result.nextRecipientC2Y)
    pushFront memos[disclose(recipient)] := fields(
      result.memoX, result.memoY, result.memoAmount)
    return caller : Bytes32 := accountId
  end

  entry burn uses debitBalance where
    read initialized as isInitialized
    require eq(isInitialized, true)
    member encryptionKeys[disclose(accountId)] as registered
    require eq(registered, true)
    read encryptionKeys[disclose(accountId)] as senderKey
    require eq(senderKey_x, result.keyX)
    require eq(senderKey_y, result.keyY)
    read balances[disclose(accountId)] as oldBalance
    require eq(oldBalance_c1x, balanceC1X)
    require eq(oldBalance_c1y, balanceC1Y)
    require eq(oldBalance_c2x, balanceC2X)
    require eq(oldBalance_c2y, balanceC2Y)
    read totalSupply as oldSupply
    write balances[disclose(accountId)] := fields(
      result.nextC1X, result.nextC1Y, result.nextC2X, result.nextC2Y)
    write totalSupply := disclose(sub(oldSupply, value))
    return caller : Bytes32 := accountId
  end

  entry clearMemos uses clearMemoInput where
    read initialized as isInitialized
    require eq(isInitialized, true)
    member encryptionKeys[disclose(accountId)] as registered
    require eq(registered, true)
    read encryptionKeys[disclose(accountId)] as storedKey
    require eq(storedKey_x, result.keyX)
    require eq(storedKey_y, result.keyY)
    member memos[disclose(accountId)] as memoListPresent
    require eq(memoListPresent, true)
    read creditEpochs[disclose(accountId)] as actualEpoch
    require eq(actualEpoch, expectedEpoch)
    reset memos[disclose(accountId)]
  end

  entry totalSupply uses noViewInputs where
    read totalSupply as currentSupply
    return supply : UInt 128 := currentSupply
  end

  entry isRegistered uses accountView where
    member encryptionKeys[disclose(account)] as registered
    return value : Bool := registered
  end

  entry balanceOf uses accountView where
    read initialized as isInitialized
    require eq(isInitialized, true)
    member balances[disclose(account)] as balancePresent
    when eq(balancePresent, true) read balances[disclose(account)] as currentBalance
    return c1 : JubjubPoint := jubjubFromCoordinates(
      select(balancePresent, currentBalance_c1x, 0),
      select(balancePresent, currentBalance_c1y, 1))
    return c2 : JubjubPoint := jubjubFromCoordinates(
      select(balancePresent, currentBalance_c2x, 0),
      select(balancePresent, currentBalance_c2y, 1))
  end

  entry pendingOf uses accountView where
    read initialized as isInitialized
    require eq(isInitialized, true)
    member pending[disclose(account)] as pendingPresent
    when eq(pendingPresent, true) read pending[disclose(account)] as currentPending
    return c1 : JubjubPoint := jubjubFromCoordinates(
      select(pendingPresent, currentPending_c1x, 0),
      select(pendingPresent, currentPending_c1y, 1))
    return c2 : JubjubPoint := jubjubFromCoordinates(
      select(pendingPresent, currentPending_c2x, 0),
      select(pendingPresent, currentPending_c2y, 1))
  end

  entry computeAccountId uses accountSecretInput where
    return accountId : Bytes32 := disclose(persistentHash32(secret))
  end

  -- Reapproval first refunds the previous owner ciphertext into the spendable
  -- balance.  The old escrow record is then replaced with the new allowance.
  entry approve uses approveEscrow where
    read initialized as isInitialized
    require eq(isInitialized, true)
    require eq(eq(spender, bytes32("")), false)
    require eq(eq(spender, accountId), false)
    member encryptionKeys[disclose(accountId)] as ownerRegistered
    require eq(ownerRegistered, true)
    member encryptionKeys[disclose(spender)] as spenderRegistered
    require eq(spenderRegistered, true)
    read encryptionKeys[disclose(accountId)] as storedOwnerKey
    require eq(storedOwnerKey_x, result.ownerKeyX)
    require eq(storedOwnerKey_y, result.ownerKeyY)
    read encryptionKeys[disclose(spender)] as storedSpenderKey
    require eq(storedSpenderKey_x, jubjubX(spenderPk))
    require eq(storedSpenderKey_y, jubjubY(spenderPk))
    read balances[disclose(accountId)] as oldBalance
    require eq(oldBalance_c1x, jubjubX(balanceC1))
    require eq(oldBalance_c1y, jubjubY(balanceC1))
    require eq(oldBalance_c2x, jubjubX(balanceC2))
    require eq(oldBalance_c2y, jubjubY(balanceC2))
    member escrow[disclose(accountId)] as ownerEscrowPresent
    if eq(ownerEscrowPresent, false) then {
      insert escrow[disclose(accountId)] := emptyMap
    } else {
    }
    member escrow[disclose(accountId)][disclose(spender)] as storedAllowancePresent
    when eq(storedAllowancePresent, true)
      read escrow[disclose(accountId)][disclose(spender)] as previousEscrow
    require eq(jubjubX(previousOwnerC1), select(storedAllowancePresent, previousEscrow_ownerCtC1X, 0))
    require eq(jubjubY(previousOwnerC1), select(storedAllowancePresent, previousEscrow_ownerCtC1Y, 1))
    require eq(jubjubX(previousOwnerC2), select(storedAllowancePresent, previousEscrow_ownerCtC2X, 0))
    require eq(jubjubY(previousOwnerC2), select(storedAllowancePresent, previousEscrow_ownerCtC2Y, 1))
    remove escrow[disclose(accountId)][disclose(spender)]
    write balances[disclose(accountId)] := fields(
      result.nextBalanceC1X, result.nextBalanceC1Y,
      result.nextBalanceC2X, result.nextBalanceC2Y)
    insert escrow[disclose(accountId)][disclose(spender)] := fields(
      result.spenderCtC1X, result.spenderCtC1Y,
      result.spenderCtC2X, result.spenderCtC2Y,
      result.ownerCtC1X, result.ownerCtC1Y,
      result.ownerCtC2X, result.ownerCtC2Y,
      result.ownerMemoEphemeralX, result.ownerMemoEphemeralY,
      result.ownerMemoAmount)
    return caller : Bytes32 := accountId
  end

  entry allowance uses allowanceView where
    member escrow[disclose(owner)] as ownerPresent
    when eq(ownerPresent, true) member escrow[disclose(owner)][disclose(spender)] as allowancePresent
    when eq(allowancePresent, true)
      read escrow[disclose(owner)][disclose(spender)] as currentAllowance
    return spenderC1 : JubjubPoint := jubjubFromCoordinates(
      select(allowancePresent, currentAllowance_spenderCtC1X, 0),
      select(allowancePresent, currentAllowance_spenderCtC1Y, 1))
    return spenderC2 : JubjubPoint := jubjubFromCoordinates(
      select(allowancePresent, currentAllowance_spenderCtC2X, 0),
      select(allowancePresent, currentAllowance_spenderCtC2Y, 1))
    return ownerC1 : JubjubPoint := jubjubFromCoordinates(
      select(allowancePresent, currentAllowance_ownerCtC1X, 0),
      select(allowancePresent, currentAllowance_ownerCtC1Y, 1))
    return ownerC2 : JubjubPoint := jubjubFromCoordinates(
      select(allowancePresent, currentAllowance_ownerCtC2X, 0),
      select(allowancePresent, currentAllowance_ownerCtC2Y, 1))
    return ownerMemoEphemeral : JubjubPoint := jubjubFromCoordinates(
      select(allowancePresent, currentAllowance_ownerMemoEphemeralX, 0),
      select(allowancePresent, currentAllowance_ownerMemoEphemeralY, 1))
    return ownerMemoAmount : Native := select(
      allowancePresent, currentAllowance_ownerMemoAmount, 0)
  end

  -- A delegated spend updates both escrow copies and the owner's remaining
  -- allowance memo. Incoming value stays in the recipient's pending pool.
  entry transferFrom uses transferFromEscrow where
    read initialized as isInitialized
    require eq(isInitialized, true)
    require eq(eq(to, bytes32("")), false)
    member encryptionKeys[disclose(fromAddress)] as ownerRegistered
    require eq(ownerRegistered, true)
    member encryptionKeys[disclose(spenderId)] as spenderRegistered
    require eq(spenderRegistered, true)
    read encryptionKeys[disclose(spenderId)] as storedSpenderKey
    require eq(storedSpenderKey_x, result.spenderKeyX)
    require eq(storedSpenderKey_y, result.spenderKeyY)
    read encryptionKeys[disclose(fromAddress)] as storedOwnerKey
    require eq(storedOwnerKey_x, jubjubX(ownerPk))
    require eq(storedOwnerKey_y, jubjubY(ownerPk))
    member escrow[disclose(fromAddress)] as ownerEscrowPresent
    require eq(ownerEscrowPresent, true)
    member escrow[disclose(fromAddress)][disclose(spenderId)] as escrowPresent
    require eq(escrowPresent, true)
    read escrow[disclose(fromAddress)][disclose(spenderId)] as oldEscrow
    require eq(oldEscrow_spenderCtC1X, jubjubX(spenderC1))
    require eq(oldEscrow_spenderCtC1Y, jubjubY(spenderC1))
    require eq(oldEscrow_spenderCtC2X, jubjubX(spenderC2))
    require eq(oldEscrow_spenderCtC2Y, jubjubY(spenderC2))
    require eq(oldEscrow_ownerCtC1X, jubjubX(ownerC1))
    require eq(oldEscrow_ownerCtC1Y, jubjubY(ownerC1))
    require eq(oldEscrow_ownerCtC2X, jubjubX(ownerC2))
    require eq(oldEscrow_ownerCtC2Y, jubjubY(ownerC2))
    member escrowSpendEpochs[disclose(fromAddress)] as spendEpochOwnerPresent
    if eq(spendEpochOwnerPresent, false) then {
      insert escrowSpendEpochs[disclose(fromAddress)] := emptyMap
    } else {
    }
    member escrowSpendEpochs[disclose(fromAddress)][disclose(spenderId)] as spendEpochPresent
    if eq(spendEpochPresent, false) then {
      reset escrowSpendEpochs[disclose(fromAddress)][disclose(spenderId)]
    } else {
    }
    increment escrowSpendEpochs[disclose(fromAddress)][disclose(spenderId)] by 1
    read escrowSpendEpochs[disclose(fromAddress)][disclose(spenderId)] as actualSpendEpoch
    require eq(actualSpendEpoch, spendEpoch)
    write escrow[disclose(fromAddress)][disclose(spenderId)] := fields(
      result.nextSpenderC1X, result.nextSpenderC1Y,
      result.nextSpenderC2X, result.nextSpenderC2Y,
      result.nextOwnerC1X, result.nextOwnerC1Y,
      result.nextOwnerC2X, result.nextOwnerC2Y,
      result.ownerMemoEphemeralX, result.ownerMemoEphemeralY,
      result.ownerMemoAmount)
    member encryptionKeys[disclose(to)] as recipientRegistered
    require eq(recipientRegistered, true)
    read encryptionKeys[disclose(to)] as storedRecipientKey
    require eq(storedRecipientKey_x, jubjubX(recipientPk))
    require eq(storedRecipientKey_y, jubjubY(recipientPk))
    read pending[disclose(to)] as oldPending
    require eq(oldPending_c1x, jubjubX(pendingC1))
    require eq(oldPending_c1y, jubjubY(pendingC1))
    require eq(oldPending_c2x, jubjubX(pendingC2))
    require eq(oldPending_c2y, jubjubY(pendingC2))
    member memos[disclose(to)] as memoListPresent
    if eq(memoListPresent, false) then {
      reset memos[disclose(to)]
    } else {
    }
    member creditEpochs[disclose(to)] as creditEpochPresent
    if eq(creditEpochPresent, false) then {
      reset creditEpochs[disclose(to)]
    } else {
    }
    increment creditEpochs[disclose(to)] by 1
    read creditEpochs[disclose(to)] as actualCreditEpoch
    require eq(actualCreditEpoch, creditEpoch)
    write pending[disclose(to)] := fields(
      result.nextPendingC1X, result.nextPendingC1Y,
      result.nextPendingC2X, result.nextPendingC2Y)
    pushFront memos[disclose(to)] := fields(
      result.memoX, result.memoY, result.memoAmount)
    return caller : Bytes32 := spenderId
  end

  -- Public-supply wrapper for consuming the escrow as a burn. It returns the
  -- authenticated spender id and reduces supply by the same private value.
  entry burnFrom uses burnFromEscrow where
    read initialized as isInitialized
    require eq(isInitialized, true)
    member encryptionKeys[disclose(fromAddress)] as ownerRegistered
    require eq(ownerRegistered, true)
    member encryptionKeys[disclose(spenderId)] as spenderRegistered
    require eq(spenderRegistered, true)
    read encryptionKeys[disclose(spenderId)] as storedSpenderKey
    require eq(storedSpenderKey_x, result.spenderKeyX)
    require eq(storedSpenderKey_y, result.spenderKeyY)
    read encryptionKeys[disclose(fromAddress)] as storedOwnerKey
    require eq(storedOwnerKey_x, jubjubX(ownerPk))
    require eq(storedOwnerKey_y, jubjubY(ownerPk))
    member escrow[disclose(fromAddress)] as ownerEscrowPresent
    require eq(ownerEscrowPresent, true)
    member escrow[disclose(fromAddress)][disclose(spenderId)] as escrowPresent
    require eq(escrowPresent, true)
    read escrow[disclose(fromAddress)][disclose(spenderId)] as oldEscrow
    require eq(oldEscrow_spenderCtC1X, jubjubX(spenderC1))
    require eq(oldEscrow_spenderCtC1Y, jubjubY(spenderC1))
    require eq(oldEscrow_spenderCtC2X, jubjubX(spenderC2))
    require eq(oldEscrow_spenderCtC2Y, jubjubY(spenderC2))
    require eq(oldEscrow_ownerCtC1X, jubjubX(ownerC1))
    require eq(oldEscrow_ownerCtC1Y, jubjubY(ownerC1))
    require eq(oldEscrow_ownerCtC2X, jubjubX(ownerC2))
    require eq(oldEscrow_ownerCtC2Y, jubjubY(ownerC2))
    member escrowSpendEpochs[disclose(fromAddress)] as spendEpochOwnerPresent
    if eq(spendEpochOwnerPresent, false) then {
      insert escrowSpendEpochs[disclose(fromAddress)] := emptyMap
    } else {
    }
    member escrowSpendEpochs[disclose(fromAddress)][disclose(spenderId)] as spendEpochPresent
    if eq(spendEpochPresent, false) then {
      reset escrowSpendEpochs[disclose(fromAddress)][disclose(spenderId)]
    } else {
    }
    increment escrowSpendEpochs[disclose(fromAddress)][disclose(spenderId)] by 1
    read escrowSpendEpochs[disclose(fromAddress)][disclose(spenderId)] as actualSpendEpoch
    require eq(actualSpendEpoch, spendEpoch)
    write escrow[disclose(fromAddress)][disclose(spenderId)] := fields(
      result.nextSpenderC1X, result.nextSpenderC1Y,
      result.nextSpenderC2X, result.nextSpenderC2Y,
      result.nextOwnerC1X, result.nextOwnerC1Y,
      result.nextOwnerC2X, result.nextOwnerC2Y,
      result.ownerMemoEphemeralX, result.ownerMemoEphemeralY,
      result.ownerMemoAmount)
    read totalSupply as currentSupply
    write totalSupply := disclose(sub(currentSupply, value))
    return caller : Bytes32 := spenderId
  end
end

end OpenZeppelinPort

namespace OpenZeppelinPort

open Noctium

private def privateByteInputNames (name : String) : List String :=
  (List.range 32).map fun index => s!"%input_{name}_byte_{index}"

private def clearMemoPhysicalInputNames : List String :=
  ["%input__noctium_bytes32_accountId_high", "%input__noctium_bytes32_accountId_low31",
    "%input_expectedEpoch"] ++ privateByteInputNames "$helper2" ++
      privateByteInputNames "$helper4"

private def hasGuardedAccountIdEquality : Nat → Noctium.Expr .bool → _root_.Bool
  | 0, _ => Bool.false
  | fuel + 1, .letE _ _ body => hasGuardedAccountIdEquality fuel body
  | _ + 1,
      .eq
        (.select
          (.eq (.bytesField (.ref _) 0) (.bytesField (.ref _) 0))
          (.eq (.bytesField (.ref _) 1) (.bytesField (.ref _) 1))
        (.bool Bool.false))
        (.bool Bool.true) => Bool.true
  | _, _ => Bool.false

private def outputReference : Nat → Noctium.Expr .native → Option String
  | 0, _ => none
  | fuel + 1, .letE _ _ body => outputReference fuel body
  | _ + 1, .ref name => some name
  | _, _ => none

private def disclosesCoordinate : Nat → Nat → Sigma Noctium.Expr → _root_.Bool
  | 0, _, _ => Bool.false
  | fuel + 1, coordinate, ⟨_, .letE _ value body⟩ =>
      disclosesCoordinate fuel coordinate ⟨_, value⟩ ||
        disclosesCoordinate fuel coordinate ⟨_, body⟩
  | _ + 1, coordinate, ⟨.native, .disclose _ (.jubjubCoordinate _ index)⟩ =>
      index == coordinate
  | _, _, _ => Bool.false

private def outputInfo (item : Noctium.Output) :
    String × Option String × _root_.Bool × _root_.Bool :=
  match item with
  | ⟨name, .native, value, _⟩ =>
      (name, outputReference 32 value,
        disclosesCoordinate 32 0 ⟨.native, value⟩,
        disclosesCoordinate 32 1 ⟨.native, value⟩)
  | ⟨name, _, _, _⟩ => (name, none, Bool.false, Bool.false)

theorem clearMemoInput_exposes_checked_circuit :
    clearMemoInput.inputs.flatMap Noctium.Input.nativeIdentifiers = clearMemoPhysicalInputNames ∧
    clearMemoInput.constraints.map (hasGuardedAccountIdEquality 32) = [Bool.true] ∧
    clearMemoInput.outputs.map outputInfo =
      [("result.keyX", some "$helper9", Bool.true, Bool.true),
        ("result.keyY", some "$helper10", Bool.true, Bool.true)] := by
  decide

#guard registerAccount.name == "OpenZeppelinPort.registerAccount"

end OpenZeppelinPort
