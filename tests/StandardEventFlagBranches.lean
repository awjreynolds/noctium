import Noctium.Frontend

open scoped Noctium

noctium_circuit eventFlagInputs where
  public present : Bool
  public route : Bool
  private receiveCommitment : Bytes 32
  private receiveCiphertext : Bytes 512
  private receiveContract : Bytes 32
  private mintCommitment : Bytes 32
  private mintDomain : Bytes 32
  private mintAmount : UInt 128
  private burnNullifier : Bytes 32
  private burnAmount : UInt 128
  private spendUserKey : Bytes 32
  private spendContract : Bytes 32
  private spendDomain : Bytes 32
  private spendToken : Bytes 32
  private spendAmount : UInt 128
  private receiveUserKey : Bytes 32
  private receiveAddress : Bytes 32
  private receiveDomain : Bytes 32
  private receiveToken : Bytes 32
  private receiveAmount : UInt 128
  private unshieldedBurnUserKey : Bytes 32
  private unshieldedBurnContract : Bytes 32
  private unshieldedBurnToken : Bytes 32
  private unshieldedBurnAmount : UInt 128
end

noctium_contract EventFlagBranches where
  entry emitFlagBranches uses eventFlagInputs where
    emitEvent(ShieldedReceive,
      commitment := disclose(receiveCommitment),
      hasCiphertext := present, ciphertext := disclose(receiveCiphertext),
      hasContractAddress := route, contractAddress := disclose(receiveContract))
    emitEvent(ShieldedMint,
      commitment := disclose(mintCommitment), domainSep := disclose(mintDomain),
      hasAmount := present, amount := disclose(mintAmount))
    emitEvent(ShieldedBurn,
      nullifier := disclose(burnNullifier), hasAmount := route, amount := disclose(burnAmount))
    emitEvent(UnshieldedSpend,
      isUser := present, userKey := disclose(spendUserKey),
      contractAddress := disclose(spendContract), domainSep := disclose(spendDomain),
      tokenType := disclose(spendToken), amount := disclose(spendAmount))
    emitEvent(UnshieldedReceive,
      isUser := route, userKey := disclose(receiveUserKey),
      contractAddress := disclose(receiveAddress), domainSep := disclose(receiveDomain),
      tokenType := disclose(receiveToken), amount := disclose(receiveAmount))
    emitEvent(UnshieldedBurn,
      isUser := route, userKey := disclose(unshieldedBurnUserKey),
      contractAddress := disclose(unshieldedBurnContract),
      tokenType := disclose(unshieldedBurnToken), amount := disclose(unshieldedBurnAmount))
  end
end
