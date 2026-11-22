import Noctium.Frontend

open scoped Noctium

noctium_circuit unshieldedMintRecipientInputs where
  public domain : Bytes32
  public amount : UInt 64
  public isContract : Bool
  public recipient : Bytes32
  public enabled : Bool
end

noctium_contract NativeUnshieldedMintRecipient where
  entry mint uses unshieldedMintRecipientInputs where
    when enabled mintUnshieldedTo(domain, amount, isContract, recipient) as mintedColor
    return color : Bytes32 := disclose(mintedColor)
  end
end

noctium_circuit privateMintAmount where
  public domain : Bytes32
  private amount : UInt 64
  public recipient : Bytes32
end

/-- undisclosed private parameter 'amount' -/
#guard_msgs (substring := true) in
noctium_contract UndisclosedUnshieldedMint where
  entry mint uses privateMintAmount where
    mintUnshieldedTo(domain, amount, false, recipient) as mintedColor
  end
end
