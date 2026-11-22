import examples.openzeppelin.ConfidentialToken
import Noctium.Frontend

open scoped Noctium

namespace OpenZeppelinPort

noctium_circuit claimMintInputs where
  private opening : Native
  private recipient : Bytes32
  private value : UInt 128
end

noctium_contract TokenMinter where
  cell route : Bytes32
  counter issuanceCount

  entry claimMint uses claimMintInputs where
    read route as target
    claimContractCall(target,
      disclose(callCommitment(ConfidentialToken, "mint", opening,
        [recipient, value], [])))
    increment issuanceCount by 1
  end
end

end OpenZeppelinPort
