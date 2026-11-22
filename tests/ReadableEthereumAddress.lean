import Noctium.Frontend

open scoped Noctium

noctium_witness keyForAddress() : Secp256k1Point

noctium_witness_circuit witnessEthereumAddress where
  output address : Bytes 20 := disclose(secp256k1EthereumAddress(witness keyForAddress()))
end

noctium_contract ReadableEthereumAddress where
  entry derive uses witnessEthereumAddress where
    return derivedAddress : Bytes 20 := address
  end
end

#guard_msgs (substring := true) in
/- error: undisclosed private -/
noctium_witness_circuit leaksEthereumAddress where
  output address : Bytes 20 := secp256k1EthereumAddress(witness keyForAddress())
end
