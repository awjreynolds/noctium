import Noctium.Frontend

open scoped Noctium

noctium_witness_circuit reverseForeignCoordinate where
  private key : Secp256k1Point
  output reversed : Bytes32 := disclose(reverseBytes32(foreignToBytes(curveX(key))))
end

noctium_contract ReverseForeignCoordinate where
  entry inspect uses reverseForeignCoordinate where
    return reversedResult : Bytes32 := reversed
  end
end
