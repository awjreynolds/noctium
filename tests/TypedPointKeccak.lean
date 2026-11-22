import Noctium.Frontend
import Noctium.Disclosure

open scoped Noctium
open Noctium

noctium_circuit pointHash where
  private point : Secp256k1Point
  output digest : Bytes32 := disclose(keccak256(point))
end

noctium_witness pointForHash() : Secp256k1Point

noctium_witness_circuit witnessedPointHash where
  public expected : Bytes32
  let point : Secp256k1Point := witness pointForHash()
  let digest : Bytes32 := keccak256(point)
  prove eq(digest, expected)
  output hostedDigest : Bytes32 := disclose(digest)
end

noctium_contract TypedPointKeccak where
  entry hash uses pointHash where
    return pointHashResult : Bytes32 := digest
  end
  entry hashHosted uses witnessedPointHash where
    return pointDigest : Bytes32 := hostedDigest
  end
end
