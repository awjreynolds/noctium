import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit jubjubGroupParity where
  private point : JubjubPoint
  private other : JubjubPoint
  private scalar : JubjubScalar
  output added : JubjubPoint := disclose(jubjubAdd(point, other))
  output negated : JubjubPoint := disclose(jubjubNeg(point))
  output multiplied : JubjubPoint := disclose(jubjubMul(point, scalar))
  output generated : JubjubPoint := disclose(jubjubMulGenerator(scalar))
end

noctium_circuit secp256k1GroupParity where
  private point : Secp256k1Point
  private other : Secp256k1Point
  private scalar : Secp256k1Scalar
  output added : Secp256k1Point := disclose(foreignAdd(point, other))
  output multiplied : Secp256k1Point := disclose(curveMul(point, scalar))
  output generated : Secp256k1Point := disclose(curveMulGenerator(scalar))
end

noctium_circuit secp256r1GroupParity where
  private point : Secp256r1Point
  private other : Secp256r1Point
  private scalar : Secp256r1Scalar
  output added : Secp256r1Point := disclose(foreignAdd(point, other))
  output multiplied : Secp256r1Point := disclose(curveMul(point, scalar))
  output generated : Secp256r1Point := disclose(curveMulGenerator(scalar))
end

noctium_circuit curve25519GroupParity where
  private point : Curve25519Point
  private other : Curve25519Point
  private scalar : Curve25519Scalar
  output added : Curve25519Point := disclose(foreignAdd(point, other))
  output multiplied : Curve25519Point := disclose(curveMul(point, scalar))
  output generated : Curve25519Point := disclose(curveMulGenerator(scalar))
end

noctium_contract CurveGroupParity where
  entry jubjubGroup uses jubjubGroupParity where
    return resultAdded : JubjubPoint := added
    return resultNegated : JubjubPoint := negated
    return resultMultiplied : JubjubPoint := multiplied
    return resultGenerated : JubjubPoint := generated
  end
  entry secp256k1Group uses secp256k1GroupParity where
    return resultAdded : Secp256k1Point := added
    return resultMultiplied : Secp256k1Point := multiplied
    return resultGenerated : Secp256k1Point := generated
  end
  entry secp256r1Group uses secp256r1GroupParity where
    return resultAdded : Secp256r1Point := added
    return resultMultiplied : Secp256r1Point := multiplied
    return resultGenerated : Secp256r1Point := generated
  end
  entry curve25519Group uses curve25519GroupParity where
    return resultAdded : Curve25519Point := added
    return resultMultiplied : Curve25519Point := multiplied
    return resultGenerated : Curve25519Point := generated
  end
end
