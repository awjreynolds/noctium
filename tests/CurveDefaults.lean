import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit curveDefaults where
  output jubjubScalarValue : JubjubScalar := default(JubjubScalar)
  output jubjubPointValue : JubjubPoint := default(JubjubPoint)
  output secp256k1BaseValue : Secp256k1Base := default(Secp256k1Base)
  output secp256k1ScalarValue : Secp256k1Scalar := default(Secp256k1Scalar)
  output secp256k1PointValue : Secp256k1Point := default(Secp256k1Point)
  output secp256r1BaseValue : Secp256r1Base := default(Secp256r1Base)
  output secp256r1ScalarValue : Secp256r1Scalar := default(Secp256r1Scalar)
  output secp256r1PointValue : Secp256r1Point := default(Secp256r1Point)
  output curve25519BaseValue : Curve25519Base := default(Curve25519Base)
  output curve25519ScalarValue : Curve25519Scalar := default(Curve25519Scalar)
  output curve25519PointValue : Curve25519Point := default(Curve25519Point)
end

noctium_contract CurveDefaults where
  entry inspect uses curveDefaults where
    return jubjubScalar : JubjubScalar := jubjubScalarValue
    return jubjubPoint : JubjubPoint := jubjubPointValue
    return k1Base : Secp256k1Base := secp256k1BaseValue
    return k1Scalar : Secp256k1Scalar := secp256k1ScalarValue
    return k1Point : Secp256k1Point := secp256k1PointValue
    return r1Base : Secp256r1Base := secp256r1BaseValue
    return r1Scalar : Secp256r1Scalar := secp256r1ScalarValue
    return r1Point : Secp256r1Point := secp256r1PointValue
    return c25519Base : Curve25519Base := curve25519BaseValue
    return c25519Scalar : Curve25519Scalar := curve25519ScalarValue
    return c25519Point : Curve25519Point := curve25519PointValue
  end
end
