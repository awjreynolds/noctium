import Noctium.Frontend
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium

noctium_circuit foreignListMaybeInputs where
  private secp256k1Base : Secp256k1Base
  private secp256k1Scalar : Secp256k1Scalar
  private secp256k1Point : Secp256k1Point
  private secp256r1Base : Secp256r1Base
  private secp256r1Scalar : Secp256r1Scalar
  private secp256r1Point : Secp256r1Point
  private curve25519Base : Curve25519Base
  private curve25519Scalar : Curve25519Scalar
  private curve25519Point : Curve25519Point
end

noctium_circuit foreignListMaybeNoInputs where
end

noctium_contract ForeignListMaybe where
  list secp256k1BaseValues : Secp256k1Base
  list secp256k1ScalarValues : Secp256k1Scalar
  list secp256k1PointValues : Secp256k1Point
  list secp256r1BaseValues : Secp256r1Base
  list secp256r1ScalarValues : Secp256r1Scalar
  list secp256r1PointValues : Secp256r1Point
  list curve25519BaseValues : Curve25519Base
  list curve25519ScalarValues : Curve25519Scalar
  list curve25519PointValues : Curve25519Point

  entry push uses foreignListMaybeInputs
      arguments [secp256k1Base, secp256k1Scalar, secp256k1Point,
        secp256r1Base, secp256r1Scalar, secp256r1Point,
        curve25519Base, curve25519Scalar, curve25519Point] where
    pushFront secp256k1BaseValues := disclose(secp256k1Base)
    pushFront secp256k1ScalarValues := disclose(secp256k1Scalar)
    pushFront secp256k1PointValues := disclose(secp256k1Point)
    pushFront secp256r1BaseValues := disclose(secp256r1Base)
    pushFront secp256r1ScalarValues := disclose(secp256r1Scalar)
    pushFront secp256r1PointValues := disclose(secp256r1Point)
    pushFront curve25519BaseValues := disclose(curve25519Base)
    pushFront curve25519ScalarValues := disclose(curve25519Scalar)
    pushFront curve25519PointValues := disclose(curve25519Point)
  end

  entry head uses foreignListMaybeNoInputs where
    headOrDefault secp256k1BaseValues as (secp256k1BasePresent, secp256k1BasePayload)
    headOrDefault secp256k1ScalarValues as (secp256k1ScalarPresent, secp256k1ScalarPayload)
    headOrDefault secp256k1PointValues as (secp256k1PointPresent, secp256k1PointPayload)
    headOrDefault secp256r1BaseValues as (secp256r1BasePresent, secp256r1BasePayload)
    headOrDefault secp256r1ScalarValues as (secp256r1ScalarPresent, secp256r1ScalarPayload)
    headOrDefault secp256r1PointValues as (secp256r1PointPresent, secp256r1PointPayload)
    headOrDefault curve25519BaseValues as (curve25519BasePresent, curve25519BasePayload)
    headOrDefault curve25519ScalarValues as (curve25519ScalarPresent, curve25519ScalarPayload)
    headOrDefault curve25519PointValues as (curve25519PointPresent, curve25519PointPayload)
    returnMaybe maybeSecp256k1Base as (secp256k1BasePresent, secp256k1BasePayload)
    returnMaybe maybeSecp256k1Scalar as (secp256k1ScalarPresent, secp256k1ScalarPayload)
    returnMaybe maybeSecp256k1Point as (secp256k1PointPresent, secp256k1PointPayload)
    returnMaybe maybeSecp256r1Base as (secp256r1BasePresent, secp256r1BasePayload)
    returnMaybe maybeSecp256r1Scalar as (secp256r1ScalarPresent, secp256r1ScalarPayload)
    returnMaybe maybeSecp256r1Point as (secp256r1PointPresent, secp256r1PointPayload)
    returnMaybe maybeCurve25519Base as (curve25519BasePresent, curve25519BasePayload)
    returnMaybe maybeCurve25519Scalar as (curve25519ScalarPresent, curve25519ScalarPayload)
    returnMaybe maybeCurve25519Point as (curve25519PointPresent, curve25519PointPayload)
  end

  entry pop uses foreignListMaybeNoInputs where
    popFront secp256k1BaseValues
    popFront secp256k1ScalarValues
    popFront secp256k1PointValues
    popFront secp256r1BaseValues
    popFront secp256r1ScalarValues
    popFront secp256r1PointValues
    popFront curve25519BaseValues
    popFront curve25519ScalarValues
    popFront curve25519PointValues
  end
end

#guard ForeignListMaybe.entrypoints.all fun candidate =>
  (Backend.Zkir.lowerEntrypoint ForeignListMaybe.state candidate).isOk
