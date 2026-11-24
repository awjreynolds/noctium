import Noctium.Frontend
import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Disclosure

open scoped Noctium
open Noctium

private def foreignFieldWire : Helpers.Wire.Codec := {
  payload := .structure "ForeignFieldNegInv.FieldValue"
  frameBytes := 32
  composites := {structures := [{
    id := "ForeignFieldNegInv.FieldValue"
    fields := [{name := "value", type := .scalar (.foreign (.base .secp256k1))}]
  }]}
}

noctium_witness_circuit readableForeignFieldNegInv using foreignFieldWire where
  private input : Payload foreignFieldWire
  let value : Secp256k1Base := field(input, value)
  output negative : Secp256k1Base := disclose(foreignNeg(value))
  output inverse : Secp256k1Base := disclose(foreignInv(value))
end

noctium_circuit foreignFieldNegInv where
  private k1Base : Secp256k1Base
  private k1Scalar : Secp256k1Scalar
  private r1Base : Secp256r1Base
  private r1Scalar : Secp256r1Scalar
  private c255Base : Curve25519Base
  private c255Scalar : Curve25519Scalar
  private k1BaseZero : Secp256k1Base
  private k1ScalarZero : Secp256k1Scalar
  private r1BaseZero : Secp256r1Base
  private r1ScalarZero : Secp256r1Scalar
  private c255BaseZero : Curve25519Base
  private c255ScalarZero : Curve25519Scalar
  private k1BaseBoundary : Secp256k1Base
  private k1ScalarBoundary : Secp256k1Scalar
  private r1BaseBoundary : Secp256r1Base
  private r1ScalarBoundary : Secp256r1Scalar
  private c255BaseBoundary : Curve25519Base
  private c255ScalarBoundary : Curve25519Scalar
  private rejectK1BaseInvZero : Bool
  private rejectK1ScalarInvZero : Bool
  private rejectR1BaseInvZero : Bool
  private rejectR1ScalarInvZero : Bool
  private rejectC255BaseInvZero : Bool
  private rejectC255ScalarInvZero : Bool
  output k1BaseNegOutput : Secp256k1Base := disclose(foreignNeg(k1Base))
  output k1BaseInvOutput : Secp256k1Base := disclose(foreignInv(k1Base))
  output k1ScalarNegOutput : Secp256k1Scalar := disclose(foreignNeg(k1Scalar))
  output k1ScalarInvOutput : Secp256k1Scalar := disclose(foreignInv(k1Scalar))
  output r1BaseNegOutput : Secp256r1Base := disclose(foreignNeg(r1Base))
  output r1BaseInvOutput : Secp256r1Base := disclose(foreignInv(r1Base))
  output r1ScalarNegOutput : Secp256r1Scalar := disclose(foreignNeg(r1Scalar))
  output r1ScalarInvOutput : Secp256r1Scalar := disclose(foreignInv(r1Scalar))
  output c255BaseNegOutput : Curve25519Base := disclose(foreignNeg(c255Base))
  output c255BaseInvOutput : Curve25519Base := disclose(foreignInv(c255Base))
  output c255ScalarNegOutput : Curve25519Scalar := disclose(foreignNeg(c255Scalar))
  output c255ScalarInvOutput : Curve25519Scalar := disclose(foreignInv(c255Scalar))
  output k1BaseZeroNegOutput : Secp256k1Base := disclose(foreignNeg(k1BaseZero))
  output k1ScalarZeroNegOutput : Secp256k1Scalar := disclose(foreignNeg(k1ScalarZero))
  output r1BaseZeroNegOutput : Secp256r1Base := disclose(foreignNeg(r1BaseZero))
  output r1ScalarZeroNegOutput : Secp256r1Scalar := disclose(foreignNeg(r1ScalarZero))
  output c255BaseZeroNegOutput : Curve25519Base := disclose(foreignNeg(c255BaseZero))
  output c255ScalarZeroNegOutput : Curve25519Scalar := disclose(foreignNeg(c255ScalarZero))
  output k1BaseBoundaryNegOutput : Secp256k1Base := disclose(foreignNeg(k1BaseBoundary))
  output k1BaseBoundaryInvOutput : Secp256k1Base := disclose(foreignInv(k1BaseBoundary))
  output k1ScalarBoundaryNegOutput : Secp256k1Scalar := disclose(foreignNeg(k1ScalarBoundary))
  output k1ScalarBoundaryInvOutput : Secp256k1Scalar := disclose(foreignInv(k1ScalarBoundary))
  output r1BaseBoundaryNegOutput : Secp256r1Base := disclose(foreignNeg(r1BaseBoundary))
  output r1BaseBoundaryInvOutput : Secp256r1Base := disclose(foreignInv(r1BaseBoundary))
  output r1ScalarBoundaryNegOutput : Secp256r1Scalar := disclose(foreignNeg(r1ScalarBoundary))
  output r1ScalarBoundaryInvOutput : Secp256r1Scalar := disclose(foreignInv(r1ScalarBoundary))
  output c255BaseBoundaryNegOutput : Curve25519Base := disclose(foreignNeg(c255BaseBoundary))
  output c255BaseBoundaryInvOutput : Curve25519Base := disclose(foreignInv(c255BaseBoundary))
  output c255ScalarBoundaryNegOutput : Curve25519Scalar := disclose(foreignNeg(c255ScalarBoundary))
  output c255ScalarBoundaryInvOutput : Curve25519Scalar := disclose(foreignInv(c255ScalarBoundary))
end

noctium_contract ForeignFieldNegInv where
  cell k1BaseProbe : Secp256k1Base
  cell k1ScalarProbe : Secp256k1Scalar
  cell r1BaseProbe : Secp256r1Base
  cell r1ScalarProbe : Secp256r1Scalar
  cell c255BaseProbe : Curve25519Base
  cell c255ScalarProbe : Curve25519Scalar
  constructor() where
    initialize k1BaseProbe := secp256k1Base(0)
    initialize k1ScalarProbe := secp256k1Scalar(0)
    initialize r1BaseProbe := secp256r1Base(0)
    initialize r1ScalarProbe := secp256r1Scalar(0)
    initialize c255BaseProbe := curve25519Base(0)
    initialize c255ScalarProbe := curve25519Scalar(0)
  end
  entry checkFields uses foreignFieldNegInv where
    when disclose(rejectK1BaseInvZero) write k1BaseProbe := disclose(foreignInv(k1BaseZero))
    when disclose(rejectK1ScalarInvZero) write k1ScalarProbe := disclose(foreignInv(k1ScalarZero))
    when disclose(rejectR1BaseInvZero) write r1BaseProbe := disclose(foreignInv(r1BaseZero))
    when disclose(rejectR1ScalarInvZero) write r1ScalarProbe := disclose(foreignInv(r1ScalarZero))
    when disclose(rejectC255BaseInvZero) write c255BaseProbe := disclose(foreignInv(c255BaseZero))
    when disclose(rejectC255ScalarInvZero) write c255ScalarProbe := disclose(foreignInv(c255ScalarZero))
    return k1BaseNeg : Secp256k1Base := k1BaseNegOutput
    return k1BaseInv : Secp256k1Base := k1BaseInvOutput
    return k1ScalarNeg : Secp256k1Scalar := k1ScalarNegOutput
    return k1ScalarInv : Secp256k1Scalar := k1ScalarInvOutput
    return r1BaseNeg : Secp256r1Base := r1BaseNegOutput
    return r1BaseInv : Secp256r1Base := r1BaseInvOutput
    return r1ScalarNeg : Secp256r1Scalar := r1ScalarNegOutput
    return r1ScalarInv : Secp256r1Scalar := r1ScalarInvOutput
    return c255BaseNeg : Curve25519Base := c255BaseNegOutput
    return c255BaseInv : Curve25519Base := c255BaseInvOutput
    return c255ScalarNeg : Curve25519Scalar := c255ScalarNegOutput
    return c255ScalarInv : Curve25519Scalar := c255ScalarInvOutput
    return k1BaseZeroNeg : Secp256k1Base := k1BaseZeroNegOutput
    return k1ScalarZeroNeg : Secp256k1Scalar := k1ScalarZeroNegOutput
    return r1BaseZeroNeg : Secp256r1Base := r1BaseZeroNegOutput
    return r1ScalarZeroNeg : Secp256r1Scalar := r1ScalarZeroNegOutput
    return c255BaseZeroNeg : Curve25519Base := c255BaseZeroNegOutput
    return c255ScalarZeroNeg : Curve25519Scalar := c255ScalarZeroNegOutput
    return k1BaseBoundaryNeg : Secp256k1Base := k1BaseBoundaryNegOutput
    return k1BaseBoundaryInv : Secp256k1Base := k1BaseBoundaryInvOutput
    return k1ScalarBoundaryNeg : Secp256k1Scalar := k1ScalarBoundaryNegOutput
    return k1ScalarBoundaryInv : Secp256k1Scalar := k1ScalarBoundaryInvOutput
    return r1BaseBoundaryNeg : Secp256r1Base := r1BaseBoundaryNegOutput
    return r1BaseBoundaryInv : Secp256r1Base := r1BaseBoundaryInvOutput
    return r1ScalarBoundaryNeg : Secp256r1Scalar := r1ScalarBoundaryNegOutput
    return r1ScalarBoundaryInv : Secp256r1Scalar := r1ScalarBoundaryInvOutput
    return c255BaseBoundaryNeg : Curve25519Base := c255BaseBoundaryNegOutput
    return c255BaseBoundaryInv : Curve25519Base := c255BaseBoundaryInvOutput
    return c255ScalarBoundaryNeg : Curve25519Scalar := c255ScalarBoundaryNegOutput
    return c255ScalarBoundaryInv : Curve25519Scalar := c255ScalarBoundaryInvOutput
  end
  entry checkReadableFields uses readableForeignFieldNegInv arguments [input] where
    return neg : Secp256k1Base := negative
    return inv : Secp256k1Base := inverse
  end
end

#guard (Backend.Impact.lower ForeignFieldNegInv.state
  ((ForeignFieldNegInv.entrypoints.find? (·.name == "checkFields")).getD
    {name := "missing", circuit := {name := "missing"}})).isOk
