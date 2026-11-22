import Noctium.Frontend
import Noctium.Disclosure

open scoped Noctium
open Noctium

noctium_circuit foreignTransportInputs where
  public expectedKBase : Secp256k1Base
  public expectedKScalar : Secp256k1Scalar
  public expectedKPoint : Secp256k1Point
  public expectedRBase : Secp256r1Base
  public expectedRScalar : Secp256r1Scalar
  public expectedRPoint : Secp256r1Point
  private actualKBase : Secp256k1Base
  private actualKScalar : Secp256k1Scalar
  private actualKPoint : Secp256k1Point
  private actualRBase : Secp256r1Base
  private actualRScalar : Secp256r1Scalar
  private actualRPoint : Secp256r1Point
  private choose : Bool
  let chosenKBase : Secp256k1Base := select(choose, actualKBase, secp256k1Base(1))
  let chosenKScalar : Secp256k1Scalar := select(choose, actualKScalar, secp256k1Scalar(0))
  let chosenKPoint : Secp256k1Point := select(choose, actualKPoint, secp256k1Identity())
  let chosenRBase : Secp256r1Base := select(choose, actualRBase, secp256r1Base(1))
  let chosenRScalar : Secp256r1Scalar := select(choose, actualRScalar, secp256r1Scalar(0))
  let chosenRPoint : Secp256r1Point := select(choose, actualRPoint, secp256r1Identity())
  assert eq(chosenKBase, expectedKBase)
  assert eq(chosenKScalar, expectedKScalar)
  assert eq(chosenKPoint, expectedKPoint)
  assert eq(chosenRBase, expectedRBase)
  assert eq(chosenRScalar, expectedRScalar)
  assert eq(chosenRPoint, expectedRPoint)
  output kBaseValue : Secp256k1Base := disclose(chosenKBase)
  output kScalarValue : Secp256k1Scalar := disclose(chosenKScalar)
  output kPointValue : Secp256k1Point := disclose(chosenKPoint)
  output rBaseValue : Secp256r1Base := disclose(chosenRBase)
  output rScalarValue : Secp256r1Scalar := disclose(chosenRScalar)
  output rPointValue : Secp256r1Point := disclose(chosenRPoint)
end

noctium_contract ForeignTransport where
  entry inspect uses foreignTransportInputs where
    return kBase : Secp256k1Base := disclose(kBaseValue)
    return kScalar : Secp256k1Scalar := disclose(kScalarValue)
    return kPoint : Secp256k1Point := disclose(kPointValue)
    return rBase : Secp256r1Base := disclose(rBaseValue)
    return rScalar : Secp256r1Scalar := disclose(rScalarValue)
    return rPoint : Secp256r1Point := disclose(rPointValue)
  end
end

#guard Foreign.Kind.sourceName (.base .secp256k1) == "Secp256k1Base"
#guard Foreign.Kind.sourceName (.scalar .secp256k1) == "Secp256k1Scalar"
#guard Foreign.Kind.sourceName (.point .secp256k1) == "Secp256k1Point"
#guard Foreign.Kind.sourceName (.base .secp256r1) == "Secp256r1Base"
#guard Foreign.Kind.sourceName (.scalar .secp256r1) == "Secp256r1Scalar"
#guard Foreign.Kind.sourceName (.point .secp256r1) == "Secp256r1Point"
#guard Foreign.Kind.encodedFieldCount (.point .secp256k1) == 5
#guard Foreign.Kind.encodedFieldCount (.base .secp256r1) == 2
#guard Foreign.pointValid .secp256k1 .identity
#guard Foreign.pointValid .secp256r1 .identity
#guard Jubjub.pointValid 0 1
#guard Jubjub.pointValid
  28336281903124990867587793011069573392383982287722241916350956173377953689573
  39385640392217313770878525135509063452020585410343666726093009378539878503883
#guard !(Jubjub.pointValid 0 (Noctium.Field.modulus - 1))
#guard !(Jubjub.pointValid Noctium.Field.modulus 1)
#guard (Foreign.canonicalBytes (.point .secp256k1) .identity).toOption ==
  some (List.replicate 33 0)
#guard (Foreign.canonicalBytes (.point .curve25519) .identity).toOption ==
  some (1 :: List.replicate 31 0)
#guard (Foreign.canonicalBytes (.point .secp256k1) (.affine
    55066263022277343669578718895168534326250603453777594175500187360389116729240
    32670510020758816978083085130507043184471273380659243275938904335757337482424)).toOption ==
  some [0x02, 0x79, 0xbe, 0x66, 0x7e, 0xf9, 0xdc, 0xbb, 0xac, 0x55, 0xa0,
    0x62, 0x95, 0xce, 0x87, 0x0b, 0x07, 0x02, 0x9b, 0xfc, 0xdb, 0x2d,
    0xce, 0x28, 0xd9, 0x59, 0xf2, 0x81, 0x5b, 0x16, 0xf8, 0x17, 0x98]
#guard (Foreign.decodePoint .secp256k1 (Foreign.identityEncoding .secp256k1)).toOption == some .identity
#guard match Foreign.decodePoint .secp256k1 [0, 0, 0, 0, 2] with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false

#guard match (Expr.foreignBase .secp256k1 1).validate Capabilities.source [] with
  | .ok _ => _root_.Bool.true
  | .error _ => _root_.Bool.false
#guard match (Expr.foreignBase .secp256k1 (Foreign.Curve.baseModulus .secp256k1)).validate
    Capabilities.source [] with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false
#guard match (Expr.foreignIdentity .secp256r1).validate
    {Capabilities.source with foreignValues := _root_.Bool.false} [] with
  | .error "target lacks typed foreign-curve value support" => _root_.Bool.true
  | _ => _root_.Bool.false

private def foreignPrivateLeak : Circuit := {
  name := "foreignPrivateLeak"
  inputs := [{name := "secret", ty := .foreign (.base .secp256k1), visibility := .private}]
  outputs := [{name := "leak", ty := .foreign (.base .secp256k1), value := (.ref "secret" : Expr (.foreign (.base .secp256k1)))}]
}

#guard match Disclosure.circuit foreignPrivateLeak with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false

/-- error: curve values require explicit typed conversions -/
#guard_msgs in
noctium_circuit invalidForeignCast where
  private value : Secp256k1Base
  output nativeValue : Native := cast(Native, value)
end
