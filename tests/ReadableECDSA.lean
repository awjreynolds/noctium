import Noctium.Frontend

open scoped Noctium
open Noctium

private abbrev k1Wire := Crypto.Secp256k1EcdsaSignature.codec
private abbrev r1Wire := Crypto.Secp256r1EcdsaSignature.codec

noctium_witness keySignatureK1() : Payload k1Wire
noctium_witness keySignatureR1() : Payload r1Wire

noctium_witness_circuit readableK1 using k1Wire where
  public digest : Bytes32
  public key : Secp256k1Point
  let signature := witness keySignatureK1()
  output valid : Bool :=
    disclose(secp256k1EcdsaVerify(digest, field(signature, r), field(signature, s), key))
end

noctium_witness_circuit readableR1 using r1Wire where
  public digest : Bytes32
  public key : Secp256r1Point
  let signature := witness keySignatureR1()
  output valid : Bool :=
    disclose(secp256r1EcdsaVerify(digest, field(signature, r), field(signature, s), key))
end

noctium_contract ReadableECDSA where
  entry k1 uses readableK1 where
    return signatureValid : Bool := valid
  end
  entry r1 uses readableR1 where
    return signatureValid : Bool := valid
  end
end

#guard_msgs (substring := true) in
/- error: undisclosed private -/
noctium_witness_circuit leaksK1SignatureCheck using k1Wire where
  public digest : Bytes32
  public key : Secp256k1Point
  let signature := witness keySignatureK1()
  output valid : Bool :=
    secp256k1EcdsaVerify(digest, field(signature, r), field(signature, s), key)
end
