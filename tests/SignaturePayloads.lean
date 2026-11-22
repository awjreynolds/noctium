import Noctium.Frontend

open scoped Noctium
open Noctium

private abbrev schnorrWire := Crypto.JubjubSchnorrSignature.codec
private abbrev k1Wire := Crypto.Secp256k1EcdsaSignature.codec
private abbrev r1Wire := Crypto.Secp256r1EcdsaSignature.codec
private abbrev edWire := Crypto.Ed25519Signature.codec

noctium_witness_circuit signaturePayloads using schnorrWire, k1Wire, r1Wire, edWire where
  private schnorr : Payload schnorrWire
  private k1 : Payload k1Wire
  private r1 : Payload r1Wire
  private ed : Payload edWire
  output schnorrResult := disclose(schnorr)
  output k1Result := disclose(k1)
  output r1Result := disclose(r1)
  output edResult := disclose(ed)
end

noctium_contract SignaturePayloads where
  entry echo uses signaturePayloads where
    return schnorrResult
    return k1Result
    return r1Result
    return edResult
  end
end
