import Noctium.Frontend

open scoped Noctium
open Noctium

private abbrev schnorrWire := Crypto.JubjubSchnorrSignature.codec
private abbrev ed25519Wire := Crypto.Ed25519Signature.codec

noctium_witness schnorrSignature() : Payload schnorrWire
noctium_witness ed25519Signature() : Payload ed25519Wire

noctium_witness_circuit readableSchnorr using schnorrWire where
  public message0 : Native
  public changedMessage0 : Native
  public message1 : Native
  public key : JubjubPoint
  let {announcement := signedAnnouncement, response := signedResponse} :=
    witness schnorrSignature()
  output valid : Bool :=
    disclose(jubjubSchnorrVerify([message0, message1], signedAnnouncement, signedResponse, key))
  output changedValid : Bool :=
    disclose(jubjubSchnorrVerify([changedMessage0, message1], signedAnnouncement, signedResponse, key))
end

noctium_witness_circuit readableEd25519 using ed25519Wire where
  public message : Bytes 0
  public changedMessage : Bytes 1
  public key : Curve25519Point
  let {r := signatureR, s := signatureS} := witness ed25519Signature()
  output valid : Bool :=
    disclose(ed25519Verify(message, signatureR, signatureS, key))
  output changedValid : Bool :=
    disclose(ed25519Verify(changedMessage, signatureR, signatureS, key))
end

noctium_contract ReadableSignatures where
  entry schnorr uses readableSchnorr where
    return signatureValid : Bool := valid
    return changedSignatureValid : Bool := changedValid
  end
  entry ed25519 uses readableEd25519 where
    return signatureValid : Bool := valid
    return changedSignatureValid : Bool := changedValid
  end
end

#guard_msgs (substring := true) in
/- error: undisclosed private -/
noctium_witness_circuit rejectsUndisclosedSignatureResult using ed25519Wire where
  public message : Bytes 0
  public key : Curve25519Point
  let {r := signatureR, s := signatureS} := witness ed25519Signature()
  output valid : Bool := ed25519Verify(message, signatureR, signatureS, key)
end
