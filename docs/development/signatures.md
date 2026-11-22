# Typed signature verification

Noctium exposes five Lean DSL helpers, implemented as typed `Expr` combinators in [Signatures.lean](../../Noctium/Crypto/Signatures.lean). They expand into the existing field, point, byte and hash operations. Compilation and Rust execution require neither Compact nor Node.

```lean
import Noctium.Frontend
open scoped Noctium

noctium_circuit verifyAuthorization where
  public digest : Bytes 32
  public key : Secp256k1Point
  private r : Secp256k1Scalar
  private s : Secp256k1Scalar
  output valid : Bool := disclose(secp256k1EcdsaVerify(digest, r, s, key))
end
```

Publishing a verification result derived from private data requires explicit disclosure. A successful verification result does not disclose the entire signature, but does release the declared predicate. Message binding, authorization, replay protection and the application's release policy remain contract obligations. Verification returns a Bool. Use a circuit assertion when acceptance must require a valid signature.

| Helper | Arguments | Result |
| --- | --- | --- |
| `secp256k1EcdsaVerify` | Bytes32 digest, Secp256k1Scalar r and s, Secp256k1Point key | Bool |
| `secp256r1EcdsaVerify` | Bytes32 digest, Secp256r1Scalar r and s, Secp256r1Point key | Bool |
| `jubjubSchnorrVerify` | Native message vector, JubjubPoint announcement, Native response, JubjubPoint key | Bool |
| `ed25519Verify` | Bytes message, Curve25519Point R, Curve25519Scalar S, Curve25519Point key | Bool |
| `secp256k1EthereumAddress` | Secp256k1Point key | Bytes20 |

## Portable signature records

Each signature type exposes a `codec`. Use the codec in the readable circuit's
`using` clause and declare the argument as `Payload codecName`. The checked
record keeps its nominal identity and curve-specific fields through the host
witness plan and native return views. Its Noctium wire frame holds two 32-byte
fields. The field names and order match the pinned Compact signature types.

The focused case echoes all four records through the Rust witness session and
ZKIR 3.2.1 native checker. It rejects a different signature identity, a scalar
from a different curve, and a changed native return commitment. Returning a
private input in the fixture requires explicit disclosure.
[Lean fixture](../../tests/SignaturePayloads.lean) · [Compact reference](../../tests/compact/SignaturePayloads.compact) · [Native check](../../runtime/tests/signature_helpers.rs)

## Protocol and failure rules

ECDSA interprets the supplied 32-byte digest as a big-endian integer and reduces it into the curve's scalar field. The equation checks the x-coordinate of `[digest/s]G + [r/s]key`, reduced modulo the scalar order, against r. Both high-s and low-s signatures are accepted. A low-s rule needs an additional application policy. The helper does not hash a message or establish a relationship between the digest and another contract value.

Identity public keys and zero r or s abort. Coordinate extraction also aborts when the computed point is the identity. Other equation mismatches return false. The explicit zero-r rejection is a deliberate stricter boundary than the pinned Compact helper, which lacks this explicit guard. Do not treat this as exact invalid-input equivalence.

Jubjub Schnorr hashes exactly `[R.x, R.y, key.x, key.y] ++ messageFields`. It reduces both the resulting Native challenge and Native response modulo the Jubjub scalar order, then checks `[response]G = R + [challenge]key`. The total preimage is limited to 1024 Native fields, leaving 1020 message fields. Identity public keys abort. Identity announcements are permitted. A mismatched equation returns false. A pairwise hash chain or byte-message encoding defines a different protocol.

Ed25519 checks `[S]G = R + [SHA512(encode(R) || encode(key) || message)]key`, reducing the SHA-512 output into the scalar field. The point encodings are canonical compressed Edwards encodings. Message length is zero through 960 bytes, because the existing hash input limit includes the 64-byte R/key prefix. No implicit prehash changes the signed message. Typed points require prime-subgroup validity and typed S requires canonical scalar encoding. Identity public keys abort. An ordinary equation mismatch returns false. Import a signature's S through canonical typed input decoding. Reducing arbitrary signature bytes modulo the order loses the original encoding check.

Ethereum address derivation applies Keccak-256 to the two 32-byte big-endian affine coordinates `x || y`, without a SEC1 prefix, then returns the final 20 bytes. Identity keys abort.

The [pinned standard library](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/compiler/standard-library.compact#L354) and [ZKIR v3 helpers](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/compiler/zkir-v3-library.compact) serve as semantic references. The MIT implementation does not copy their Apache-2.0 source. Ed25519's published vector and encoding rules come from [RFC 8032](https://www.rfc-editor.org/rfc/rfc8032.html#section-7.1).

## Focused evidence

[Source fixture](../../tests/SignatureChecks.lean), [native runtime case](../../runtime/tests/signature_helpers.rs), [retained artifacts](../../runtime/tests/fixtures/signature-helpers/321), [issue 82](https://github.com/awjreynolds/noctium/issues/82).

The Source fixture exercises every helper, explicit disclosure, wrong-curve rejection and the Ed25519 message cap. The native case uses RustCrypto's secp256k1 prehash fixture, its P-256 FIPS 186-4 CAVP fixture, RFC 8032's empty-message Ed25519 vector and the Ethereum address for private key 1. The Jubjub case independently constructs a signature with native group arithmetic and the pinned native transient hash. Altered digest/message values, precondition failures and tampered native witness values receive focused checks through the same Rust `prepare` and native `check` route.

These checks establish scoped Source/native behavior. They do not establish cryptographic security, complete Compact equivalence or compiler preservation. No new keys, proofs, deployments, K benchmark or web/mobile qualification accompanies this slice. Broader assurance remains tracked in issues [21](https://github.com/awjreynolds/noctium/issues/21) and [23](https://github.com/awjreynolds/noctium/issues/23).

The compiler/Claim build, Source guards and guide snippet pass. The focused native case passes in 0.05 seconds, including a valid identity-announcement Schnorr signature and an ECDSA computed-identity rejection. Re-exported Source artifacts match the retained bytes. The fixture contains 420 native instructions, 105 private transcript fields and six output bindings. These are structural counts, not K or proving-time measurements.

Reproduce the focused runtime case with `cargo test --manifest-path runtime/Cargo.toml --no-default-features --features zkir-321 --test signature_helpers` using the pinned Rust toolchain described in the runtime setup.
