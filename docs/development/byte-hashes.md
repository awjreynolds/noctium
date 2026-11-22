# SHA-512 and Keccak-256

`sha512(value)` accepts `Bytes n` and returns `Bytes 64`.
`keccak256(value)` returns `Bytes32` and uses Keccak padding, distinct from
SHA3-256. Both accept source lengths from 0 through the existing 1024-byte limit.
Use explicit serialization or concatenation to construct a preimage.

```lean
import Noctium.Frontend
open scoped Noctium

noctium_circuit hashPayload where
  private payload : Bytes 64
  output digest : Bytes 64 := disclose(sha512(payload))
end
```

Hashing preserves private origins. Releasing a hash or a selected digest byte
requires the same explicit disclosure as other derived private values. The Lean
semantic context supplies separate hash oracles with fail-closed defaults and
checks every returned digest's length and octet bounds.

The compiler emits the native `sha512` and `keccak256` instructions directly.
Preimages use one exact FAB byte alignment and canonical Native chunks, with
the partial final chunk first in FAB order. Empty source preimages use an empty
alignment and no operands. Native hashing accepts this route without constructing
an unsupported native `Bytes 0` value or substituting a constant digest.
Operand evaluation, assertions and range requirements remain active for empty
preimages.

[The source fixture](../../tests/ByteHashes.lean) and
[native cases](../../runtime/tests/byte_hashes.rs) cover empty and `abc` preimages,
31/32/33-byte boundaries, typed 32/64-byte returns and reuse of SHA-512 output in
slicing and concatenation. Changed input/output bindings, a false private guard,
SHA3 substitution, and malformed producer alignment/count/ranges reject.
Empty hashes pass the official checker and native circuit sizing. A focused
Rust host Session case exercises the same operations through the interpreter.

These are source, checker, sizing and host execution results on the selected
3.2.1 profile. No new keys, proofs or deployment were created for this feature.
`keccak256(point)` also accepts a typed `Secp256k1Point` on the 3.2.1 profile.
Its 96-byte FAB preimage includes both coordinates and the field-encoded identity
flag. The compiler binds the five aligned operands to one validated point.
Compact and the native checker agree on the generator digest. The native case
rejects a compressed point with an out-of-field coordinate and a changed digest
return. [Lean fixture](../../tests/TypedPointKeccak.lean)
[Compact reference](../../tests/compact/typed-point-keccak.mjs)
[Native check](../../runtime/tests/typed_point_keccak.rs)

Ordinary circuits also accept `keccak256Fab(environment, type, [values])` for
checked named records and tuples. The backend derives the atom order and byte
widths from the layout. The native producer checks those widths and binds the
same typed operands. `Sha512Fab.hash` computes both digests over a record with
Bytes32, Bool, UInt16 and Native fields. Both Keccak digests match Compact
0.36.1. The native check rejects UInt16 overflow and a changed return
commitment. The existing point case emits the same ZKIR and Impact bytes.
[Mixed FAB source](../../tests/Sha512Fab.lean) · [Compact oracle](../../tests/compact/sha512-fab.mjs) · [Native check](../../runtime/tests/sha512_fab.rs)

Readable witness circuits accept `sha512(record)` and `keccak256(record)` over
checked FAB layouts. A witness provider returns the named record once, and
the compiler derives the field order and byte widths from its declaration.
`Sha512Fab.hashHosted` checks both digests against the pinned Compact vector in
the Rust witness session and the native ZKIR checker. The session rejects a
reply with a different record identity. Returning a digest derived from a
private witness requires `disclose`.
[Hosted case](../../runtime/tests/witness_control.rs)
