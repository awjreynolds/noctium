# Fixed byte values

Use `Bytes n` for a byte string with a compile-time length from 0 through 1024.
The limit reuses the compiler's existing fixed-vector resource bound. `Bytes32`
remains an alias for the 32-byte source type, with its existing wire encoding.

```lean
import Noctium.Frontend
open scoped Noctium

noctium_circuit combine where
  private left : Bytes 31
  private right : Bytes 33
  let joined : Bytes 64 := concatBytes(left, right)
  output first : UInt 8 := disclose(byteAt(joined, 0))
end
```

`reverseBytes(value)` preserves the length. `sliceBytes(value, start, stop)` uses
constant bounds, includes `start` and excludes `stop`. Bounds must satisfy
`start <= stop <= length`. `concatBytes(left, right)` returns the sum of the two
lengths, subject to the same resource limit. `eq(left, right)` compares
equal-length byte values through their checked chunks. `bytes(n, "text")` encodes UTF-8
and pads on the right with zero bytes. Selection requires matching lengths.
Private inputs keep their private origins through each operation. Publishing
a derived value requires an explicit `disclose` at the public output or return.

Use `toBytes(value, width)` to encode a Native or UInt value in 1 through
1024 little-endian bytes. The conversion rejects a value too large for the
selected width and pads the high bytes with zeros. For example,
`toBytes(255, 1)` returns one byte with value 255. `toBytes(256, 1)` fails
the fit check. `serialize` keeps its type-directed frame width rules.

Readable witness circuits also construct Bytes from checked octets.

```lean
let packed := packBytes(7, ..vector, ..suffix, 23)
output reversed : Bytes 6 := disclose(reverseBytes(packed))
```

Each direct item must fit UInt8 by its declared type. A numeric literal in this
position uses its unsigned range. Tuple and vector spreads contribute one
octet per element. A fixed Bytes spread keeps its byte order and reuses its
whole segment. Empty spreads still evaluate their source once. The pinned
Compact fixture checks payload order and the three witness calls.
[Lean fixture](../../tests/ReadableRecordConstruction.lean) · [Compact comparison](../../tests/compact/readable-record-construction.mjs)

The host token is `Bytes<n>` and its value is
`{"kind":"bytes","values":[0,1,2]}`. The array must contain exactly the declared
number of integer octets. The SDK rejects malformed lengths and non-byte values.
Rust retains `ScalarType::Bytes32` for 32 bytes and uses `ScalarType::Bytes(n)`
for other supported lengths. Existing source witness and private-state transport
carry the same logical value before expansion to checked Native byte leaves.

Native byte instructions use 31-byte field chunks in low-to-high order. Ledger
output commitments reverse the chunk order through the pinned FAB alignment.
Typed entrypoint results preserve the logical byte value in the host and commit
the corresponding fields in the circuit. A final partial chunk receives its
exact range bound.

The ZKIR lowerer slices existing byte leaves by position. Packed values still
use the native slice instruction. Widening a checked byte to a 32-byte value
keeps its eight-bit range check and supplies 31 zero high bytes.

The pinned native ZKIR type excludes zero-length bytes. Source `Bytes 0` has one
possible value and no native fields. Empty operations preserve operand evaluation,
assertions and failures while omitting an unsupported native zero-byte value.
Zero-byte equality and unused partial byte bindings also preserve evaluation.

[The source fixture](../../tests/NativeBytes.lean) and
[focused native case](../../runtime/tests/native_bytes.rs) cover chunk boundaries,
selection, typed returns, invalid lengths and output binding. A zero-field return
still rejects a false private assertion.

These are source and native-checker results on the selected 3.2.1 profile. No new
keys, proofs or deployment were created for this feature. [Byte ledger cells,
map values and nested leaves](byte-storage.md) have separate scoped checks.
Non-Bytes32 byte keys remain gated. Other native byte operations and full
overload, proof and SDK qualification remain part of the wider capability goal.

## Public byte arguments

An ordinary nonempty public `Bytes n` input uses one Impact push and one readback of the fixed-width value. The native statement binds the readback in FAB order, starting with the highest chunk. Each chunk holds up to 31 bytes and has an exact range constraint. Public `Bytes 0` has no physical fields or readback. The source type and the SDK's byte-array value remain the same.

A 256-byte input now has nine public transcript fields and two VM operations. The previous bytewise prologue used 256 fields and 512 operations. The standard event catalog uses an ordinary public memo and matches the same reference payloads after packing. [Catalog benchmark and localnet receipt](standard-events.md#focused-qualification)

## Native byte packing

Computed byte values now lower through native `bytes_into_natives`. The operation returns exactly `ceil(n / 31)` Native chunks, ordered from the first input bytes to the last. Each chunk uses little-endian byte order. The final partial chunk keeps its exact range. Source representations, disclosure rules and FAB output ordering stay the same. Other typed values continue using native `encode`.

The source and producer support lengths 1 through 1024. Source `Bytes 0` erases to zero fields without creating a native zero-length byte value. The producer shares checked byte-chunk semantics with `encode` and rejects wrong types, output counts and unsupported lengths.

The [source example](../../tests/NativeBytePacking.lean) returns reversed private byte strings at lengths 1, 31, 32, 62 and 63, plus an empty value. The [focused Rust case](../../runtime/tests/native_byte_packing.rs) checks the actual opcode and output counts, compares every returned byte and rejects a changed byte in the final chunk. The pinned 3.2.1 checker accepts the generated relation. One case passes in 0.01 seconds.

Implementation revision: `4292fa13c494a8d27c40fd27f8f78b727ada3e1a`. The compiler, producer checks and source export pass. No new key generation, proofs, deployment or performance comparison accompanies this change. Upstream describes this instruction as a temporary bridge. The Lean byte representation stays independent of the instruction choice at future pins.

## Concatenation on a chunk boundary

A packed prefix ending on a 31-byte boundary joins the suffix's existing
chunks in Encode order. The independent producer still checks the canonical
chunk bounds and the FAB return order.

In the `AlignedByteConcat.joinTail` fixture, a public Bytes31 prefix joins a
one-byte slice of a public Bytes2 value. On the pinned ZKIR 3.2.1
`mock-compile`, the relation changed from 16 to 12 instructions and from
149 to 132 rows. Both builds used K9. The Impact plans matched byte for byte.
Both native runs accepted the same 32-byte result and rejected a changed
public transcript output.
[Lean fixture](../../tests/AlignedByteConcat.lean) · [Native check](../../runtime/tests/aligned_byte_concat.rs)

The baseline relation SHA-256 was
`feb44bcee7f5b1cdd4961b61073ca6fd7cf4fce17384c15009f67bc11b0e39fd`.
The optimized relation SHA-256 is
`45c70ed2375e1a03aa5b69f592749cbef2ffaa5e29eda4a35e35005af40b4543`.
