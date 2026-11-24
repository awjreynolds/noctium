# Exact-length byte ledger values

Byte values use their declared length in native FAB alignment. Source types from `Bytes 0` through `Bytes 1024`, including `Bytes32`, use this representation in cells, map values and nested scalar leaves. Byte keys remain restricted to Bytes32. Other key restrictions stay unchanged.

The ledger stores public state. Writing a private witness value or a value derived from one requires `disclose(...)`. Byte storage preserves the existing disclosure checks.

```lean
import Noctium.Frontend
open scoped Noctium

noctium_circuit publishDigest where
  private nextDigest : Bytes 33
end

noctium_contract Digests where
  cell digest : Bytes 33
  entry replace uses publishDigest where
    write digest := disclose(nextDigest)
    read digest as currentDigest
    return saved : Bytes 33 := disclose(currentDigest)
  end
end
```

## Length and empty values

FAB normalizes trailing zero bytes in its stored value. The alignment retains the declared length, so reading a Bytes31 value restores all 31 bytes, including trailing zeros. A Bytes31 cell and a Bytes32 cell remain different even when every byte is zero. A field-aligned zero is a different representation too.

An empty byte value occupies an explicit byte-aligned cell of length zero. Missing state is Null. Reads distinguish these states even though the empty value contributes no payload fields to the native transcript.

ZKIR does not support a typed Bytes0 value. Noctium erases the empty payload and retains the ledger operation and any expression checks evaluated before producing the value. This follows the existing Source empty-byte semantics.

## Native read boundary

Nonempty ledger reads bind bounded Native chunks in FAB order, from the highest chunk to the lowest. Logical byte operations reconstruct the value in the low-to-high order required by ZKIR. Each chunk keeps its exact bit bound. Skipped guarded reads produce zero bytes of the declared length without inspecting the skipped path.

Public Bytes32 inputs keep their existing packed two-chunk prologue. Private byte input transport stays bytewise. Storage support adds no native opcode.

## Flat root Map record values

[Issue 1048](https://github.com/awjreynolds/noctium/issues/1048) adds Bytes1 and Bytes33 fields to flat records stored in root Maps. The scoped fixture covers both a Bytes32 scalar key and a record key with Bytes1 and Bytes33 fields. Compact 0.36.1 and the selected Ledger 9/ZKIR 3.2.1 native checker match returned fields and retained aligned values after removal. Wrong key/value widths and nested scalar/record-key record values reject. See the [Lean fixture](../../tests/RootFixedByteRecordValuedMap.lean), [Compact comparison](../../tests/compact/root-fixed-byte-record-valued-map.mjs) and [native case](../../runtime/tests/root_fixed_byte_record_valued_map.rs).

## Qualification

The focused fixture is [BytesStorage.lean](../../tests/BytesStorage.lean), with the native case in [byte_storage.rs](../../runtime/tests/byte_storage.rs). Implementation and measured results are tracked in [issue 79](https://github.com/awjreynolds/noctium/issues/79).

The entrypoint has 4,813 ZKIR instructions, 1,208 native inputs, 80 transcript groups and 82 return fields. Private inputs retain 1,122 bytewise/scalar fields, including the assertion condition. The producer caps are 8,192 instructions and 2,048 inputs. Vector, return and symbolic-expression limits stay unchanged. These are structural measurements, not K or proving-time results. Private byte packing remains an efficiency task in [issue 74](https://github.com/awjreynolds/noctium/issues/74).

The native case passes three updates and all 14 old/new results in 0.05 seconds. It checks lengths 0, 1, 31, 32, 33 and 1024, trailing zeros, skipped missing reads, overwrite and sibling preservation. Changed transcript data, a false assertion in an empty write, malformed input lengths, Null or misaligned cells, noncanonical atoms and wrong leaf/key schemas reject.

The 66-job compiler build, source fixture, producer-cap guards, guide snippet and legacy 3.2.0 runtime library compilation pass. One focused control case checks projection order, ranges and empty reads. The retained public Bytes32 native compatibility case also passes in 0.06 seconds. No repeated witness Session campaign was run.

This storage slice covers source and native checking. [Foreign ledger keys](foreign-trees.md) have separate evidence. Nested composite record leaves, proofs, deployment and full compiler preservation remain separate work.
