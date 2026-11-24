# Exact-length byte ledger values

Byte values use their declared length in native FAB alignment. Source types from `Bytes 0` through `Bytes 1024`, including `Bytes32`, use this representation in cells, map values and nested scalar leaves. Fixed-byte Map keys and Set elements support widths from `Bytes 0` through `Bytes 1024`. Wallet-specific key paths remain restricted to Bytes32. Other key restrictions stay unchanged.

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

[Issue 1048](https://github.com/awjreynolds/noctium/issues/1048) adds Bytes1 and Bytes33 fields to flat records stored in root Maps. The scoped fixture covers both a Bytes32 scalar key and a record key with Bytes1 and Bytes33 fields. Compact 0.36.1 and the selected Ledger 9/ZKIR 3.2.1 native checker match returned fields and retained aligned values after removal. Wrong key and value widths reject. See the [Lean fixture](../../tests/RootFixedByteRecordValuedMap.lean), [Compact comparison](../../tests/compact/root-fixed-byte-record-valued-map.mjs) and [native case](../../runtime/tests/root_fixed_byte_record_valued_map.rs).

## Flat record values in nested Maps

Scalar Map paths support flat record values with fixed-width byte fields. The two-level case stores a record with a Bytes1 label and a Bytes33 digest. Both owner buckets use the same leaf key, and the digests share their first 32 bytes. The comparison checks exact reads and overwrites, removal in one bucket, and preservation of the sibling and the other owner's value. It also covers a malformed digest width and lookup of the removed key. [Lean fixture](../../tests/NestedFixedByteMapRecordValues.lean) · [Compact oracle](../../tests/compact/nested-fixed-byte-record-values.mjs) · [Native replay](../../runtime/tests/nested_fixed_byte_record_values.rs)

To reproduce the comparison, use Compact 0.36.1 (`COMPACTC_0361`) and Compact Runtime 0.21.0 (`COMPACT_RUNTIME_0210`). The runtime argument is the package directory containing `package.json`.

```sh
mkdir -p build/experiments
scratch=$(mktemp -d build/experiments/nested-map-values.XXXXXX)
trap 'rm -rf "$scratch"' EXIT
node tests/compact/nested-fixed-byte-record-values.mjs \
  "$COMPACTC_0361" "$COMPACT_RUNTIME_0210" > "$scratch/compact.json"
lake exe noctium compile tests/NestedFixedByteMapRecordValues.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --output "$scratch/native"
NOCTIUM_NESTED_FIXED_BYTE_RECORD_VALUES_DIR="$scratch/native" \
NOCTIUM_NESTED_FIXED_BYTE_RECORD_VALUES_COMPACT="$scratch/compact.json" \
  cargo test --manifest-path runtime/Cargo.toml --no-default-features \
  --features zkir-321 --test nested_fixed_byte_record_values -- --ignored
```

The record-key case uses one Bytes32 parent and an inner key with Bytes1 and Bytes33 fields. Its value stores a Bytes1 label and Bytes33 digest. Compact and the native checker compare six exact readbacks across insertion, overwrite and removal, then check both surviving cells. The fixture rejects a wrong-width ID, a wrong-width digest and lookup of the removed key. To rerun, emit `NestedRecordKeyByteValues.lean` with the same target and run the Compact oracle. Pass the generated directory and oracle JSON to `nested_record_key_byte_values` through `NOCTIUM_NESTED_RECORD_KEY_BYTE_VALUES_DIR` and `NOCTIUM_NESTED_RECORD_KEY_BYTE_VALUES_COMPACT`. [Lean fixture](../../tests/NestedRecordKeyByteValues.lean) · [Compact oracle](../../tests/compact/nested-record-key-byte-values.mjs) · [Native replay](../../runtime/tests/nested_record_key_byte_values.rs)

The two-parent case stores the same record key under two Bytes32 groups for one owner. Compact 0.36.1 and the native checker match six readbacks and the exact surviving keys and values after insertion, overwrite and removal. Both reject the wrong ID or digest width and lookup after removal. To rerun, emit `NestedTwoParentRecordKeyValues.lean` with the same target and run the two-parent Compact oracle. Pass the generated directory and oracle JSON to `nested_record_key_byte_values` through `NOCTIUM_TWO_PARENT_RECORD_KEY_VALUES_DIR` and `NOCTIUM_TWO_PARENT_RECORD_KEY_VALUES_COMPACT`. Separate Lean and Rust schema checks accept 13 scalar parents and reject 14. [Lean fixture](../../tests/NestedTwoParentRecordKeyValues.lean) · [Compact oracle](../../tests/compact/nested-two-parent-record-key-values.mjs) · [Native replay](../../runtime/tests/nested_record_key_byte_values.rs)

### Circuit sizes for the matched Map fixtures

Both fixture pairs use the same logical inputs, ledger updates and returned values. The differential tests check exact surviving storage and rejected inputs. Sizing used Noctium `0fd61b70`, Compact 0.36.1 (`7fa3a117c`), and the same pinned ZKIR 3.2.1 `mock-compile` on both outputs. Noctium emitted ZKIR JSON 3.2 with the default ledger target. Compact emitted JSON 3.1 with `--skip-zk`. [Scalar-key evidence](https://github.com/awjreynolds/noctium/pull/1182) · [Record-key evidence](https://github.com/awjreynolds/noctium/pull/1186) · [Sizing tool pin](../../profiles/midnight-ledger-9-zkir-3.2.1.json)

| Inner key | Entrypoint | Noctium rows | Compact rows | Noctium K | Compact K | Noctium instructions | Compact instructions |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Bytes32 | `initializeOwner` | 141 | 145 | 8 | 8 | 23 | 14 |
| Bytes32 | `exercise` | 1,595 | 1,409 | 11 | 11 | 193 | 127 |
| Bytes32 | `inspect` | 671 | 575 | 10 | 10 | 67 | 41 |
| Bytes32 | `lookupAbsent` | 269 | 224 | 9 | 8 | 22 | 12 |
| Record | `store` | 348 | 379 | 9 | 9 | 47 | 25 |
| Record | `lookup` | 307 | 274 | 9 | 9 | 26 | 13 |
| Record | `remove` | 210 | 223 | 8 | 8 | 21 | 9 |

The Noctium fixtures declare public circuit inputs. Their relations read those values through the ledger transcript. Compact puts the source argument fields in the relation header. In a second record-key run, Noctium used explicit `arguments` and the same number of header fields as Compact. The existing native differential test also passed on those artifacts.

| Entrypoint | Header input fields, both | Noctium explicit-argument rows | Compact rows | K, both |
| --- | ---: | ---: | ---: | ---: |
| `store` | 8 | 384 | 379 | 9 |
| `lookup` | 5 | 341 | 274 | 9 |
| `remove` | 5 | 223 | 223 | 8 |

To reproduce the first table, emit the Lean fixtures with `--emit ledger` as above, compile the paired `.compact` files with `--skip-zk` into separate directories, and run `zkir mock-compile` on each `.zkir` file. For the explicit-argument variant, change the input declarations in `NestedRecordKeyByteValues.lean` to `private`, list each entrypoint's arguments in declaration order with `arguments [...]`, and wrap their ledger uses in `disclose(...)`. Use a scratch copy and pass its emitted directory to the same native comparison. These measurements cover synthesized rows and K. Proving latency and key-transfer cost remain unmeasured.

## Qualification

The focused fixture is [BytesStorage.lean](../../tests/BytesStorage.lean), with the native case in [byte_storage.rs](../../runtime/tests/byte_storage.rs). Implementation and measured results are tracked in [issue 79](https://github.com/awjreynolds/noctium/issues/79).

The entrypoint has 4,813 ZKIR instructions, 1,208 native inputs, 80 transcript groups and 82 return fields. Private inputs retain 1,122 bytewise/scalar fields, including the assertion condition. The producer caps are 8,192 instructions and 2,048 inputs. Vector, return and symbolic-expression limits stay unchanged. These are structural measurements, not K or proving-time results. Private byte packing remains an efficiency task in [issue 74](https://github.com/awjreynolds/noctium/issues/74).

The native case passes three updates and all 14 old/new results in 0.05 seconds. It checks lengths 0, 1, 31, 32, 33 and 1024, trailing zeros, skipped missing reads, overwrite and sibling preservation. Changed transcript data, a false assertion in an empty write, malformed input lengths, Null or misaligned cells, noncanonical atoms and wrong leaf/key schemas reject.

The 66-job compiler build, source fixture, producer-cap guards, guide snippet and legacy 3.2.0 runtime library compilation pass. One focused control case checks projection order, ranges and empty reads. The retained public Bytes32 native compatibility case also passes in 0.06 seconds. No repeated witness Session campaign was run.

This storage slice covers source and native query-context checking. [Foreign ledger keys](foreign-trees.md) have separate evidence. Non-flat record leaves, proofs, finalized deployment and full compiler preservation remain separate work.
