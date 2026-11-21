# Constructors and sealed deployment cells

A contract may declare public constructor arguments and typed cell initializers:

```lean
sealed cell name : OpaqueString
sealed cell decimals : UInt 8
constructor(name_ : OpaqueString, decimals_ : UInt 8) where
  initialize name := name_
  initialize decimals := decimals_
end
```

The constructor builds fresh genesis state. Other state uses typed defaults,
including empty maps and Lists and zero Counters. Each sealed cell must have one
initializer. Constructor parameters and cell types must match. Missing, extra,
out-of-range or incorrectly typed arguments reject.

`construct_state(plan, arguments)` evaluates the compiler-emitted constructor.
The native deployment assembler uses this path when the artifact declares a
constructor. Its deployment `state` argument then contains constructor arguments.
Without a constructor, existing explicit state configuration remains supported.
`create_state` remains the low-level explicit state constructor/hydrator.

## Seed a flat Map

```lean
sealed map entries : Native => UInt 64
constructor(key : Native, value : UInt 64) where
  insert entries[disclose(key)] := disclose(value)
end
```

Flat Maps begin empty. A constructor applies typed inserts in source order.
Entry points and helpers read a sealed Map. Source validation rejects writes
to it, and the native checker rejects a prepared call that changes it.

The fixture compares a seeded Native/Field-to-UInt64 Map and an empty sealed
Map against Compact 0.36.1. Both preserve the Maps during a write to a
neighboring Cell. The native checker rejects a constructor insert aimed at
a scalar Cell and an entrypoint write aimed at the sealed Map. Point
`NOCTIUM_SEALED_MAP_CONSTRUCTOR_DIR` at fresh ZKIR 3.2.1 compiler output to
run the Rust case. Funded execution and other Map layouts remain open.
[Lean fixture](../../tests/SealedMapConstructor.lean) ·
[Compact oracle](../../tests/compact/sealed-map-constructor.mjs) ·
[Native checker](../../runtime/tests/sealed_map_constructor.rs)

OpaqueString is deployment/host data, outside circuit `Ty`. Its cell contains one
raw UTF-8 FAB atom with Compress alignment. The codec preserves embedded U+0000
and rejects trailing U+0000 before constructing state. Ledger serialization
otherwise normalizes the atom and trims that trailing byte. Native compression
uses the exact UTF-8 byte count. `decode_opaque_string` checks Compress alignment,
the byte limit, FAB normal form and UTF-8. The pinned reference exercises the
same text in a Compact constructor and Map. [Reference runner](../../tests/compact/opaque-string-cases.mjs)

Run the reference with absolute paths for Compact 0.36.1 (`COMPACTC_0361`)
and `@midnight-ntwrk/compact-runtime` 0.21.0 (`COMPACT_RUNTIME_0210`).

```sh
scratch=$(mktemp -d)
trap 'rm -rf -- "$scratch"' EXIT
"$COMPACTC_0361" --version | grep -E '^0\.36\.1 \(7fa3a117c'
test "$(node -p 'require(process.argv[1]).version' "$COMPACT_RUNTIME_0210/package.json")" = '0.21.0'
"$COMPACTC_0361" --skip-zk tests/compact/OpaqueStringCases.compact "$scratch/compact"
mkdir -p "$scratch/node_modules/@midnight-ntwrk"
ln -s "$COMPACT_RUNTIME_0210" "$scratch/node_modules/@midnight-ntwrk/compact-runtime"
cp tests/compact/opaque-string-cases.mjs "$scratch/opaque-string-cases.mjs"
node "$scratch/opaque-string-cases.mjs"
```

The compiler rejects entrypoint writes to sealed cells, including inactive
writes. The runtime rejects a prepared call which changes a sealed cell. Bundle
validation binds the constructor descriptor and sealed state schema to compiler
metadata. The ledger VM has no separate sealed-cell permission type.

Constructors execute off chain. This feature does not prove constructor
execution on the ledger. Deployment assurance must bind the source artifact,
constructor arguments and actual genesis state. Private witness callbacks and
arbitrary initialization effects remain open.

`tests/ConstructorMetadata.lean` and `runtime/tests/constructor_metadata.rs`
cover initialized metadata, UTF-8 with a trailing zero byte, immutable metadata,
argument rejection and a forged-plan mutation. Broader initialization and
state-preservation proofs remain separate work. The focused native case passed
in under 0.01 seconds.
