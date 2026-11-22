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
run the Rust case. Other Map layouts remain open.
[Lean fixture](../../tests/SealedMapConstructor.lean) ·
[Compact oracle](../../tests/compact/sealed-map-constructor.mjs) ·
[Native checker](../../runtime/tests/sealed_map_constructor.rs)

Ledger 9.1.0.1 finalized deployment at localnet height 50646. Decoded state
matched the exact native constructor output with key 5, value 42 and an empty
neighboring sealed Map. The `get` call finalized at height 50649 with the
same full contract state digest. The lookup relation used K7 and 84 rows.
[Finalized receipt](sealed-map-localnet-receipt.json)

## Seed a Counter and a scalar List

```lean
sealed counter total
sealed list items : Native
constructor(amount : UInt 16, first : Native) where
  increment total by 70000
  increment total by amount
  pushFront items := first
  pushFront items := 42
end
```

Root Counters and scalar Lists start at zero and empty. Counter increments
take the existing native UInt32 immediate or a UInt16 source expression.
List pushes apply in source order. The constructor supports these actions on
ordinary and sealed state. Sealed slots allow reads, and entrypoints reject
writes to them.

With `amount = 5` and `first = 17`, the pinned Compact oracle and the native
checker agree on Counter 70005, List length 2 and head 42. The Compact
fixture splits the constant 70000 into two UInt16 increments. Noctium's
native `inspect` relation uses K7 and 116 rows.
[Lean fixture](../../tests/SealedRootCounterListConstructor.lean) ·
[Compact oracle](../../tests/compact/sealed-counter-list-constructor.mjs) ·
[Native checker](../../runtime/tests/sealed_counter_list_constructor.rs)

Ledger 9.1.0.1 finalized deployment at localnet height 51062. The state
matched the native constructor output. The `inspect` call finalized at
height 51065 and preserved the exact deployed state bytes.
[Finalized receipt](sealed-counter-list-localnet-receipt.json)

## Seed a Set

```lean
sealed set registered : Native
sealed set emptySet : Native
constructor(key : Native) where
  insert registered[disclose(key)]
end
```

Root scalar Sets start empty and accept typed keys in constructors. Duplicate
inserts leave a single member. Sealed Sets allow membership and size reads and
reject entrypoint mutations. Ordinary Sets share the same constructor syntax.

The Lean artifact and Compact reference cover two inserts of key 17, a read
confirming size 1, and an adjacent empty sealed Set. The Compact reference also
checks an absent key. The native relation uses K7 and 120 rows.
[Lean fixture](../../tests/SealedRootSetConstructor.lean) ·
[Compact oracle](../../tests/compact/sealed-set-constructor.mjs) ·
[Native checker](../../runtime/tests/sealed_set_constructor.rs)

Ledger 9.1.0.1 finalized deployment at localnet height 51343. The state
matched the native constructor output. The read at 51346 preserved the full
deployed state bytes. [Finalized receipt](sealed-set-localnet-receipt.json)

## Initialize an opaque string

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
