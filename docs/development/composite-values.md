# Checked composite values and native qualification

`Noctium.Types.Values` consumes the `CheckedLayout` result from composite type compilation. `CompiledType` stores the exact compiler-result equality and canonical type fingerprint. Construction checks nominal identity, field order, scalar bounds and fixed lengths. `TypedValue` stores its successful flattening equality. `unflattenChecked` reconstructs a value and records equality with the supplied canonical leaves. Projection and decomposition compile the selected logical type again, preserving nominal identities.

`ValueExpressions` validates aggregate literal and scalar-expression construction. Its native witness view uses the same checked layout to emit scalar constraints, enum tag constraints and zero-padding constraints. Enum payload constraints apply under the selected variant. A Bool payload uses a UInt1 cast of `select(active, payload, 0)`. A Bool cast would test truthiness and would accept an invalid value such as 2. A Native payload in another variant retains its full field range.

`NativeExpression` is raw backend IR. Its proof certifies the leaf count, not canonicality of caller-supplied constraints. Callers must regenerate constraints with `checkNativeExpression` before lowering. Dynamic selection rechecks its parent leaves and preserves supplied constraints as additional obligations in their original order. Earlier index bounds therefore persist through chained selections, including values with zero leaves. Future source integration must preserve this boundary.

Dynamic fixed-vector selection emits a UInt constraint on the Native index with maximum `length - 1`. Empty vectors reject selection. The bound persists when the selected element has zero leaves. Component origins, index origins and control origins occupy separate fields. Enum projections also retain tag origins. These fields supply bookkeeping for DF-01. They do not authorize disclosure or enable aggregate source syntax.

## WireV1 and host checks

The Noctium wire is `noctium:aggregate:value:v1:`, a u32 little-endian descriptor length, the full canonical type descriptor, a u32 little-endian leaf count, then one fixed 32-byte little-endian canonical Native field per leaf. This format is distinct from ZKIR's minimal-length immediate strings and ledger proof-preimage SCALE encoding. The native fixture converts the same leaves into the upstream relation preimage.

The Rust codec accepts compiler schema JSON, recomputes the canonical descriptor and all layout counts, checks repeated nominal definitions for consistency, and validates each logical value against the layout. Iterative parsing and traversal preserve the checked limits, including retained children under zero-length vectors. Schema, logical JSON and wire inputs each have a 1 MiB transport limit. C ABI output buffers have owned tokens with copy and free operations.

Explicit aggregate casts support equal-shape tuple/vector widening. UInt leaves widen to larger inclusive bounds or Native. Bool, byte lengths and nominal struct/enum layouts remain exact. The host validates the source value before rebuilding the target value from its canonical leaves, under the existing allocation budget. Private leaf and control origins survive the conversion. Implicit runtime argument and return checks still require exact aggregate tokens. Lean emits the required casts at typed source boundaries. See [iteration](iteration.md) for the source/native example.

`runtime/tests/fixtures/aggregates` contains synthetic public fixtures emitted by `tests/CompositeValues.lean`. The canonical encoding is 543 bytes with SHA-256 `5c78e24dca26d0d5611b64b1589da13728aaf1a5450b42ec750a551d6bd8d440`. The current Lean fixture and one focused Rust exact-wire roundtrip check agree. Earlier twelve-case Rust and linked C++ qualification records apply to their historical source revisions. Cases include malformed descriptors, inconsistent nominal definitions, changed fingerprints, noncanonical scalars, invalid tags, nonzero padding, stale tokens, the 16,384-node retained-layout boundary and the 1 MiB transport boundary.

## Native relation evidence

`Noctium.Backend.AggregateFixture` calls the existing `Zkir.lowerCircuit` producer. The fixture includes a tuple, nominal struct, fixed vector, enum, bytes, unit and a zero-length vector. Private witness leaves and a private index feed the relation. Public expected leaves are asserted equal to the computed leaves. Outputs use explicit disclosure. The existing producer binds the public expected sequence and disclosed result sequence through Impact.

The pinned ZKIR 3.2.1 checker passed 14 raw-witness cases. Three valid cases cover the nested value, a full-width Native enum payload and an empty enum variant. Eleven rejecting cases cover changed public leaves, changed bound outputs, invalid enum tags, active Bool/UInt violations, nonzero padding, index bounds, incorrect selection and scalar/byte bounds. The checker bypasses the Lean evaluator.

The independent pinned native CLI compiled the relation at `k=8`, 184 rows. The existing loopback native proof server returned a self-verified 3,468-byte proof. `tests/composite-values/qualification-evidence.json` records the source, binary, checker, compiler and proof hashes. This evidence qualifies the typed backend's standalone relation. Ledger acceptance, component disclosure analysis and aggregate source routes belong to later work.

## Reproduce

With the pinned toolchains and existing proof service:

```sh
lake build Noctium.Backend.AggregateFixture Noctium.Types.ValueSchema Noctium.Types.ValueViews
lake env lean tests/CompositeValues.lean
lake env lean --run tests/CompositeValues.lean /private/tmp/noctium-aggregate-codec
lake env lean --run Noctium/Backend/AggregateFixture.lean /private/tmp/noctium-aggregate-native
node tests/composite-values/qualify.mjs /private/tmp/noctium-aggregate-native /private/tmp/noctium-zkir321-wasm/package/midnight_zkir_wasm_fs.js check
/private/tmp/noctium-native-zkir-321/bin/zkir compile /private/tmp/noctium-aggregate-native/aggregate.zkir /private/tmp/noctium-aggregate-native/aggregate.prover /private/tmp/noctium-aggregate-native/aggregate.verifier
node tests/composite-values/qualify.mjs /private/tmp/noctium-aggregate-native /private/tmp/noctium-zkir321-wasm/package/midnight_zkir_wasm_fs.js prove
```

Run the Rust gate from `runtime`:

```sh
RUSTUP_HOME=/private/tmp/noctium-rustup CARGO_HOME=/private/tmp/noctium-cargo CARGO_TARGET_DIR=/private/tmp/noctium-rust-runtime-321-target /private/tmp/noctium-cargo/bin/cargo +1.100.0 test --no-default-features --features zkir-321 --test aggregates
```

Build the host library with the same environment and `cargo +1.100.0 build --no-default-features --features zkir-321`, then run the C++ gate from the repository root:

```sh
/usr/bin/clang++ -std=c++17 runtime/tests/aggregate_cpp_smoke.cpp -Iruntime/include -L/private/tmp/noctium-rust-runtime-321-target/debug -lnoctium_runtime -Wl,-rpath,/private/tmp/noctium-rust-runtime-321-target/debug -o /private/tmp/noctium-aggregate-cpp-smoke
/private/tmp/noctium-aggregate-cpp-smoke runtime/tests/fixtures/aggregates/schema.json runtime/tests/fixtures/aggregates/value.json runtime/tests/fixtures/aggregates/wire.hex
```

## Construct a record in a readable circuit

Use a checked codec from the circuit's `using` clause to construct a nominal record.

```lean
let constructed := record(Payload readingWire, {
  active := enabled, count := amount, reading := measure
})
```

Supply each declared field once. Initializers execute once in the codec's
declaration order, which matches the pinned Compact 0.36.1 executable. Bind
effectful values before the constructor to choose their execution order.
The result carries the codec's nominal type. Private components still require
explicit disclosure at public sinks. [Source fixture](../../tests/ReadableRecordConstruction.lean)

## Compare two flat records

In a readable circuit, `eq(left, right)` compares records with the same
nominal type and direct Native, Bool or bounded UInt fields. The compiler
evaluates the operands in order. The result inherits private value and control
origins from both operands, so a public result may need explicit disclosure.
The fixture checks identical records and a difference in each field against
the pinned Compact oracle and the native relation. The replay test exercises
the same typed comparison in Lean.
[Lean fixture](../../tests/NominalRecordEquality.lean) · [Native check](../../runtime/tests/nominal_record_equality.rs) · [Compact fixture](../../tests/compact/nominal-record-equality.mjs)
