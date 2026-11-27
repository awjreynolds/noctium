# Committed getter results

Entrypoints return named Native, Bool, bounded UInt, fixed Bytes, Jubjub and
supported foreign-curve values. Helper entrypoints also return checked composite
values. Return expressions resolve after state effects, including ledger reads after writes.
`tests/NativeReturns.lean` contains a getter and an update operation:

```lean
read balance as currentBalance
read count as currentCount
return balanceValue : Native := currentBalance
return countValue : UInt 64 := currentCount
return enabledValue : Bool := enabled
```

Return declarations must be trailing statements at the entrypoint's top level.
Labels are unique. The type checker validates each expression against the final
read environment. Returning private data requires explicit `disclose(...)`.
This authorizes release to the application result channel. The return itself
does not put clear values in the transaction's ledger call.

Logical returns expand into canonical Native Fields in declaration order:

| Logical type | Native fields |
| --- | --- |
| Native, Bool, UInt | One field; Bool and UInt retain their bounds |
| Bytes32 | Two chunks, using the existing FAB byte-alignment order |
| Bytes(n) | `ceil(n / 31)` chunks in FAB order, including zero fields for Bytes0 |
| JubjubScalar | One canonical scalar-to-Native encoding |
| JubjubPoint | Two affine coordinates, x then y |
| Foreign curve values | The native family's canonical encoded fields |
| Composite helper result | One Native field per checked layout leaf |

Point and scalar values retain the existing canonical/subgroup input and
expression checks. Bytes32 results retain every digest bit. The 256-field output
limit applies after expansion.

The compiler emits those values as ZKIR outputs. The native call prototype's
`output` contains the same fields, and Midnight commits them with the call input
and communication randomness. The ledger stores that commitment. It does not
need a separate clear return field.

## Native call arguments

An entrypoint selects committed arguments from its private inputs:

```lean
entry advance uses returnInput arguments [amount] where
  read balance as beforeBalance
  write balance := disclose(add(beforeBalance, amount))
end
```

The ordered `callInputs` list becomes the native relation's input header and
`ContractCallPrototype.input`. Selected values no longer appear in the private
witness transcript. The communication commitment binds these arguments together
with the returned fields. Selecting an argument preserves its privacy. A
private value or decision reaching a public state write or result still
requires explicit `disclose`.

Direct entrypoints accept Native, Bool, bounded UInt, fixed Bytes, Jubjub
scalars and points, and the supported foreign-curve values. Inputs use the
same field order as the return table above. Bytes use FAB chunks from high to
low, and Bytes0 contributes no fields. Foreign values keep their exact native
type in the input header. UInt and Bool ranges, byte chunk bounds and the
Jubjub canonicality checks still run in the circuit.

The compiler and bundle reader require exact header names, types and order.
Unknown, duplicate or public selections reject. Limits are 256 logical
arguments and 256 physical fields after encoding. Readable hosted witness
circuits use the same `arguments` clause. Select private scalar or fixed-byte
source parameters. Provider responses stay in their private transcript slots.
The witness sidecar authenticates the argument order against the native header
and the Impact plan. The host still passes each logical parameter to the witness
program using its original type. [Hosted call fixture](../../tests/TypedCallArguments.lean)

The focused host/native case commits a Bytes33 value, a UInt8, a zero-bound UInt
and Bytes0. It checks exact header fields in declared argument order, the
remaining salt and provider reply, and rejection after changing an argument
or reordering the sidecar binding.

A hosted helper also accepts a private aggregate parameter in its entirety.
Select its name in `arguments [request]`. The caller supplies
`request := fields(amount, okay)` in the argument list of `callCommitment`.
The compiler expands the declared layout into adjacent Native slots in checked
order. The host passes the original typed record to the provider. The witness
validator rejects partial or reordered aggregate groups. Empty aggregates still
take a label in the call interface and contribute zero fields.
[Aggregate argument fixture](../../tests/WitnessSource.lean)

An ordinary circuit can declare a scalar tuple such as
`private pair : [UInt 8, Bool]` and project its fields with
`tupleAt(pair, 0)` and `tupleAt(pair, 1)`. Select `arguments [pair]`
to commit the two typed fields in tuple order. Public tuples use the
same layout with public visibility. Explicit disclosure governs releases
of private fields. [Ordinary tuple fixture](../../tests/OrdinaryTupleInputs.lean)

Emitted `noctium.json` describes ordered groups in standalone
`inputViews` and entrypoint `callInputViews`. The corresponding input
rows retain each field's type and visibility. Native execution uses the
ordered scalar fields.

Readable witness circuits also declare checked aggregate inputs with `Payload`
and a codec named in `using`. For example, `private payment : Payload paymentWire`
takes a typed record. A `public` declaration uses the same layout and includes
its fields in the public statement. The host receives the typed JSON value.
The compiler uses the codec's payload definition and leaves byte encoding to
an explicit `encode` call. `arguments [payment]` commits the private record in
layout order. Explicit `disclose` still governs releases from its fields.
[Readable payment example](../../examples/AggregateSerialization.lean)

Two builds at compiler revision `0ede45d` reproduced all 12 selected compiler
files, including the generated Rust binding. The authenticated Rust witness
API completed the provider call, generated the K9 proof for
`HostedCallArguments.review` (159 rows), verified it and attached it to the
native intent. The bundle manifest SHA-256 was
`9a600a97daa29d304e39e04b1979d8dc7d892887f9f2cb969483515cd26d71ee`.
This qualification ends at the proved intent.
The [typed argument example](../../tests/TypedCallArguments.lean) exercises mixed
input types, an independent private witness and the field order through the
native checker. A reordered header or an out-of-range byte chunk rejects even
with a recomputed commitment. [Typed call commitments](native-call-claims.md#check-the-call-payload-against-a-declared-interface)
reuse the same encoding on the caller side.

Rust callers prepare the operation, run `check(&execution, &circuit)`, then read
`execution.returns()` or `execution.returns_json()`. Primitive values retain their
logical types, so JSON uses booleans for Bool and decimal strings for Native and UInt.
Bytes32 uses `{kind:"bytes", values:[...]}`; scalar and point JSON use their
existing `jubjubScalar` and `jubjubPoint` shapes. The C runtime's completed JSON
response adds `result.returns` when nonempty.
Native transaction assembly uses the evaluated output and fresh communication
randomness. Bundle validation checks agreement among the plan return schema,
compiler metadata and native output header.

Composite helper results use `returnViews` metadata. Each view contains a logical
name, canonical schema and ordered physical Native return names. The runtime
validates the schema, field mapping and values during preparation and completion.
`returns()` retains physical fields for native callers. `returns_json()` groups
them into typed record, tuple, vector, enum, bytes and Unit JSON and omits their
physical aliases. The existing C JSON result path exposes the same logical views.
Empty composites retain their logical result with zero physical fields.

Readable witness circuits infer an aggregate result from an unannotated
`output`. The entrypoint commits that result by its declared label.

```lean
noctium_witness_circuit readPayment using paymentWire where
  private frame : Bytes 10
  output payment := disclose(decode(paymentWire, frame))
end

noctium_contract PaymentReader where
  entry readPayment uses readPayment where
    return payment
  end
end
```

One circuit can declare several aggregate outputs alongside typed scalar
outputs. Each named return selects its own fields in checked layout order,
even when the entrypoint returns the groups in a different order. The compiler
checks disclosure at each circuit output. The bundler authenticates each view
with the entrypoint artifacts.
[Complete example](../../examples/AggregateSerialization.lean)

Enums retain their variant tag and canonical padding checks. Bool and UInt fields
retain their bounds. Reordered or reused field mappings reject. A private field
still needs explicit disclosure in the source, including fields nested in a
composite result. Views never authorize disclosure. The current limit is 256
physical Native return fields and 256 logical views.

The source metadata includes return labels, types and expressions. Existing
entrypoints omit the optional `returns` field and keep empty native outputs.
The JavaScript development harness rejects nonempty returns instead of treating
them as an empty output. The native Rust runtime implements this feature.

`runtime/tests/native_returns.rs` provides one focused native sequence: getter,
two updates, and getter again, with exact expected balances, counters and Bool
results. It compares the output commitment and rejects a forged commitment,
a forged return expression and a mismatched declared return type. The source
fixture rejects a private return without disclosure.
The update operation now uses `amount` as a native call argument. The case checks
its raw preimage slot and absence from the private transcript. Changing that
argument still rejects after recomputing its communication commitment, because
the existing state transition and outputs no longer match.

`tests/NativeOpaqueReturns.lean` and `runtime/tests/native_opaque_returns.rs`
add one source/native example for Bytes32 and Jubjub results. Independent SHA-256
and group arithmetic agree with the named results and their six-field commitment.
The case covers a full-range scalar and rejects an altered digest high byte.

`tests/NativeBytes.lean`, `tests/ForeignOperations.lean` and `tests/Curve25519.lean`
also supply retained source/native return cases for general bytes and foreign
families. The staged helper path in `tests/IterationWitness.lean` returns a receipt
with a total, Bool vector, enum claim, bytes, nested Unit and an explicitly released
private offset. Its eight Native fields form one committed SDK result. The native
case checks active and inactive records and rejects an altered provider response.
Source guards reject removal of the field's disclosure. Codec checks reject
noncanonical Bool/UInt leaves and retain empty values.

The readable `readPayment` example commits seven native fields and exposes one
`payment` record. The authenticated host and native checker return the same
tuple, vector, enum and memo fields. They reject the three malformed input
variants from the pinned Compact comparison. The native checker rejects a
changed memo byte under the original commitment. The runtime rejects a
reordered field map. [Focused Rust test](../../runtime/tests/aggregate_serialization.rs)

The `inspectPayment` entrypoint returns two aggregates, a Bool and two bytes.
The authenticated host and native checker agree on each value. The test
checks distinct views in a different order from the circuit's declarations
and rejects a modified private frame under the original commitment.

Two fresh compilations reproduced all 21 ledger and witness files byte for
byte. The empty-vector example compiled with one logical view and zero physical
fields.

The selected `readPayment` entrypoint at compiler revision `d470fa2` used K9
and 298 rows. Its fresh native proof finalized on the Ledger 9.1.0.1 localnet.
The Rust client funded both transactions and checked the exact finalized state.
The authenticated bundle manifest digest was
`ebd3bb550d1be33f3cf6c691f7e979bcef5d76a8f0b9f30a3c447f03016f043c`.

| Action | Finalized block | Transaction ID |
| --- | ---: | --- |
| Deploy | 31695 | `93def8d638e89909ff83c4b5bed5c617695b587d4b0567d3cdc10fe42e78390d` |
| Call | 31698 | `60e77ad6397c52625ecb4871841b3b8843561862110b978a62db4cff7690dd4c` |

See the [native call protocol](native-call-claims.md) for composition evidence.
