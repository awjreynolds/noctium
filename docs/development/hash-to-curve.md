# Hash ordered fields to a Jubjub point

`hashToCurve([field1, field2, ...])` hashes an ordered list of Native fields into a typed `JubjubPoint`. The source bound is 0–1024 fields. This is the complete signature of the pinned native `hash_to_curve` instruction. It has no curve selector or byte/FAB overload.

```lean
import Noctium.Frontend
open scoped Noctium

noctium_circuit accountPoint where
  public domain : Native
  private secret : Native
  output point : JubjubPoint := disclose(hashToCurve([domain, secret]))
end
```

The operation uses Midnight's native Poseidon-based hash-to-Jubjub algorithm. It adds no application domain field. Supply an explicit domain in the input list when your protocol requires one. Argument order matters. Bytes and other logical types require explicit conversion to the intended field representation.

Empty input follows the native hash algorithm. Both empty and nonempty computations retain operand assertions and private origins. Derived private points require explicit disclosure at public sinks. Typed results compose with existing point arithmetic, coordinate extraction and `toBytes32` encoding. The Rust evaluator calls the pinned native hash API without Node or a new cryptographic dependency.

Typed Jubjub circuit outputs use the existing canonical projections: one Native field for a scalar and x/y fields for a point. The focused example checks both through contract results. Lean reference evaluation needs explicit hash and point-validation oracles. The source helper diagnostic trace does not return curve values yet.

The focused source and native cases are [HashToCurve.lean](../../tests/HashToCurve.lean) and [hash_to_curve.rs](../../runtime/tests/hash_to_curve.rs). They exercise empty, single and domain-prefixed inputs, point composition and encoding, altered input order/domain, changed private inputs and a retained assertion around the empty hash. A real Rust Session case checks witness execution. These checks add no keys, proofs or deployment qualification. Formal witness semantics and compiler-wide preservation remain tracked under [issue 21](https://github.com/awjreynolds/noctium/issues/21).

## Hash a typed witness payload

Use `hashToCurveValue(payload)` in a readable witness circuit to pack a
checked value with its FAB layout and hash the ordered fields. A private
provider result requires `disclose(hashToCurveValue(payload))` at a public
output. The witness session evaluates the payload once and the emitted
relation checks the point using the same field packing.

The paired case returns the same two points as Compact 0.36.1 for a record
containing Bytes32, Bool, UInt16, a fieldless enum and Native. The native
session rejects a malformed provider result. Changing the counter in the
private transcript also invalidates the original point.
[Lean source](../../tests/MixedFabHashToCurve.lean) · [Compact replay](../../tests/compact/mixed-fab-hash-to-curve.mjs) · [Native replay](../../runtime/tests/witness_control.rs)
