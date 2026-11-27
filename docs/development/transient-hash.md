# Ordered Native transient hashing

`transientHashNativeVector([values...])` hashes an ordered list of zero through 1024 Native fields with the pinned ZKIR `transient_hash` instruction. It adds no domain, alignment, type or length operands. The native algorithm itself binds the vector length.

```lean
import Noctium.Frontend
open scoped Noctium

noctium_circuit hashFields where
  private first : Native
  private second : Native
  private third : Native
  output commitment : Native := disclose(
    transientHashNativeVector([17, first, second, third]))
end
```

The leading 17 is an explicit application choice. The compiler does not insert one. Field order and vector length form part of the native hash definition. Native inputs require canonical field values. Bool, UInt and JubjubScalar values need an explicit supported conversion before entering the raw vector.

`poseidon2(domain, left, right)` retains its existing meaning: the hash of exactly `[domain, left, right]`. The compiler shares an equivalent vector computation, while evaluating every operand and its assertions before reusing a result. Chaining pairwise calls produces a different hash from a single longer vector.

## Typed scalar preimages

`transientHashValue(value)` hashes one `Native`, `Bool` or bounded `UInt`
value in ordinary and readable circuits. It uses one canonical Native field.
`false` and `true` encode as zero and one. Equal field representations produce
the same hash across the supported scalar types, as observed in pinned
Compact 0.36.1. Private origins and partial operand checks still apply.
[Source fixture](../../tests/ScalarTransientHash.lean) · [Native test](../../runtime/tests/scalar_transient_hash.rs) · [Compact oracle](../../tests/compact/scalar-transient-hash.mjs)

## Empty vectors and semantic evaluation

The pinned fixed-length Poseidon implementation returns zero for an empty vector. This is native behavior, not a replacement for a missing hash implementation. Lean semantic evaluation requires a configured transient-hash oracle and fails closed by default, including for empty vectors. The Rust evaluator calls the native implementation directly.

Private origins propagate from every operand. Publishing the derived hash requires explicit disclosure. A cached hash result does not skip operand assertions.

## Checked FAB payloads

Ordinary circuits use `transientHashFab(environment, type, [fields...])` with
typed leaf expressions listed in declaration and index order. The checked
layout supports nested records, tuples and fixed vectors with Native, Bool,
bounded UInt, fixed Bytes1 through Bytes32, or payload-free enum leaves.
Empty tuples and vectors contribute zero fields. FAB encoding packs Bytes32
into a one-byte high field and a 31-byte low field. The native preimage limit
is 1024 fields. Every input contributes its disclosure origin.

The mixed fixture checks a six-field preimage against Compact 0.36.1. Changing
the UInt16 field changes the hash. Changing either commitment opening leaves the
hash unchanged. [Lean fixture](../../tests/MixedFabCommitments.lean) · [Native
test](../../runtime/tests/mixed_fab_commitments.rs) · [Compact oracle](../../tests/compact/mixed-fab-persistent-hash.mjs)

The nested fixture compares an eight-field mixed preimage, its reversed
vector order, and an empty preimage against the same Compact release.
[Lean fixture](../../tests/NestedTransientHash.lean) · [Native
test](../../runtime/tests/nested_transient_hash.rs) · [Compact oracle](../../tests/compact/nested-transient-hash.mjs)

`persistentCommitFab` and `transientCommitFab` accept a checked
`CompositeType.scalar .native` layout with one Native payload value.
The pinned Compact `Field` overloads agree on both digests for payload 41,
a Bytes32 opening filled with 9 and Native opening 19. The checked output
still requires explicit disclosure when a payload or opening is private.
[Lean fixture](../../tests/BoundedFabHashCommit.lean) ·
[Native check](../../runtime/tests/bounded_fab_hash_commit.rs) ·
[Compact replay](../../tests/compact/bounded-fab-hash-commit.mjs)

Readable circuits use `transientHashValue(payload)` directly on a checked
composite value. The payload evaluates once. Its fields use the same FAB
order and fixed-byte chunk packing as the ordinary route. A private
payload still requires explicit disclosure to publish its digest.
[Lean fixture](../../tests/ReadableFabHash.lean) · [Native test](../../runtime/tests/readable_fab_hash.rs)

## Schnorr reference boundary

The pinned Compact Schnorr message is `Vector<N, Field>`. Its challenge preimage is exactly `[announcement.x, announcement.y, publicKey.x, publicKey.y] ++ messageFields`. Source struct/vector flattening preserves that order and emits no extra operands. [Pinned standard library](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/compiler/standard-library.compact#L360), [datatype flattening](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/compiler/circuit-passes/flatten-datatypes.ss#L80), [ZKIR lowering](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/compiler/zkir-v3-passes/reduce-to-zkir.ss#L255).

The [typed signature helpers](signatures.md) build on this field-vector preimage contract, tracked in [issue 82](https://github.com/awjreynolds/noctium/issues/82).

## Evidence

[Issue 81](https://github.com/awjreynolds/noctium/issues/81), [Source fixture](../../tests/TransientHash.lean), [native case](../../runtime/tests/transient_hash.rs). The focused case checks empty, singleton, legacy three-field and longer vectors, exact native reference values, order/length binding, cached operand assertions and committed results.

The 67-job compiler/Claim build, source fixture, producer inventory/bounds/type guards, guide snippet and legacy 3.2.0 runtime library compilation pass. The native case passes in 0.02 seconds. One focused host/control case covers both operation routes at lengths 0, 1, 3 and 1024, legacy equivalence and malformed type/arity rejection in 0.05 seconds. Re-exported Source artifacts match the retained fixture bytes.

The entrypoint has 15 instructions, six private inputs and six output fields. Four hash operations have arities 3, 0, 1 and 5. Equivalent legacy/vector expressions and repeated longer vectors share their computations. These are structural counts, not proving-time measurements.

No new keys, proofs, deployments or K/proving-time benchmarks qualify this slice. Signature helpers have separate scoped evidence. Full signature assurance and compiler preservation remain separate work.
