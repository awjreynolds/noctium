# Typed Boolean gates

`boolAnd(left, right)`, `boolOr(left, right)` and `boolXor(left, right)` take two `Bool` expressions and evaluate both operands. `andThen(left, right)` evaluates the right operand only when the left operand is true. `orElse(left, right)` evaluates the right operand only when the left operand is false.

```lean
import Noctium.Frontend
open scoped Noctium

noctium_circuit eligible where
  private member : Bool
  private unused : Bool
  output allowed : Bool := disclose(boolAnd(member, unused))
end
```

The public and private source ABI still represents Boolean values as constrained Native fields, zero or one. Each new gate bridges its operands to the native `Bool` type using typed `load_constant` values and `cond_select`, emits `and`, `or` or `xor`, then encodes the result back to one Native field. Existing Boolean source paths retain their representation.

Private origins propagate through each gate. Releasing a result requires `disclose`. Both operand computations retain their assertions, including the right operand of `boolAnd(false, ...)` and `boolOr(true, ...)`. These gates do not authorize disclosure or hide information in a public result.

The producer validates actual typed Bool operands, nonempty native gate inputs and canonical single-field Bool constants. A constrained Native field is insufficient as a typed gate operand until bridged. Other `load_constant` codecs remain unsupported.

The focused source and native cases are [BooleanGates.lean](../../tests/BooleanGates.lean) and [native_boolean_gates.rs](../../runtime/tests/native_boolean_gates.rs). They cover truth tables, nested XOR parity, output binding, eager assertions and malformed producer operands. A host Session case exercises the witness interpreter. This slice adds no keys, proofs or deployment qualification.

[LazyBoolean.lean](../../tests/LazyBoolean.lean) checks short-circuiting in ordinary circuits. An inactive right operand skips the check on a `UInt 8` to `UInt 1` narrowing. The active path still enforces the bound, including inside a nested lazy expression. This expression-level support uses the shared guarded lowering. Witness scheduling and ledger effects use their own statement controls.

```sh
lake exe noctium compile tests/LazyBoolean.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --output build/lazy-boolean
NOCTIUM_LAZY_BOOLEAN_DIR="$PWD/build/lazy-boolean" \
  cargo test --locked --manifest-path runtime/Cargo.toml --no-default-features \
  --features zkir-321 --test native_boolean_gates \
  lazy_boolean_gates_skip_inactive_uint1_narrowing -- --ignored --exact
```

The separate formal witness semantics needs reconciliation with the expanded byte, curve and Boolean language. [Issue 21](https://github.com/awjreynolds/noctium/issues/21#issuecomment-6971590829) tracks that gap. The focused execution cases do not establish witness-erasure or whole-language preservation.

`ite(condition, thenValue, elseValue)` binds the condition once. Branches join when their types match or when both are bounded unsigned integers, in which case the wider bound becomes the result type. A `UInt 1` arm joined with a `UInt 8` arm returns `UInt 8`. Only the selected branch's dynamic checks apply. `select` evaluates both branches. The [ordinary Lean fixture](../../tests/LazyConditional.lean) and [pinned Compact comparator](../../tests/compact/LazyConditional.compact) check inactive and active narrowing, the bounded result join, and same-type Boolean branches. The [Compact runtime comparison](../../tests/compact/lazy-conditional.mjs) also selects a record through a ternary and checks that only its selected witness provider runs. The [readable Lean fixture](../../tests/ReadableLazyConditional.lean) selects an aggregate through `if`; its native harness checks the chosen provider, guarded assertion and relation. The [ordinary native check](../../runtime/tests/native_boolean_gates.rs) changes each private condition in an accepted proof input and checks rejection against the emitted relation.
