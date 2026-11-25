# Native unsigned scalar slice

The Rust evaluator and C ABI implement the scalar rules in `Noctium/ScalarPolicy.lean`. This extends the existing Native/Bool representation. It adds no Compact runtime or compiler dependency.

Normalized plan types use `UIntRange<N>`, with a canonical decimal exclusive bound `1 <= N <= 2^248`. Runtime values use canonical decimal JSON strings in `[0,N)`. JSON numbers, signed strings, redundant leading zeroes and string booleans reject. The inclusive maximum is `N-1`. The supported source forms UInt width and UIntRange bound normalize before reaching the runtime. User-defined type aliases remain outside this slice.

The new expression schema is:

| Tag | Fields | Rule |
| --- | --- | --- |
| `uint` | `maximum`, `value`, both decimal strings | Validate inclusive maximum and value |
| `uadd` | `left`, `right`, `maximum` | Result maximum equals the sum of operand maxima |
| `usub` | `left`, `right`, `maximum` | Result maximum equals the left maximum, underflow rejects |
| `umul` | `left`, `right`, `maximum` | Result maximum equals the product of operand maxima |
| `cast` | `type`, `value` | Checked scalar conversion |
| `sub` | `left`, `right` | Native field subtraction |

Unsigned arithmetic recomputes the inferred maximum from operand types. A supplied maximum must match exactly. Inferred maxima above `2^248-1` reject even when particular operand values produce a small result. Native arithmetic retains field semantics and requires Native operands. The Lean frontend inserts explicit casts for mixed Native/unsigned arithmetic. Boolean arithmetic requires a cast.

Casts to Bool use zero/nonzero semantics. Casts to an unsigned type validate the actual value against the target maximum, including narrowing. Widening changes the declared type without changing the number. Equality and eager selection require exact scalar types, including the unsigned maximum. Outputs require exact declared types and explicit public visibility.

Unsigned state cells and map schema types use the existing scalar field encoding. Decoding a state cell rechecks its declared range. Nonempty initial maps and reads after writes retain the previous slice's restrictions. The runtime still requires the official circuit checker for compiled constraints and guards.

The C ABI remains version 1. A provider request carries the normalized type in `request.type`, for example `UIntRange<256>`. The response value is a decimal string. Wrong range or representation rejects without consuming the pending request. Native/Bool provider requests retain their existing encoding.

The bounded ZKIR whitelist now includes `neg`, `not`, `constrain_eq`, `constrain_bits` and `less_than`. Bit counts must be integers in 1 through 248. Native ZKIR implements source subtraction through negation and addition. There is no native `sub` instruction. A zero-only range uses `constrain_eq`, and a power-of-two exclusive bound uses `constrain_bits` without an out-of-range comparison constant.

`runtime/tests/unsigned.rs` covers maximum and maximum-plus-one boundaries, malformed inputs, type confusion, inferred-range limits, subtraction underflow, conversions, output visibility and unsigned state cells. Its checked-in fixture comes from `examples/BoundedScalars.lean`. The native checker accepts private values 255 and 255 with public sum 510, then rejects a wrong sum, out-of-range input and nonzero previous cell.

## Bounded addition at a helper argument

Two UInt8 operands each have inclusive maximum 255. Their sum has
inclusive maximum 510 and exclusive bound 511. Compact accepts the sum
as a `Uint<0..511>` helper argument. Noctium accepts it as `UIntRange 511`.
Both reject changing only the helper parameter to the exclusive bound
510. The declared return still admits 510, so the rejection is at the
argument boundary. Both accepted runs return 510 for 255 + 255.

The emitted Noctium Impact plan normalizes the operands to
`UIntRange<256>` and the return to `UIntRange<511>`. The Rust check
confirms that the selected Ledger 9.1.0.1 / ZKIR 3.2.1 relation accepts
the call and the return retains the inclusive maximum 510. Compact
0.36.1 (`7fa3a117c`) records operand `maxval` 255 and result `maxval` 510
in `compiler/contract-info.json`. Its generated runtime is checked with
Compact Runtime 0.21.0.
[Lean fixture](../../tests/BoundedUintHelper.lean) ·
[Compact reference](../../tests/compact/bounded-uint-arithmetic.mjs) ·
[Native check](../../runtime/tests/unsigned.rs)

```sh
set -eu
mkdir -p build/experiments
scratch=$(mktemp -d "$PWD/build/experiments/bounded-helper.XXXXXX")
trap 'rm -rf "$scratch"' EXIT
lake build Noctium.Cli Noctium.Compiler Noctium.Frontend
lake env lean tests/BoundedUintHelper.lean
node tests/compact/bounded-uint-arithmetic.mjs \
  "$COMPACTC_0361" "$COMPACT_RUNTIME_0210"
lake env lean --run NoctiumMain.lean compile tests/BoundedUintHelper.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --output "$scratch/native"
NOCTIUM_BOUNDED_HELPER_DIR="$scratch/native" \
  cargo +1.100.0 test --locked --manifest-path runtime/Cargo.toml \
  --no-default-features --features zkir-321 --test unsigned \
  bounded_uint_addition_crosses_the_checked_helper_boundary -- --ignored --exact
```

## Repeated-call state guard

Run [`tests/scalars/replay-bounded-scalars.sh`](../../tests/scalars/replay-bounded-scalars.sh) for a focused replay comparison. The [Lean source runner](../../tests/scalars/BoundedScalarsReplay.lean) accepts two identical zero-sum calls at total zero, then accepts a sum of two. The [native Rust test](../../runtime/tests/bounded_scalars_replay.rs) checks the same three calls through pinned native 3.2.1 `prepare` and ZKIR `check`. A sum of three passes both checks from a fresh zero state. After the accepted sum of two, preparation returns an execution but the native checker rejects it at the state guard. The last accepted decoded total stays two, and the entrypoint has no committed call returns.

The result separates two policies: this state guard rejects a later call after a nonzero write, but it does not enforce at most one successful call. Two zero-sum calls form the shortest counterexample to an at-most-one-success policy. The test output records accepted state totals and an empty return list. It does not print private inputs. The Lean runner checks the source evaluator, while the Rust test checks freshly emitted Impact and ZKIR through the selected native runtime. Neither check is a deployed transaction or a proof of compiler correctness.

The linked C++ harness also executes this source-generated fixture through typed providers. Reuse the qualified native fixture's parameters/address to prepare both public envelopes:

```sh
python3 runtime/tests/prepare_abi_fixture.py "$QUALIFIED_ARTIFACTS" /tmp/noctium-abi-public.json
python3 runtime/tests/prepare_abi_fixture.py "$QUALIFIED_ARTIFACTS" /tmp/noctium-abi-unsigned.json --unsigned-fixture
env -i PATH=/usr/bin:/bin /tmp/noctium-cpp-smoke /tmp/noctium-abi-public.json /tmp/noctium-abi-unsigned.json
```

Build/link commands are in [native-runtime-abi.md](native-runtime-abi.md). The unsigned test supplies both private values from C++, verifies canonical/range/type response rejection, and obtains public result 510 after official checking. The original claim and its invalid/replay checks remain the Native/Bool regression.

This runtime check does not generate a proof or submit a ledger transaction. Issue 33's parent integration separately qualifies the generated relation, key material, prover and local ledger roundtrip. General scalar feature equivalence remains broader than this first unsigned slice.
