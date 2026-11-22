# Anonymous operators, map and fold

`Noctium.Helpers.Iteration` constructs ordinary checked Helpers declarations and call terms at compile time. The implementation is Lean. Its output follows the existing direct ZKIR, native ledger and host-neutral witness paths.

An operator names an existing helper or supplies an anonymous statement body. Missing parameter annotations come from actual argument types. A missing result annotation comes from the body returns. The compiler captures referenced outer values as typed arguments. Parameter and block bindings retain their lexical scopes. Generated declarations still pass ordinary helper checks. Frontend source references use Lean name resolution, including private definitions.

## Readable witness circuits

```lean
noctium_witness_circuit sumBytes where
  public values : Bytes 2
  public offset : Native
  let adjusted := map([values], fun value => add(value, offset))
  output sum : Native := fold(0, [adjusted], fun acc value => add(acc, value))
end
```

The compiler infers each parameter from the input sequence or fold seed. The
operator captures `offset` from the enclosing circuit. Fold evaluates its seed
first. Each complete sequence then evaluates once in source order, followed by
the operator once per element. The staged Helpers API accepts full statement
bodies and explicit types for empty tuples.

Use `fun item => do ... return value end` for a readable callback with local
`let` bindings and `prove` assertions. Both `map` and `fold` accept this body.
Each invocation evaluates its bindings and assertions in order, then evaluates
the return expression. Bindings stay local to the callback. Native results
still require `disclose` when they depend on private values.

```lean
let adjusted := map([values], fun value => do
  let widened := cast(Native, value)
  let result := add(widened, offset)
  prove boolNot(eq(result, 999))
  return result
end)
```

Use `for item in values do ... end` when the body performs effects such as
private reads, witness calls, assertions, or staging. The body sees the inferred
element type and captures enclosing values. The sequence expression runs once,
including when empty. The body runs in index order and its bindings stay inside
each iteration. If an empty tuple's body uses the item as a scalar, give it a
type through a direct typed use. A witness parameter or an annotated `let`
supplies the missing type. A loop also accepts `for item : UInt 8 in items do`.
The same witness parameter rule applies to readable `map` and `fold` callbacks.
The same item from an empty tuple supports separate Bool and UInt uses. The
checker gives each use its own type and checks the body. With zero elements,
the sequence expression still runs and the callback has no invocations. A
nonempty or annotated sequence keeps its declared element type. When neither
the declaration nor a unique inferred type is available, use the item in a
typed position. [Container loop and empty tuple fixture](../../tests/ReadableContainerLoop.lean)

The mixed-type empty tuple case returns seed 11 with zero operator callbacks
in the native Rust SDK, browser WASM, and Compact 0.36.1. Rust and WASM use the
same generated host plan.

For bytes `[4, 5]`, the native Rust witness executor, the browser WASM control
session and the Compact 0.36.1 oracle all request the sequence once, read and
update the private accumulator in order, evaluate the empty sequence once, and
return 9. The Rust checker accepts the emitted ZKIR 3.2.1 relation and verifies
ledger total 9. An incorrect second provider reply rejects before the empty
sequence is evaluated. [Compact oracle](../../tests/compact/ReadableContainerLoop.compact) · [Browser runner](../../sdk/web/tests/readable-container-loop.mjs)

To rerun the browser case, build the web package as described in the
[web witness SDK guide](web-witness-sdk.md). Emit the host plan, then serve the
package on loopback as in that guide.

```sh
.lake/build/bin/noctium compile tests/ReadableContainerLoop.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit control --output build/container-loop-control
cp build/container-loop-control/readableContainerLoopHost.control.json build/noctium-web/plan.json
cp sdk/web/tests/readable-container-loop.mjs build/noctium-web/
printf '%s\n' '<!doctype html><body><script type="module" src="./readable-container-loop.mjs"></script></body>' \
  > build/noctium-web/container-loop.html
```

Open `/container-loop.html` on that server. The page reports both the valid
result and the rejection.

The [hosted fixture](../../tests/ReadableIteration.lean) uses a private seed and
two-byte witness, maps a provider over the bytes, then folds the results with a
public offset. Its [Compact oracle](../../tests/compact/ReadableIteration.compact)
with [runner](../../tests/compact/readable-iteration.mjs) uses the same inputs,
disclosure and ledger write. The Rust host and Compact 0.36.1 agree on seed,
byte-vector, visit 4, visit 5, followed by result and ledger total 31. The
pinned ZKIR 3.2.1 checker accepts the Noctium entrypoint. The Lean fixture also
checks that omitting disclosure rejects a private fold at a public output.

## Source construction

The API returns an updated `Helpers.Program` and the resulting `Helpers.Term`. Thread the updated program into subsequent construction, then put the returned term in the caller's body. `scope`, `env` and `span` identify the caller's lexical context. The [complete source example](../../tests/IterationWitness.lean) shows this assembly.

```lean
let (mappedProgram, mapped) ← Iteration.mapWithLimits {} base 0 env {}
  [.ref "values"]
  (.anonymous [{name := "value"}] none [
    .return (some (.binary .add (.ref "value") (.ref "offset")))])

let (foldedProgram, folded) ← Iteration.foldWithLimits {} mappedProgram 0 env {}
  (.native 0) [mapped]
  (.anonymous [{name := "acc"}, {name := "value"}] none [
    .return (some (.binary .add (.ref "acc") (.ref "value")))])
```

`applyWithLimits` applies an operator to ordinary argument expressions. `mapWithLimits` accepts one or more fixed sequence expressions and requires equal lengths. Its operator receives one element from each sequence. `foldWithLimits` accepts an initial value and a list of equal-length sequences. Its operator receives the current accumulator and one element from each sequence. Supported sequences include vectors, vector-compatible tuples, scalar byte strings and checked composite byte layouts. Tuple elements need a common type under the supported subtype rules. Byte elements use the bounded range 0..255. An empty tuple supplies its length. Its element type comes from an explicit parameter or a uniquely matching named helper. An omitted anonymous parameter stays unresolved while the source checker checks the zero-length callback.

Generated wrapper parameters evaluate each complete sequence once. Fold evaluates its initial expression before its sequence expression. Ordered bindings retain operator calls and partial computations. Empty vectors keep their declared element type, so checking the operator does not require indexing a nonexistent element. Existing source, type, parameter, declaration and finite expansion limits apply. Checked layout costs bound result projection expansion before cloning. Zero-field results retain strict evaluation tokens, so binding a Unit or empty aggregate does not discard its assertions or partial computations.

Fold requires the accumulator parameter and result types to match exactly. The initial expression accepts a narrower compatible type. Map results use checked scalar, Unit, tuple, record, nested vector, byte and enum layouts. The compiler projects their canonical leaves into the result vector. Enum tag projections return the checked Native variant ordinal. Payload projections run only under their matching tag, and shorter variants retain canonical zero padding. Nested enum payloads use the same rule. Unit parameters and captures retain their logical argument positions while contributing zero native fields. Additional sequence forms need further implementation. Anonymous operators support ordinary structured statement bodies, including their own returns. Public effects and outputs still require explicit disclosure of private values and controlling conditions.

Tuple sequence elements join field by field. For example, `(UInt(maximum=3), Native)` and `(Native, UInt(maximum=3))` share `(Native, Native)`. Tuples must have equal arity and vectors equal length. UInt fields widen to a larger UInt bound or Native. Bool, byte lengths and nominal record/enum identities stay exact. The same rules apply to helper arguments and inferred anonymous returns. Generated host plans contain explicit checked aggregate casts, so expressions still evaluate once.

Reading `.enumTag` returns the tag as data. `disclose` around this projection authorizes release of the tag value. The payload stays private. Selecting a variant's payload also depends on its tag, so disclosing only the payload does not release the private tag or earlier private selection conditions.

## Unit arguments

A Unit helper parameter uses a logical parameter plus a `compositeParameters` entry whose type is `.unit`. A root Unit input occupies one `Export.compositeInputs` row with type `.unit`. Typed host plans retain its name, visibility and `Unit` schema. The native circuit receives no placeholder Boolean or field input.

Hosts supply the canonical value `{"kind":"unit"}`. A missing logical Unit argument still rejects. Unit-valued argument expressions retain strict evaluation, including failing computations, even though their value has no data fields. Anonymous captures and generic specializations use the same representation.

## Focused execution evidence

The [native case](../../runtime/src/witness_execution/iteration_ledger_tests.rs) consumes artifacts generated from `IterationWitness.lean`. Its expected provider order is:

1. `touch` returns Unit. The caller binds this value, passes it to an anonymous operator and captures it in map.
2. `seed` returns 0 after the Unit argument evaluates.
3. `values` returns the private tuple of pairs `[(1,0),(1,1),(1,2)]` once. The pairs mix UInt and Native fields in different positions. Their common element type is `(Native, Native)`. Map sums each pair to 1, 2 and 3 before adding the captured offset.
4. Three `double` calls receive 3, 4 and 5 after adding captured private offset 2. They return 6, 8 and 10.

Each mapped record contains an enum amount and a nested two-element metadata vector. The middle input produces the empty amount variant. The other two contain amounts 6 and 10. Fold reads each enum tag and conditionally projects the active payload alongside byte fees `[1,2,3]`. The two-sequence fold sums the amounts and fees to 22. The source asserts the expected result, explicitly discloses the public cell write and stages private value 22. The entrypoint returns an `Iteration.Receipt` record containing the total, a Bool vector, an enum claim, bytes, nested Unit and an explicitly released private offset. Eight Native return fields form one committed SDK result. The inactive branch makes no provider calls and returns total 0 with the empty claim variant. The offset release remains explicit on both paths. A wrong provider value rejects before the write and private stage. Completed paths run through the native checker. Source rejections remove the write disclosure or the returned offset disclosure and check the private value is rejected at each public sink. Reordered return-view fields also reject.

This example uses staged Lean source construction with explicit Helpers statements. Generic operator preservation remains open under [issue 48](https://github.com/awjreynolds/noctium/issues/48). Source and native checker cases do not establish full Compact equivalence or whole-compiler preservation. A conservative closure pass omits unused bindings only when their value and creation guard are total in the checked Native context. Partial and unknown expressions retain their order and guard totalization. At the [record-only checkpoint](https://github.com/awjreynolds/noctium/commit/02beefa6f7a2352b00387f04fc6ed931b34f3b86), the Impact plan fell from 25,167,866 to 3,309,220 bytes and ZKIR occupied 15,583 bytes. The current example also exercises Unit arguments, captures and a logical Unit root input. The native test rejects omission of that root input and checks its empty native binding list. The current nested-enum export occupies 231,506 bytes for Impact and 27,386 bytes for ZKIR. The native case passes in 0.06 seconds, excluding compilation. The workload now includes a committed composite receipt and nested tuple inputs with explicit structural widening, so these sizes do not form a matched optimisation comparison. Redundant total-value forcing is omitted, while explicit constraints and partial checks remain. Raw composite witness field bounds are unconditional circuit input requirements, including inactive defaults. These are artifact sizes, without a proof-time or K claim. Broader expression sharing stays in [optimisation issue 85](https://github.com/awjreynolds/noctium/issues/85). No keys, proofs, deployments or new K benchmark accompany this extension.

### Empty tuple inputs

The source checker accepts an unresolved parameter in a typed return, binding
or helper argument. Arithmetic and Boolean conditions require an operand type.
A callback with a known result infers the empty vector element type. When the
result is still unresolved, pass `expectedElement` to the staged `mapWithLimits`
API from the surrounding result type. For example, `some (.scalar .native)`
chooses `Vector 0 Native` for the unannotated identity callback. A fold with
an explicit result type uses that type for an omitted accumulator annotation.

The [empty-tuple fixture](../../tests/EmptyTupleIteration.lean) folds over the result
of an empty map and another empty tuple, with omitted callback parameter types.
The Rust host asks for the seed first,
then for tuple inputs 1, 2 and 3. The result and the ledger cell both equal the
seed. Both operator callbacks remain uncalled. The [Compact 0.36.1 oracle](../../tests/compact/EmptyTupleIteration.compact)
with [Compact runtime 0.21.0](../../tests/compact/empty-tuple-iteration.mjs) produces the same
call order, result and ledger value for seed 9.

```sh
lake build noctium Noctium:shared
mkdir -p build/experiments
scratch=$(mktemp -d "$PWD/build/experiments/empty-tuple.XXXXXX")
trap 'rm -rf -- "$scratch"' EXIT
.lake/build/bin/noctium compile tests/EmptyTupleIteration.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --emit witness --output "$scratch/contract"
NOCTIUM_EMPTY_TUPLE_ARTIFACTS="$scratch/contract" \
  cargo +1.100.0 test --manifest-path runtime/Cargo.toml --locked \
    --no-default-features --features zkir-321 --lib \
    empty_tuple_iteration_evaluates_arguments_without_invoking_operators -- --ignored
```

To run the oracle in the same scratch directory, use Compact 0.36.1 and make
`@midnight-ntwrk/compact-runtime` 0.21.0 available to Node.

```sh
compactc --skip-zk tests/compact/EmptyTupleIteration.compact "$scratch/compact"
cp tests/compact/empty-tuple-iteration.mjs "$scratch/"
node "$scratch/empty-tuple-iteration.mjs"
```
