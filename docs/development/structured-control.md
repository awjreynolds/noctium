# Structured host control

Issue 42 adds lazy expressions, conditional statements and short-circuit
operators to the typed helper source model. Portable host execution uses the
Rust continuation machine and a separate C ABI. Node is unnecessary for source
compilation, callback execution and the C++ adapter.

The [native helper route](native-helper-branches.md) now lowers witness-free
branches and lazy expressions, with results usable by guarded contract effects.
General structured witness/state effects and their complete proof/ledger path
remain under CF-02. The old eager scalar `select` keeps its existing semantics. Host
execution establishes no theorem about native guarded proof soundness.

## Readable witness conditionals

In a `noctium_witness_circuit`, `if … then … else …` and `ite(condition, yes, no)`
choose one arm. Both arms must have a common checked type. In this example
`loadLeft` and `loadRight` return the same declared payload type.

```lean
let selected := if choice then
  let value := witness loadLeft() in value
else
  let value := witness loadRight() in value
output amount : Native := disclose(field(selected, amount))
```

Only the selected provider runs. The compiler keeps each arm's local bindings
and assertions under its guard. It tracks disclosure on each selected component
and carries private control dependencies into the result. The focused source and
Rust tests check both arms, inactive callback suppression, and rejection of a
failed selected assertion on the host and in the native ZKIR 3.2.1 checker.
Guard-aware recording and replay proofs remain outside this checked slice.

### Short-circuit Boolean expressions

`andThen(left, right)` evaluates the right operand only when the left operand
is true. `orElse(left, right)` evaluates it only when the left operand is false.
Both operands require Bool. Any local bindings, witnesses and assertions in
the right operand stay under its guard. Private values and control dependencies
still require disclosure at public outputs.

The native fixture covers both callback paths and rejects a failed active
assertion. [Lean source](../../tests/ReadableLazyConditional.lean) · [Rust check](../../runtime/tests/readable_lazy_conditional.rs)

### Scoped statements

Use a statement block for branch-local bindings, assertions and witnesses.

```lean
if choice then
  let selected := witness loadLeft()
  prove eq(field(selected, amount), expected)
else
  let selected := witness loadRight()
  prove eq(field(selected, amount), expected)
end
witness afterChoice(expected)
```

Each arm has its own bindings. Both arms type-check and only the selected arm
runs. The compiler lowers the branch as a Unit helper so the following
witness has one unconditional call site. A failed active assertion stops
execution before that call. An omitted `else` has an empty body.

## Bounded native write guards

Issue 43 now has a narrow source-to-checker slice for scalar state writes:

```lean
when disclose(enabled) write balance := nextBalance
when disclose(enabled) insert allowances[account] := amount
```

The compiler binds each write's Impact groups to the source guard. A private
guard must be disclosed because the active update changes the public ledger
transcript. The selected ZKIR 3.2.1 native checker accepts both active and
inactive cases and checks the full activity vector. The Rust materializer skips
inactive payload evaluation and state changes.

This slice supports guarded scalar cell and map writes, guarded scalar cell,
map-value and membership reads, plus unguarded map membership reads:

```lean
member balances[account] as present
when disclose(eq(present, false)) insert balances[account] := amount
```

The materializer gathers membership from the native `Member` opcode after the
ordered write prefix. An inactive guarded read binds its canonical zero or
false value without evaluating its map key or touching a missing path. ZKIR
uses the source guard on the read input and asserts that an inactive read equals
its default. The selected-321 checks live in
`tests/Issue43ConditionalWrites.lean` and
`runtime/tests/conditional_writes.rs`, and in
`tests/Issue43MapMembership.lean` and `runtime/tests/map_membership.rs`, plus
`tests/Issue43GuardedReads.lean` and `runtime/tests/guarded_reads.rs`.

Guarded writes and `require` also support partial scalar expressions. Inactive
unsigned subtraction, narrowing casts and inline `assertThen` use safe native
defaults. Active expressions retain their original rejection behavior. The
compiler captures activity under a fresh name before transforming nested
`let` expressions, so local shadowing preserves the original guard. Disclosure
checks still run on the original source value and control.

```lean
when disclose(enabled) write quota := disclose(sub(left, right))
when disclose(enabled) require assertThen(approved, true)
```

One focused native test covers inactive failures, corresponding active
rejections, valid active writes and nested name shadowing. Its source is
`tests/Issue43GuardedPartialWrites.lean`, with native checks in
`runtime/src/proof/guarded_partials.rs`. The test passes the assembled call and
its checked activity through the proof SDK's native statement preview. Lean
checks the resulting public fields against the emitted Impact bytes for both
active and inactive writes. Eager `select` keeps eager evaluation inside an
active expression. Guarded assertions retain the existing successful-value
disclosure scope, without a failure-channel privacy claim.

The selected-3.2.1 inactive conditional-write fixture also passes real native
proof construction and verified attachment. The SDK freezes a preview of native
Noop insertion/merging and gas, then checks actual attachment against that exact
statement. One changed skipped statement field rejects the proof. See the
[native proof API](native-proof-api.md#native-phase-and-statement).
The private-only, all-inactive source case also proves and attaches with zero
original VM operations. Its skipped fields use an empty native transcript
container, without a dummy source input.
The native source surface now accepts nested effect blocks:

```lean
if disclose(enabled) then {
  read balance as current
  write selected := current
} else {
  write selected := 0
}
```

Both arms are checked. Read locals stay inside their branch, and both arms may
reuse the same source name. Nested conditions are totalized under their parent
guard, so an inactive narrowing cast or assertion does not execute. `absent`
queries inside blocks remain unsupported. This package has one selected-3.2.1
native checker fixture at `tests/Issue43EffectBlocks.lean` and
`runtime/tests/effect_blocks.rs`. General `Helpers.Statement.branch` and witness
integration still need their own native path. These checks do not add ledger
deployment evidence.

## Authoring and compilation

Use `Helpers.Term.ite`, `andThen`, `orElse` and `witness`, plus
`Helpers.Statement.branch` and `stage`. A witness names a registered provider
and declares its scalar result type. Staging names an explicit capability,
private-state key and scalar type. The complete working source is
[ControlSource.lean](../../tests/ControlSource.lean).

```lean
open scoped Noctium
noctium_control conditionalProviders from conditionalProvidersProgram
  entry "conditionalProviders"
```

The `noctium_control` command checks the program and creates a registered
portable plan. The ordinary compiler exports this registry separately from
native circuits:

```sh
lake exe noctium compile tests/ControlSource.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --output /private/tmp/noctium-control-source
```

This source emits eleven `.control.json` files. `noctium.json` lists their
filenames under `hostControlPlans` and records `nativeGuardQualified: false`.
Named calls refer to a typed function table. Exporting the plan never duplicates
callee subtrees. Declarations retain lexical identities, overload resolution,
argument order, scalar types and the implementation resource caps from
[named helpers](named-helpers.md).

Both arms receive type checks, even beneath a literal condition. Conditional
expression types require one arm to be a subtype of the other. Statements
allow discarded results with different types. Branch locals stay inside their
branch. A return exits the nearest named function. Purity analysis visits both
arms and the right operand of short-circuit expressions before scheduling.
`FN-PURE-INACTIVE` therefore rejects a declared-pure helper containing a witness
call inside a literal-false branch.

## Scheduling and host protocol

The host evaluates a condition before choosing one arm. `andThen` skips its
right operand after false. `orElse` skips its right operand after true.
Inactive assertions and narrowing casts do not execute or fail. The existing
`select` evaluates the condition and both values in order.

The portable runtime first validates the whole plan, including inactive
branches, function signatures, call cycles and resource limits. Execution uses
an explicit continuation stack. Suspension retains the current continuation.
Resuming a witness never replays earlier callbacks or private writes.

Every declared witness needs a registered provider, including witnesses which
remain inactive during the invocation. Providers use the existing versioned
host context, capability grants and typed schemas. A request binds its id,
operation, capability and scalar result schema. Invalid responses fail without
advancing execution. Cancellation invalidates pending requests and clears the
invocation's value buffers and private journal.

A source `stage` applies the existing host runtime's capability and typed-value
checks. Validated staged writes appear in the private request's
`invocationWrites` overlay for later callbacks. The original store remains
unchanged. Cancellation and failure clear the overlay and staged journal.
The control session exposes no transaction submission, receipt acceptance,
private-state CAS or durable commit operation. External side effects performed
inside arbitrary callback code receive no rollback guarantee.

Ordinary result transport carries host-execution statuses: ready, need-host,
completed, failed or cancelled. Scheduling and request metadata can depend on
private guards and remain visible to the host/controller. These messages are
not safe public contract observations or public logs. DF-00 checks successful
scalar contract-return payloads. It excludes host/provider activity and timing.
Execution errors use the fixed `execution_rejected` code.

Callback arguments, invocation writes and effect traces use separate private
accessors and private token handles. Ordinary result-copy functions reject
private tokens. This channel separation does not hide branch scheduling from
the host/controller.

## Disclosure

`Control.checkDisclosure` invokes the helper type, recursion, purity and hard
resource checks before its constant-aware DF-00 walk. Public inputs start with
no private origins. Private parameters and witness results retain their
origins through arithmetic, casts, hashing and helper calls.

Literal conditions select one arm for disclosure analysis. Unknown conditions
merge the origins of possible returned values. Statement conditions add a
separate accumulated control origin. Nested branches and early returns retain
this origin, including control over whether a later return executes.
Disclosing a returned payload does not release its surrounding statement guard.
Disclose the guard before branching to authorize that control dependence.
Unit returns have no public payload slot. They accept private control when no
public scalar value is returned. Scalar returns retain their control checks.
Assertions keep DF-00's current successful-execution scope. Their failure
behavior is not a general privacy guarantee.

The Rust runtime repeats type validation and checks actual returned origins
and control dependence before completing a successful scalar return. This does not make intermediate
host statuses confidential or safe to publish. These host checks do not
authorize guarded public ledger, event or cross-contract routes. Those routes
still need their source and native backend packages.

## Resource policy

All helper budgets remain immutable upper bounds. `WithLimits` APIs permit
only tighter budgets. Source preflight counts terms and statements in both
arms, including inactive and post-return syntax, before recursive passes.
Call-site multiplicity, memoized summaries, expanded-depth limits and shared
execution fuel remain active. Runtime continuation tasks and bounded abstract
constant/control analysis share the 131,072-step maximum. Abstract analysis
invokes no callbacks, stages no writes and changes no invocation state. The portable plan has a 1 MiB compact JSON limit. Emission reserves a
conservative byte allowance before constructing each node, including six bytes
per UTF-8 metadata byte for JSON escaping. `compileWithLimits` accepts an optional
fourth `maxPlanBytes` argument for tighter tests. Raising this allowance above
1 MiB fails. A minimal Unit plan exercises exact allowance boundaries of
1,072 bytes accepted and 1,071 rejected before construction.
Names and span filenames use at most 1,024 UTF-8 bytes. Lexical identity
components fit unsigned 64-bit integers, and span lines/columns stay at or below
1,000,000,000. These are local implementation caps, not language or ledger limits.
Oversized metadata errors never echo the rejected text. Witness names and stage capabilities/keys additionally
follow the existing host protocol syntax. At most 32 witness providers fit the
current host context. Host request, write and private-byte budgets remain
independent invocation limits.

## Evidence

Run `lake env lean tests/Control.lean` and
`lake env lean tests/ControlSource.lean`. Cases cover both-arm typing, subtype
joins, lazy assertions/casts, short-circuit order, eager-select distinction,
inactive purity, constant/private/nested control, payload-only disclosure,
authorized guards and private early returns. Existing named-helper and resource
boundary tests remain in `tests/Helpers.lean`.

The shared generated fixtures live in
[runtime/tests/fixtures/control](../../runtime/tests/fixtures/control).
The Rust callback driver and
[C++ C ABI driver](../../runtime/tests/control_cpp_smoke.cpp) consume the actual
Lean-generated `conditionalProviders` plan. The inactive case returns 7 with
zero callback invocations and zero staged writes. The active case invokes
`flag`, `left`, then `right`, stages one write between `left` and `right`, and
returns 22. The right callback observes `counter/value = 1` through the private
invocation overlay. Both adapters also reject the shared `activeFailure` plan
with the same fixed error and empty trace, and exercise cancellation.

```sh
cargo +1.100.0 test --manifest-path runtime/Cargo.toml --locked \
  --no-default-features --features zkir-321 --test control
```

Build the matching native library before compiling the C++ smoke program.
Link `runtime/tests/control_cpp_smoke.cpp` against `noctium_runtime`, then pass
`conditionalProviders.control.json` and `activeFailure.control.json` as the two
arguments. The public ABI is documented in
[noctium_control.h](../../runtime/include/noctium_control.h). Fixture
callbacks and their values are public synthetic test data. Production callback
registrations and private inputs stay under the embedding host's control.
