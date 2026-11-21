# Native Counter storage and operations

Noctium Counter state uses the pinned ledger's `Cell(u64)` encoding. Its FAB
alignment is one eight-byte atom, not the Field alignment used by ordinary
`UInt 64` cells. Source values read from counters retain the UInt64 range.

The source forms are `counter total`, `tree epochs : Bytes32 => Counter`, and
`tree epochs : Bytes32 => Bytes32 => Counter`. Existing `read ... as` binds the
value. `increment ... by amount` and `decrement ... by amount` accept a UInt16
expression or a numeric literal through the native u32 limit. A private amount
needs explicit disclosure, as in `increment total by disclose(amount)`.
`reset ...` writes zero. Missing parent maps require explicit
initialization. A reset initializes an absent counter leaf or replaces an
existing value. Contracts decide whether to expose reset to callers.

`counterLessThan path against limit as below` binds a Bool from the native VM. The threshold has type `UInt 64`, and equality returns `false`. The same syntax works on a standalone Counter or a nested path. Under `when`, an inactive comparison returns `false` without reading the path or evaluating the threshold. Active comparisons require an existing Counter with the ledger's Bytes8 alignment. Disclose private values before using them in the path, threshold or public activity guard.

Updates use native `Idx(push_path)`, one `Addi` or `Subi`, then `Ins`. The
relation binds the evaluated amount in the immediate operand. Updates do not
bind the previous value as a circuit read unless the source requests a read.
The native VM rejects u64 overflow and underflow. A false guard skips path
lookup and amount evaluation.

`tests/NativeCounter.lean` and `runtime/tests/native_counter.rs` provide the
focused source/native example. It exercises standalone and nested counters,
reads after updates, reset, inactive guards, checked arithmetic and rejection
of field-aligned state supplied as a Counter. The fixture exposes test-only
update/reset entrypoints and establishes no token authorization policy.

[CounterAmounts.lean](../../tests/CounterAmounts.lean) and its
[native checker case](../../runtime/tests/counter_amounts.rs) exercise
expression amounts in both directions. The
[Compact 0.36.1 oracle](../../tests/compact/counter-amounts.mjs) checks
the same accepted amounts and state transitions with the pinned runtime.

The pinned recipes are
[Counter operations](https://github.com/midnightntwrk/midnight-ledger/blob/a2b30128ca4b660b73a068e29b56b48ede8c9a74/onchain-runtime/vendored/program_fragments.rs#L158-L217).
Counter uses eight-byte alignment in
[FAB alignments](https://github.com/midnightntwrk/midnight-ledger/blob/a2b30128ca4b660b73a068e29b56b48ede8c9a74/base-crypto/src/fab/alignments.rs#L73-L81).
## Strict comparison conformance

The comparison uses the pinned `Counter_less_than` opcode sequence and sees updates earlier in the entrypoint. Compact 0.36.1 and the native checker agree for thresholds 299, 300, 301 and UInt64 maximum on standalone and nested counters. The native checker also tests equality against an actual UInt64-maximum counter and rejects malformed storage alignment. [Lean source](../../tests/CounterCompare.lean) · [Compact oracle](../../tests/compact/counter-compare.mjs) · [Native checker](../../runtime/tests/counter_compare.rs)

Ledger 9.1.0.1 finalized the standalone comparison at block 48864 and the nested comparison at block 48870 after seeding its path. Both final counters held 300. The nested read left the finalized state bytes unchanged. An active call on the unseeded path rejected during preparation and preserved its admitted state token. [Funded receipt](native-counter-compare-localnet-receipt.json)

Compile the fixture with `--emit ledger` and the ZKIR 3.2.1 target. Prepare the authenticated `inspect`, `seedNested` and `inspectNested` bundles under a single directory and pass their manifest digests as a JSON object keyed by entrypoint name. Run the test on the funded isolated development chain. [Bundle assembly](portable-artifacts.md)

```sh
NOCTIUM_COUNTER_COMPARE_BUNDLES=PATH_TO_BUNDLES \
NOCTIUM_COUNTER_COMPARE_MANIFESTS=JSON_OF_THREE_MANIFEST_DIGESTS \
NOCTIUM_COUNTER_COMPARE_PARAMETER_CACHE=PATH_TO_TRUSTED_PARAMETER_CACHE \
NOCTIUM_COUNTER_COMPARE_NODE=http://127.0.0.1:19944 \
  cargo +1.100.0 test --locked --manifest-path runtime/Cargo.toml --lib \
  --no-default-features --features zkir-321,localnet \
  counter_comparison_finalizes_on_ledger -- --ignored --nocapture
```

[Native-field memo Lists](native-lists.md) have a separate source/native example.
