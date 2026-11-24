# Native Lists

Noctium lowers Lists of scalars and checked ledger records directly to the pinned
ledger VM. A node is `Array[Cell(record), tail, Cell(length)]`. The empty value
is `Array[Null, Null, Cell(0u64)]`. Length uses the ledger's eight-byte u64 FAB
alignment. Record fields retain their declared order and storage types.
A `Native` field occupies one Field atom, a `Bytes32` field one 32-byte atom,
and a `JubjubPoint` field two Field atoms holding the checked x/y coordinates.

`tests/NativeList.lean` declares a standalone `list inbox : struct Memo {...}`
and a two-key `tree memos : Bytes32 => Bytes32 => List struct Memo {...}`.
For scalar Lists, declare `list values : Native` or
`tree memos : Bytes32 => List Bytes 128`. A scalar head binds one value
under the requested name. The native codec preserves the value's alignment.
A 128-byte element uses one Bytes128 atom and five transcript fields.

The source operations are:

- `reset path` initializes or clears a List. Parent maps need explicit creation.
- `length path as count` binds a UInt64 value.
- `isEmpty path as empty` binds a Bool from the ordered length read.
- `head path as memo` binds the checked record fields, such as `memo_x`.
- `headOrDefault path as (present, memo)` binds a Bool and the same record fields. An empty List returns `false` with typed defaults. Every present record returns `true`.
- `pushFront path := value` prepends a scalar. Use
  `pushFront path := fields(...)` for a named record.
- `popFront path` replaces the selected List with its tail.

Strict `head` rejects an empty List. `headOrDefault` reads the native length
and guards the head read with the nonempty result. Noctium binds both reads to
the ordered ledger state. An inactive statement returns `false` and typed
defaults without looking up its path. A missing active path still rejects.

An active pop of an initialized empty List writes native `Null` to the
selected slot or Map entry. Typed reads reject that value. Use `reset` to
restore the empty List node.

Each List effect emits one guarded native sequence. Each VM opcode retains its
own activity entry, with the same source guard across the sequence. An inactive operation skips
its path lookup and payload evaluation. Inactive head reads bind zero for
`Native` and `Bytes32` and the identity `(0, 1)` for `JubjubPoint`. An inactive
length read binds zero. Reads after writes use the ordered native
state prefix. Nested paths preserve other owners and spenders. A List permits
at most 13 map keys because prepend needs an additional native insertion level.
The three-slot node shape does not impose a three-element List limit.

Ledger Lists are public state. Ciphertext-shaped records still require explicit
field disclosure at writes. Storing encrypted fields does not by itself prove
correct encryption, key ownership, or a privacy policy. This storage layer
reuses the record schemas needed by the confidential-token memo workload.

The focused source/native example is `tests/NativeList.lean` plus
`runtime/tests/native_list.rs`. It covers prepend order, reads, removal, reset,
separate nested paths, inactive guards, exact storage alignment, empty pop
and rejection of malformed record payloads. The emitted program also checks
that an active pop through an absent nested path rejects.

The recipes follow the pinned ledger's
[List fragments](https://github.com/midnightntwrk/midnight-ledger/blob/a2b30128ca4b660b73a068e29b56b48ede8c9a74/onchain-runtime/vendored/program_fragments.rs#L434-L527)
and [StateValue field encoding](https://github.com/midnightntwrk/midnight-ledger/blob/a2b30128ca4b660b73a068e29b56b48ede8c9a74/onchain-state/src/state.rs#L401-L435).
The compiler emits uncached native operations for pop.

[OptionalListHead.lean](../../tests/OptionalListHead.lean) checks the optional form on standalone and nested paths. [MixedLedgerRecord.lean](../../tests/MixedLedgerRecord.lean) uses the same memo shape in map cells and List nodes. `fields(...)` takes one typed expression per declared field. Reads bind names such as `memo_payload` and `memo_ephemeral` with their declared types.

[NativeScalarList.lean](../../tests/NativeScalarList.lean) and its
[native checker case](../../runtime/tests/native_scalar_list.rs) exercise
standalone Native and nested Bytes128 Lists. The
[Compact 0.36.1 oracle](../../tests/compact/native-scalar-list.mjs)
checks the corresponding empty, prepend, pop and reset transitions.

Pinned Compact 0.36.1 and Runtime 0.21.0 agree with the Noctium source
interpreter and emitted ZKIR 3.2.1 case. An active pop writes `Null` to an
empty root List or selected Map entry. A subsequent head read fails. An
inactive pop through an absent parent leaves the state unchanged. An
active pop from a populated List removes one item. [Compact case and state assertions](../../tests/compact/list-pop-front.mjs)

The pinned Ledger 9 `List_pop_front!` fragment independently produces the
same `Null` at an empty root or selected Map entry when run directly in
`QueryContext`. Siblings stay intact. A missing Map key causes the query to
fail. This evidence covers the native VM fragment and the selected state
paths. [Pinned fragment](https://github.com/midnightntwrk/midnight-ledger/blob/a2b30128ca4b660b73a068e29b56b48ede8c9a74/onchain-runtime/vendored/program_fragments.rs#L497) ·
[Native VM check](../../runtime/tests/native_scalar_list.rs)

The [pinned Compact `Maybe` oracle](../../tests/compact/ListHeadMaybe.compact)
and [runner](../../tests/compact/list-head-maybe.mjs) check `head()` on
`List<Uint<8>>`: an empty List returns `is_some = false, value = 0`, and a
List after pushing `37` returns `is_some = true, value = 37`. The runner
requires Compact 0.36.1 and `@midnight-ntwrk/compact-runtime` 0.21.0, and
accepts their local paths as arguments:

```sh
node tests/compact/list-head-maybe.mjs <compactc-0.36.1> <compact-runtime-0.21.0>
```

[`NativeScalarListMaybe.lean`](../../tests/NativeScalarListMaybe.lean)
uses `headOrDefault values as (present, payload)` followed by
`returnMaybe head as (present, payload)`. The native checker accepted the
fresh 3.2.1 circuits for both cases and returned one structured value with
the Boolean tag first and the UInt8 payload second. An absent result carries
the canonical zero payload. [Native checker](../../runtime/tests/scalar_list_maybe.rs)

```sh
lake exe noctium compile tests/NativeScalarListMaybe.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --output build/scalar-list-maybe
NOCTIUM_SCALAR_LIST_MAYBE_DIR="$PWD/build/scalar-list-maybe" \
  cargo test --locked --manifest-path runtime/Cargo.toml \
  --no-default-features --features zkir-321 --test scalar_list_maybe -- --ignored
```

[RecordListHeadMaybe.lean](../../tests/RecordListHeadMaybe.lean) uses the
same source form for a record with Native fields. The return keeps the
List element's nominal type and orders the tag before the record fields.
The paired fixture checks an empty List and a List seeded with `{17, 23}`.
[Compact runner](../../tests/compact/record-list-head-maybe.mjs) · [Native checker](../../runtime/tests/record_list_head_maybe.rs)

## Check emptiness for zero-width and nested record Lists

The paired fixture compares an empty `List<Bytes<0>>` with a List containing
one zero-width item. It also compares empty and populated record Lists beneath
two Map keys. The active read through an absent parent rejects in Compact and
native preflight. A disabled guard skips the path and returns false.

The development deployment finalized at height 85346 and seeded both layouts
at 85349. The K10 inspection relation has 712 rows. The finalized inspection
at 85352 matched all five Boolean returns and preserved the exact seeded state
bytes. [Lean fixture](../../tests/ListIsEmptyParity.lean) ·
[Compact oracle](../../tests/compact/list-isempty-parity.mjs) ·
[Finalized receipt](list-isempty-localnet-receipt.json)
