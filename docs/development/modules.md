# Lean module identity and views

`Noctium.Modules` provides the bounded compile-time core for Noctium module
composition. Registration receives the full Lean `Name` for each source
module. A user-facing alias or import path does not replace that identity.

An instance key contains the source `Name` and its ordered normalized type or
natural arguments. Equal keys share one expansion. Different source names or
arguments produce distinct member identities, even when their runtime shapes
match. Re-exports and selective imports hold references to the original member
identity. They do not copy state fields or grant access to private members.

The expansion API accepts a registry of pure module definitions:

```lean
import Noctium.Modules
open Noctium.Modules

private def registry : Registry := ...
def result := expand registry `Demo.Entry []
```

Definitions list source members, imports, selections, and exports. Each member
has a registration ordinal, source name, kind, visibility, and source span.
Imports name the exact target module identity and may pass concrete normalized
arguments or forward parameters declared by the importing module. Exports may
reference local public members or selected names from imported views.

A circuit or witness member may carry a `SourceExportRef`, which points to an
original generic helper program constant, export name, and ordered arguments.
Expansion resolves module parameters into a `ResolvedSourceExport`. A view
stores only the member identity, so compiler checks and typed witness signature
metadata continue to resolve through the original source constant.

Modules with ledger behavior also declare typed state members and entrypoint
templates. A template points to a circuit member and uses `StateTarget` values
for reads and writes. Expansion resolves those references through the module's
own members or selected import views. `Expansion.contractPlan` deduplicates
state by full member identity, assigns canonical field names, resolves entry
aliases, and groups helper requests by exact source program. The frontend then
specializes each group with the issue46 batch session, checks the concrete
program, attaches the compiled circuits, and validates an ordinary
`Noctium.Contract`.

State schemas support fixed scalar types, type parameters that specialize to a
scalar, and unsigned bounds supplied by natural parameters. Expansion resolves
the schema for each exact module key before checking effects. Aggregate state
types fail with a source diagnostic. `writeCellOutput` takes its type from the
resolved cell and names a circuit output; ordinary contract validation checks
that output's type against the selected circuit.

The expansion checks module arity and argument kinds, unknown modules and
exports, private-member exports, duplicate source identities, import cycles,
and configurable work limits. It charges instance and node budgets before
expanding a module. It bounds normalized type nodes before canonical key
encoding. Canonical keys encode `Name` constructors, component and argument
boundaries, full normalized types, and decimal natural values. A fixed digest
provides stable field names. The expansion retains each exact structural key
and rejects digest collisions before producing output. Digests are identifiers,
not cryptographic authority.

`Expansion.stateFieldName` derives a field name from the originating module
instance and member ordinal. An alias view returns the same field name as the
source member. `resolveImport` and `resolveExport` return references with the
same source identity, so visibility and disclosure analysis can keep using the
original member metadata.

This module is the pure expansion layer. Frontend and compiler registration
must re-expand the registered root and use fresh concrete specialized helper
programs, source spans, disclosure origins, and typed witness signature
metadata during compilation. The issue46 batch session ensures export order
does not affect generated identities. General cross-contract calls are
separate issue50 work. Runtime execution of general typed witness functions is
issue62 and is not provided by module expansion.

## Jubjub circuit specialization

Supply `.typeValue (.scalar .jubjubScalar)` or
`.typeValue (.scalar .jubjubPoint)` when importing a generic circuit member.
They resolve to distinct instances and retain their public input and output
types in the emitted native relations. The fixture imports both versions of
one identity circuit and stores each result in a fixed, typed Cell. Generic
ledger state type substitution is a separate scope.
[Lean fixture](../../tests/modules/JubjubGenericIdentity.lean) · [Compact comparison](../../tests/compact/generic-jubjub-module.mjs)

## Generic record Cells

Pass a declared record as `.checkedTypeValue value environment` when selecting
a generic module with `stateSchema? := some (.cell (.parameter "T"))`. Its
reachable type declarations determine the checked ledger layout. Bind
constructor inputs by field name with `recordFields`. The module stores one
record Cell and returns it as a typed record. A guarded write requires
disclosure for private values used as payload or guard.

For a whole-record write, declare the helper input as `next : T` and use
`.writeRecordCellInput target "next" (disclosed := Bool.true)`. The module
checks the specialized argument against the Cell's exact layout, then adds
the grouped header fields in layout order. List separate scalar arguments
such as an update guard in `callInputs`.
[Lean fixture](../../tests/modules/GenericRecordCell.lean) · [Compact comparison](../../tests/compact/generic-record-cell.mjs)

## Import exported types

Select the source member in your module definition, then bind the selected
name for your circuit. This example reads `LocalPacket` from the `selected`
view of the requested module.

```lean
noctium_module_type LocalPacket from importedModuleTypesRequest with "selected", "LocalPacket"

def packetWire : Noctium.Helpers.Wire.Codec := {
  payload := LocalPacket.value
  composites := LocalPacket.environment
  frameBytes := 33}
```

Use `Payload packetWire` for the aggregate input. The imported environment
contains the checked declarations reachable from the selected type. Aliases
and re-exports retain the originating identity. Instantiating the generic
record at another type gives a distinct type. An imported nominal UInt also
binds its local name for scalar circuit signatures, with the original UInt
identity and bound. Private and unselected types are unavailable through
the view.
[Lean fixture](../../tests/modules/ImportedModuleTypes.lean) · [Compact comparison](../../tests/compact/module-type-exports.mjs)

## Focused checks

Run the pure expansion cases and deterministic source CLI fixture with:

```sh
bash tests/modules/check.sh
```

`tests/Modules.lean` covers structural source identity, alias and re-export
identity, same-key cache reuse, distinct generic instances, nested argument
forwarding, kind and arity rejection, private visibility, import cycles, and
instance/type-node limits. It also exercises the issue46 batch specialization
API, which processes one selected export set in sorted name order while sharing
its helper and type caches.

An ordinary circuit defined in another Lean module can serve as a contract
entrypoint. Use the circuit's qualified name in `entry ... uses ...`.
The compiler emits the selected circuit and applies its normal target and
disclosure checks. The CLI fixture compares the entrypoint's ZKIR 3.2.1 bytes
against the same definition in one file. Imported artifacts retain the existing
unqualified metadata for source provenance. [CLI fixture](../../tests/cli.sh)

The [native module fixture](../../tests/modules/Native.lean) specializes a
helper and state with a natural and scalar type argument. Two update aliases
for `(2, Native)` share the same circuit and field. The `againRead` entrypoint
reads the shared field through the locally renamed `mirror` view and checks
the read against its public input. The `(3, UIntRange<256>)` instance uses a
different circuit and field.

The [module CLI check](../../tests/modules/check.sh) builds the fixture as one
source file and then imports the same library from a separate Lean module.
Both builds emit identical ZKIR, Impact and metadata bytes for the pinned
3.2.1 profile. The check also makes the generic helper input private and
verifies re-exporting its result still fails disclosure before emission.

Compact 0.36.1 and its 0.21.0 runtime agree on the two aliases observing one
balance. The oracle accepts the read at 11 after the first alias writes 11.
It ends with shared balance 23 and distinct balance 7, and rejects a stale
read at 22. [Compact oracle](../../tests/compact/ModuleLedger.compact) · [Runner](../../tests/compact/module-ledger.mjs)

On the funded Ledger 9 development localnet, deployment finalized at block 70.
The two alias writes and the read through `mirror` finalized at blocks 73,
76, and 79. The distinct specialization finalized at block 82 with its own
balance of 7 and the shared balance still 23. Both update aliases used the
same circuit and verifier key. The SDK rejected a proof bound to the wrong
alias and rejected the stale read before proving.
[Finalized receipts and artifact hashes](module-ledger-localnet-receipts.json)

The linked C++ client executed the same sequence on Ledger 9 with identical
ZKIR, Impact plans and verifier keys. It recovered the original signed
`firstUpdate` after a process restart. All five finalized state digests
matched the Rust run.
[C++ receipts and artifact hashes](module-ledger-cpp-localnet-receipts.json)

The compiler re-expands each module contract from its registered source
constants during inspection. It then re-runs generic specialization,
component disclosure, witness compilation, and contract validation. Cached
generated constants provide stable source names, while fresh output supplies
the program, circuit, contract, witness, and signature data used by compilation.
