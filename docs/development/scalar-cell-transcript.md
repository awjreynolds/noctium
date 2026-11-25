# Scalar cell transcript qualification

[ScalarCellTranscript](../../examples/ScalarCellTranscript.lean) reads a UInt16
cell, adds a public UInt8 delta, writes the result, reads it back, and returns
the second read. The call has three source effects and 11 native Impact
operations. It uses the selected Ledger 9 and ZKIR 3.2.1 target.

The [Lean artifact proof](../../Noctium/Verification/ScalarCellArtifactExecution.lean)
connects checked artifact bytes to the source execution for the admitted
unguarded scalar-cell fragment. The following exercise separately checks
an emitted circuit with Midnight's official checker.

## Run the checker

Build the compiler, then emit a standalone set of ledger artifacts into a
disposable directory. Supply the verified 3.2.1 checker JavaScript module and
the Ledger V9 1.0.2 JavaScript module pinned in the
[conformance lockfile](../../scripts/zkir/package-lock.json).
The [3.2.1 qualification](zkir-3.2.1-qualification.md#upstream-identity) records
the official checker tarball and SHA-256.

```sh
lake build noctium
scratch="$(mktemp -d)"
out="$scratch/ledger"
.lake/build/bin/noctium compile examples/ScalarCellTranscript.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --output "$out"
node tests/scalars/check-scalar-cell-transcript.mjs \
  "$out/ScalarCellTranscript.apply.zkir" "$CHECKER_MODULE" "$LEDGER_V9_MODULE"
```

The harness uses the Ledger API to construct a commitment to the return value.
The official checker accepts total 10 plus delta 3 with an observed return of
13. Changing only the first read from 10 to 11 fails public transcript input
binding. Changing only the second read from 13 to 14 fails the return
commitment. These cases exercise the emitted relation directly.

## Funded development ledger

Use the [native Rust assembler](native-assembler.md) and the
[isolated localnet runner](../../scripts/localnet/README.md) with target
`midnight-ledger-9-zkir-3.2.1`. The circuit has k=7 and 94 rows in the
pinned native mock compiler. The funded fixture uses initial total 65,522
and delta 13. Include a negative input with delta 256.

The deployment finalized at block 386 and the call at block 389. The fetched
state decoded to 65,535 and matched the native prediction byte for byte.
Executing the same source in Lean returned 65,535 and produced the same
cell value. A fresh call with the same delta after the accepted write
rejected at the UInt16 boundary. The harness checked the rejection against
fetched state and left that state unchanged. It submitted no duplicate
signed transaction.

[Recorded checker and ledger evidence](../../tests/scalars/scalar-cell-transcript-evidence.json)
includes the source and artifact digests, verifier digest, and finalized
receipts.
