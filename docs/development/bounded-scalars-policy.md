# BoundedScalars policy replay

`BoundedScalars.apply` starts with a public `total` cell of zero. The public
`expected` input and `total` range from 0 to 510, inclusive. The private
`left` and `right` operands range from 0 to 255, inclusive. An enabled call
requires the operands to sum to `expected` and the prior total to be zero.
An accepted call writes the sum to `total`, the only ledger cell. The source
circuit produces `result` for the write. The entrypoint declares no committed
call returns.

| Case from total zero | Expected | Left | Right | Scoped result |
| --- | ---: | ---: | ---: | --- |
| Maximum bounded sum | 510 | 255 | 255 | Source and native accept. The new total is 510. |
| Incorrect expected value | 509 | 255 | 255 | The source circuit and native checker reject. Native preparation reaches the checker from total zero. |
| Impossible enabled predicate | 510 | 255 | 255 | The source policy has no reachable enabled call. |

The last row replaces only the enabled predicate of the source specification
with an always-false predicate. The reachability condition asks for an initial
state and inputs satisfying both the precondition and the enabled predicate.
The first row supplies a concrete witness to that condition and checks the
actual source run against the registered postcondition. The mutated policy
fails the same reachability condition for every candidate. The control leaves
the source contract and registered theorem unchanged.

The registered policy and proof names are
`Noctium.BoundedScalarsVerification.policy`, `functional` and `privacy`
under the same namespace. The [Foundation source profile](../../profiles/foundation-source-v1.json)
pins the `bounded-scalars-source-audit-v1` report kind and its reviewed model
SHA-256 `f570ba99a309ae2dd26d532a01ed38e98e2336c910e0fe634398cab0ae33c25e`.
The registered functional theorem covers canonical source inputs and states.
The source privacy theorem compares successful outcomes under the pinned
precondition, with equal public input, initial state and evaluation context.
The public ledger update releases the sum already supplied as `expected`.

The native replay uses the pinned Ledger 9.1.0.1 and ZKIR 3.2.1 profile with
locally initialized state and synthetic operands. The native evidence covers
Impact preparation, the ZKIR checker and the decoded state for these vectors.
Universal source-to-native agreement, proof creation, finalized ledger
execution and privacy of rejected calls require separate evidence.

## Reproduce

Run from the repository root with pinned Lean and Rust toolchains.

```sh
(
  set -eu
  mkdir -p build/experiments
  scratch=$(mktemp -d "$PWD/build/experiments/bounded-scalars-policy.XXXXXX")
  trap 'rm -rf "$scratch"' EXIT
  mkdir -p "$scratch/imports/examples" "$scratch/imports/proofs"
  export LEAN_PATH="$scratch/imports"
  lake build Noctium.Cli Noctium.Compiler Noctium.Frontend Noctium.Verification
  lake env lean -D Elab.async=false -o "$LEAN_PATH/examples/BoundedScalars.olean" \
    examples/BoundedScalars.lean
  lake env lean -D Elab.async=false -o "$LEAN_PATH/proofs/BoundedScalarsVerification.olean" \
    proofs/BoundedScalarsVerification.lean
  lake env lean tests/scalars/BoundedScalarsPolicy.lean
  lake env lean --run NoctiumMain.lean compile examples/BoundedScalars.lean \
    --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
    --emit ledger --output "$scratch/native"
  NOCTIUM_BOUNDED_SCALARS_REPLAY_DIR="$scratch/native" \
    cargo +1.100.0 test --locked --manifest-path runtime/Cargo.toml \
      --no-default-features --features zkir-321 --test bounded_scalars_replay \
      -- --ignored --nocapture
)
```

The separate [Foundation profile replay](../../scripts/proofs/replay-foundation-source-profile.sh)
checks the pinned source reports and their artifact associations. The reviewed
BoundedScalars model digest matches its original source revision. The current
model export fails the digest check, and the current proof export fails
against the original model. Both failures reproduce on the base revision.
[Pin regression #1414](https://github.com/awjreynolds/noctium/issues/1414)

The [state-guard replay](native-unsigned-scalars.md#repeated-call-state-guard)
covers a valid sum rejected after a nonzero write.
