#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
experiments="$repo_root/build/experiments"
mkdir -p "$experiments"
scratch="$(mktemp -d "$experiments/bounded-scalars-replay.XXXXXX")"
trap 'rm -rf "$scratch"' EXIT

generated="$scratch/generated"
mkdir -p "$generated"

cd "$repo_root"
lake exe noctium compile examples/BoundedScalars.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json --output "$generated"
lake env lean --root=examples -o .lake/build/lib/lean/BoundedScalars.olean \
  examples/BoundedScalars.lean
lake env lean --run tests/scalars/BoundedScalarsReplay.lean > "$scratch/source-evidence.json"
cat "$scratch/source-evidence.json"

CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$repo_root/runtime/target}" \
NOCTIUM_BOUNDED_SCALARS_REPLAY_DIR="$generated" \
  cargo +1.100.0 test --locked --manifest-path runtime/Cargo.toml \
    --no-default-features --features zkir-321 --test bounded_scalars_replay \
    -- --ignored --nocapture
