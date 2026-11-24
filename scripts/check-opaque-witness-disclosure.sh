#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

if [[ $# -ne 2 ]]; then
  echo "usage: $0 <compactc-0.36.1> <compact-runtime-0.21.0>" >&2
  exit 2
fi
compactc=$1
compact_runtime=$2
mkdir -p build/experiments
scratch="$(mktemp -d "$PWD/build/experiments/1224-opaque-witness-disclosure.XXXXXX")"
trap 'rm -rf -- "$scratch"' EXIT

lake exe noctium compile tests/OpaqueWitnessDisclosure.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --output "$scratch/noctium"
node tests/compact/opaque-witness-disclosure.mjs "$compactc" "$compact_runtime"
NOCTIUM_OPAQUE_WITNESS_DIR="$scratch/noctium" \
  cargo +1.100.0 test --locked --manifest-path runtime/Cargo.toml --no-default-features \
    --features zkir-321 --test opaque_witness_disclosure \
    opaque_string_provider_is_disclosed_into_a_root_cell_and_bindings_reject_tampering \
    -- --ignored --exact
