#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."

if [ "$#" -ne 2 ]; then
  echo "usage: $0 <compactc-0.36.1> <compact-runtime-0.21.0>" >&2
  exit 2
fi
compactc=$1
runtime_directory=$2

mkdir -p build/experiments
scratch=$(mktemp -d build/experiments/860-foreign-curve-generic.XXXXXX)
trap 'rm -rf "$scratch"' EXIT

lake env lean tests/Modules.lean
lake env lean tests/modules/ForeignCurveGenericIdentity.lean
lake exe noctium compile tests/modules/ForeignCurveGenericIdentity.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --emit standalone --emit specialization \
  --output "$scratch/noctium"
node tests/modules/check-foreign-curve-artifacts.mjs "$scratch/noctium"
node tests/compact/generic-foreign-curve-module.mjs "$compactc" "$runtime_directory"
