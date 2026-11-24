#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"
export PYTHONDONTWRITEBYTECODE=1

mkdir -p build/experiments
scratch="$(mktemp -d "$repo_root/build/experiments/foundation-source-v1.XXXXXX")"
cleanup() {
  rm -rf "$scratch"
}
trap cleanup EXIT HUP INT TERM

python3 scripts/proofs/check-private-claim-audit.py --report \
  > "$scratch/private-claim-report.json"

imports="$scratch/imports"
mkdir -p "$imports/examples" "$imports/proofs"
export LEAN_PATH="$imports"
lake build Noctium Noctium.Cli Noctium.Compiler Noctium.Frontend \
  Noctium.Verification.ExportAudit Noctium.Verification.ScalarNormalization \
  Noctium.Verification.SourceEffects
lake env lean -D Elab.async=false -o "$imports/examples/BoundedScalars.olean" \
  examples/BoundedScalars.lean
lake env lean -D Elab.async=false -o "$imports/proofs/BoundedScalarsVerification.olean" \
  proofs/BoundedScalarsVerification.lean
lake env leanexport proofs.BoundedScalarsVerification -- \
  Noctium.Verification.FunctionalObligation \
  Noctium.Verification.PrivacyObligation \
  Noctium.BoundedScalarsVerification.policy \
  propext Classical.choice Quot.sound \
  > "$scratch/bounded-scalars-model.ndjson"

python3 scripts/proofs/check-bounded-scalars-audit.py \
  --trusted-model-export "$scratch/bounded-scalars-model.ndjson" \
  > "$scratch/bounded-scalars-report.json"

target=profiles/midnight-ledger-9-zkir-3.2.1-target.json
lake env lean --run NoctiumMain.lean compile examples/PrivateClaim.lean \
  --target "$target" --emit ledger --output "$scratch/private-claim-artifacts"
lake env lean --run NoctiumMain.lean compile examples/BoundedScalars.lean \
  --target "$target" --emit ledger --output "$scratch/bounded-scalars-artifacts"

python3 scripts/proofs/check-foundation-source-profile.py \
  --private-claim-report "$scratch/private-claim-report.json" \
  --private-claim-artifacts "$scratch/private-claim-artifacts" \
  --bounded-scalars-report "$scratch/bounded-scalars-report.json" \
  --bounded-scalars-artifacts "$scratch/bounded-scalars-artifacts"
