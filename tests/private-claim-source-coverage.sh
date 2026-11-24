#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

imports=".lake/build/lib/lean"
mkdir -p "$imports/examples" "$imports/proofs"
lake env lean -D Elab.async=false -o "$imports/examples/PrivateClaim.olean" examples/PrivateClaim.lean
lake env lean -D Elab.async=false -o "$imports/proofs/PrivateClaim.olean" proofs/PrivateClaim.lean
lake env lean -D Elab.async=false -o "$imports/proofs/PrivateClaimVerification.olean" proofs/PrivateClaimVerification.lean
lake env lean tests/PrivateClaimSourceCoverage.lean
