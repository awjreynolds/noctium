#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
cli="$PWD/.lake/build/bin/noctium"
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT

cat > "$scratch/TargetRequirement.lean" <<'LEAN'
import Noctium.Frontend
open scoped Noctium

set_option noctium.requiredTarget "midnight-ledger-9-zkir-3.2.1"

noctium_circuit targetRequirement where
  output result : Native := 7
end
LEAN
source="$scratch/TargetRequirement.lean"
target=profiles/midnight-ledger-9-zkir-3.2.1-target.json
"$cli" check "$source" --target "$target"
"$cli" compile "$source" --target "$target" --emit standalone --output "$scratch/matched"
test -s "$scratch/matched/targetRequirement.zkir"

if "$cli" check "$source" > "$scratch/check-error" 2>&1; then
  exit 1
fi
if "$cli" compile "$source" --output "$scratch/mismatched" > "$scratch/compile-error" 2>&1; then
  exit 1
fi
for operation in check compile; do
  grep -F "requires target 'midnight-ledger-9-zkir-3.2.1', selected 'midnight-ledger-9'" \
    "$scratch/$operation-error" > /dev/null
done
test ! -e "$scratch/mismatched"

sed 's/midnight-ledger-9-zkir-3.2.1/unknown-profile/' "$source" > "$scratch/Unknown.lean"
if "$cli" check "$scratch/Unknown.lean" --target "$target" > "$scratch/unknown-error" 2>&1; then
  exit 1
fi
grep -F "unknown Noctium source target requirement 'unknown-profile'" "$scratch/unknown-error" > /dev/null

# A requirement stored in an imported module must survive through its .olean
# and apply to a source that imports it indirectly.
mkdir -p "$scratch/imports"
cat > "$scratch/imports/Pinned.lean" <<'LEAN'
import Noctium.Frontend
open scoped Noctium
noctium_require_target "midnight-ledger-9-zkir-3.2.1"
LEAN
cat > "$scratch/imports/Relay.lean" <<'LEAN'
import Pinned
LEAN
lake env lean --root="$scratch/imports" -o "$scratch/imports/Pinned.olean" \
  "$scratch/imports/Pinned.lean"
lean_path="$scratch/imports:$PWD/.lake/build/lib/lean"
env LEAN_PATH="$lean_path" lean --root="$scratch/imports" -o "$scratch/imports/Relay.olean" \
  "$scratch/imports/Relay.lean"

cat > "$scratch/TransitiveRequirement.lean" <<'LEAN'
import Relay
import Noctium.Frontend
open scoped Noctium
noctium_circuit transitiveRequirement where
  output result : Native := 7
end
LEAN
transitive="$scratch/TransitiveRequirement.lean"
env LEAN_PATH="$lean_path" "$cli" check "$transitive" --target "$target"
env LEAN_PATH="$lean_path" "$cli" compile "$transitive" --target "$target" \
  --emit standalone --output "$scratch/transitive-matched"
test -s "$scratch/transitive-matched/transitiveRequirement.zkir"

if env LEAN_PATH="$lean_path" "$cli" check "$transitive" > "$scratch/transitive-check-error" 2>&1; then
  exit 1
fi
if env LEAN_PATH="$lean_path" "$cli" compile "$transitive" --output "$scratch/transitive-mismatched" \
    > "$scratch/transitive-compile-error" 2>&1; then
  exit 1
fi
for operation in check compile; do
  grep -F "Noctium module 'Pinned' requires target 'midnight-ledger-9-zkir-3.2.1', selected 'midnight-ledger-9'" \
    "$scratch/transitive-$operation-error" > /dev/null
done
test ! -e "$scratch/transitive-mismatched"

# Importing a second module with a conflicting explicit baseline requirement
# must fail before the CLI creates output.
cat > "$scratch/imports/Baseline.lean" <<'LEAN'
import Noctium.Frontend
open scoped Noctium
noctium_require_target "midnight-ledger-9"
LEAN
lake env lean --root="$scratch/imports" -o "$scratch/imports/Baseline.olean" \
  "$scratch/imports/Baseline.lean"
cat > "$scratch/ConflictingRequirements.lean" <<'LEAN'
import Pinned
import Baseline
import Noctium.Frontend
open scoped Noctium
noctium_circuit conflictingRequirements where
  output result : Native := 7
end
LEAN
if env LEAN_PATH="$lean_path" "$cli" compile "$scratch/ConflictingRequirements.lean" \
    --target "$target" --output "$scratch/conflicting-output" \
    > "$scratch/conflicting-error" 2>&1; then
  echo 'conflicting imported target requirements passed compile' >&2
  exit 1
fi
grep -F "Noctium module 'Baseline' requires target 'midnight-ledger-9', selected 'midnight-ledger-9-zkir-3.2.1'" \
  "$scratch/conflicting-error" > /dev/null
test ! -e "$scratch/conflicting-output"

cat > "$scratch/UnknownCommand.lean" <<'LEAN'
import Noctium.Frontend
open scoped Noctium
noctium_require_target "unknown-profile"
noctium_circuit unknownCommand where
  output result : Native := 7
end
LEAN
if "$cli" check "$scratch/UnknownCommand.lean" --target "$target" \
    > "$scratch/unknown-command-error" 2>&1; then
  echo 'unknown noctium_require_target profile passed check' >&2
  exit 1
fi
grep -F "unknown Noctium source target requirement 'unknown-profile'" \
  "$scratch/unknown-command-error" > /dev/null
