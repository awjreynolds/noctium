#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
cli="$PWD/.lake/build/bin/noctium"
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT

cat > "$scratch/Supported.lean" <<'LEAN'
import Noctium.Frontend
open scoped Noctium
noctium_require_source_api "0.1.0"
noctium_circuit sourceApiSupported where
  output result : Native := 7
end
LEAN
source="$scratch/Supported.lean"
selected=profiles/midnight-ledger-9-zkir-3.2.1-target.json
"$cli" check "$source" --target "$selected"
"$cli" compile "$source" --target "$selected" --emit standalone --output "$scratch/supported"
test -s "$scratch/supported/sourceApiSupported.zkir"

sed 's/0.1.0/>=0.0.0, <0.1.0 || =0.1.0/' "$source" > "$scratch/Range.lean"
"$cli" check "$scratch/Range.lean" --target "$selected"
"$cli" compile "$scratch/Range.lean" --target "$selected" --emit standalone --output "$scratch/ranged"
sed '/^noctium_require_source_api /d' "$source" > "$scratch/Unspecified.lean"
"$cli" compile "$scratch/Unspecified.lean" --target "$selected" --emit standalone --output "$scratch/unspecified"
relation=sourceApiSupported.zkir
cmp "$scratch/supported/$relation" "$scratch/ranged/$relation"
cmp "$scratch/supported/$relation" "$scratch/unspecified/$relation"

{
  cat "$source"
  printf '%s\n' 'noctium_require_target "midnight-ledger-9-zkir-3.2.1"'
} > "$scratch/Independent.lean"
"$cli" check "$scratch/Independent.lean" --target "$selected"
if "$cli" check "$scratch/Independent.lean" > "$scratch/target-rejected" 2>&1; then
  echo 'matching source API requirement bypassed the native target requirement' >&2
  exit 1
fi
grep -F "requires target 'midnight-ledger-9-zkir-3.2.1'" "$scratch/target-rejected" > /dev/null

for operation in check compile; do
  args=()
  if [[ "$operation" == compile ]]; then args+=(--output "$scratch/rejected"); fi
  sed 's/0.1.0/0.2.0/' "$source" > "$scratch/Incompatible.lean"
  if "$cli" "$operation" "$scratch/Incompatible.lean" "${args[@]}" \
      > "$scratch/$operation-rejected" 2>&1; then
    echo "incompatible source API requirement passed $operation" >&2
    exit 1
  fi
  grep -F "requires source API" "$scratch/$operation-rejected" > /dev/null
done
test ! -e "$scratch/rejected"

sed 's/0.1.0/not-a-version/' "$source" > "$scratch/Malformed.lean"
if "$cli" check "$scratch/Malformed.lean" > "$scratch/malformed" 2>&1; then
  echo 'malformed source API requirement passed check' >&2
  exit 1
fi
grep -F 'invalid Noctium source API requirement' "$scratch/malformed" > /dev/null

mkdir -p "$scratch/imports"
cat > "$scratch/imports/Pinned.lean" <<'LEAN'
import Noctium.Frontend
open scoped Noctium
noctium_require_source_api ">=0.2.0"
LEAN
cat > "$scratch/imports/Relay.lean" <<'LEAN'
import Pinned
LEAN
lake env lean --root="$scratch/imports" -o "$scratch/imports/Pinned.olean" \
  "$scratch/imports/Pinned.lean"
lean_path="$scratch/imports:$PWD/.lake/build/lib/lean"
env LEAN_PATH="$lean_path" lean --root="$scratch/imports" \
  -o "$scratch/imports/Relay.olean" "$scratch/imports/Relay.lean"
cat > "$scratch/Imported.lean" <<'LEAN'
import Relay
import Noctium.Frontend
open scoped Noctium
noctium_circuit importedSourceApiMismatch where
  output result : Native := 7
end
LEAN
if env LEAN_PATH="$lean_path" "$cli" check "$scratch/Imported.lean" \
    > "$scratch/imported-mismatch" 2>&1; then
  echo 'incompatible source API requirement passed check' >&2
  exit 1
fi
grep -F "Noctium module 'Pinned' requires source API '>=0.2.0'" \
  "$scratch/imported-mismatch" > /dev/null
if env LEAN_PATH="$lean_path" "$cli" compile "$scratch/Imported.lean" \
    --output "$scratch/imported-rejected" > "$scratch/imported-compile-mismatch" 2>&1; then
  echo 'incompatible imported source API requirement passed compile' >&2
  exit 1
fi
grep -F "Noctium module 'Pinned' requires source API '>=0.2.0'" \
  "$scratch/imported-compile-mismatch" > /dev/null
test ! -e "$scratch/imported-rejected"
