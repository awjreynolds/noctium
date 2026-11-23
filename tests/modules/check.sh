#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
lake env lean tests/Modules.lean
lake env lean tests/modules/PublicModuleAliases.lean
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
lake exe noctium compile tests/modules/Native.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --output "$scratch/first"

awk '/^def moduleContractRoot / { exit } { print }' tests/modules/Native.lean \
  > "$scratch/ModuleLibrary.lean"
{
  printf '%s\n' 'import ModuleLibrary' 'open scoped Noctium' 'open Noctium.Helpers.Specialization'
  sed -n '/^def moduleContractRoot /,$p' tests/modules/Native.lean
} > "$scratch/ModuleConsumer.lean"
lake env lean --root="$scratch" -o "$scratch/ModuleLibrary.olean" "$scratch/ModuleLibrary.lean"
LEAN_PATH="$scratch:$PWD/.lake/build/lib/lean" .lake/build/bin/noctium compile "$scratch/ModuleConsumer.lean" \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --output "$scratch/second"
diff -r "$scratch/first" "$scratch/second"
node - "$scratch/first/noctium.json" <<'JS'
const fs = require('node:fs');
const manifest = JSON.parse(fs.readFileSync(process.argv[2], 'utf8'));
const [contract] = manifest.contracts;
if (manifest.contracts.length !== 1 || contract.entrypoints.length !== 4) {
  throw new Error('expected one module contract with four exported entrypoints');
}
if (contract.state.length !== 2) {
  throw new Error(`expected two canonical state fields, found ${contract.state.length}`);
}
const stateTypes = contract.state.map(state => state.kind.cell).sort();
if (stateTypes.join(',') !== 'Native,UIntRange<256>') {
  throw new Error(`generic state types were not substituted: ${stateTypes.join(',')}`);
}
const entries = Object.fromEntries(contract.entrypoints.map(entry => [entry.name, entry]));
const field = name => entries[name].effects.find(effect => effect.op === 'writeCell')?.state;
if (entries.firstUpdate.circuit !== entries.againUpdate.circuit ||
    field('firstUpdate') !== field('againUpdate')) {
  throw new Error('re-export aliases did not reuse circuit and state identities');
}
if (entries.differentUpdate.circuit === entries.firstUpdate.circuit ||
    field('differentUpdate') === field('firstUpdate')) {
  throw new Error('different generic arguments reused a circuit or state identity');
}
const [read, check] = entries.againRead.effects;
if (entries.againRead.effects.length !== 2 ||
    read.op !== 'readCell' || read.state !== field('firstUpdate') ||
    check.op !== 'require') {
  throw new Error('reader alias did not use and check the original state field');
}
JS

sed 's/type := .parameter "T", visibility := .public/type := .parameter "T", visibility := .private/' \
  tests/modules/Native.lean > "$scratch/PrivateModule.lean"
if .lake/build/bin/noctium compile "$scratch/PrivateModule.lean" \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --output "$scratch/rejected" > "$scratch/error" 2>&1; then
  echo 'A module alias exposed a private value' >&2
  exit 1
fi
grep -F "undisclosed private parameter 'value'" "$scratch/error" > /dev/null
test ! -e "$scratch/rejected"
echo 'Module import, artifact determinism and re-export disclosure checks passed'
