#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
cli="$PWD/.lake/build/bin/noctium"
scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT

"$cli" compile examples/BoundedScalars.lean --output "$scratch/first"
"$cli" compile examples/BoundedScalars.lean --output "$scratch/second"
diff -r "$scratch/first" "$scratch/second"

node --input-type=module - "$scratch/first" <<'JS'
import {readFileSync} from 'node:fs';
import {join} from 'node:path';
import {deepStrictEqual, ok} from 'node:assert/strict';
const directory = process.argv[2];
const plan = JSON.parse(readFileSync(join(directory, 'BoundedScalars.apply.impact.json')));
const circuit = JSON.parse(readFileSync(join(directory, 'BoundedScalars.apply.zkir')));
deepStrictEqual(plan.circuit.inputs.map(value => value.type), ['UIntRange<511>', 'UIntRange<256>', 'UIntRange<256>']);
deepStrictEqual(plan.state[0].kind, {cell: 'UIntRange<511>'});
deepStrictEqual(plan.circuit.constraints[0].left.tag, 'uadd');
deepStrictEqual(plan.circuit.constraints[0].left.maximum, '510');
ok(circuit.instructions.some(value => value.op === 'constrain_bits' && value.bits === 8));
ok(circuit.instructions.some(value => value.op === 'less_than' && value.bits === 9));
ok(circuit.instructions.every(value => value.op !== 'sub'));
deepStrictEqual(circuit.instructions.filter(value => value.op === 'output').length, 1);
deepStrictEqual(circuit.instructions.at(-1).op, 'output');
JS

cat > "$scratch/invalid.lean" <<'LEAN'
import Noctium.Frontend
open scoped Noctium
noctium_circuit bad where
  private unused : UInt 249
end
LEAN
if "$cli" compile "$scratch/invalid.lean" --output "$scratch/invalid-output" > "$scratch/error" 2>&1; then
  echo 'oversized unsigned type compiled' >&2
  exit 1
fi
grep -F 'unsigned width exceeds target maximum' "$scratch/error" > /dev/null
test ! -e "$scratch/invalid-output"

"$cli" compile examples/PrivateClaim.lean --output "$scratch/claim-first"
"$cli" compile examples/PrivateClaim.lean --output "$scratch/claim-second"
diff -r "$scratch/claim-first" "$scratch/claim-second"
node tests/private-claim-smoke.mjs "$scratch/claim-first"

# The smoke boundary must reject genuine compiler output for another profile.
"$cli" compile examples/PrivateClaim.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --output "$scratch/claim-wrong-profile"
if node tests/private-claim-smoke.mjs "$scratch/claim-wrong-profile" > "$scratch/wrong-profile-error" 2>&1; then
  echo 'PrivateClaim smoke accepted the wrong target profile' >&2
  exit 1
fi
grep -F 'wrong target profile' "$scratch/wrong-profile-error" > /dev/null

# Compile a real PrivateClaim source variant with a different entrypoint name.
sed 's/entry claim uses/entry verify uses/' examples/PrivateClaim.lean > "$scratch/wrong-operation.lean"
"$cli" compile "$scratch/wrong-operation.lean" --output "$scratch/claim-wrong-operation"
if node tests/private-claim-smoke.mjs "$scratch/claim-wrong-operation" > "$scratch/wrong-operation-error" 2>&1; then
  echo 'PrivateClaim smoke accepted the wrong entrypoint' >&2
  exit 1
fi
grep -F 'wrong operation' "$scratch/wrong-operation-error" > /dev/null

echo 'Unsigned CLI conformance passed'
