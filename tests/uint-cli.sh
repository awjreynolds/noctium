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
"$cli" compile examples/PrivateClaim.lean --target profiles/midnight-ledger-9-zkir-3.2.1-target.json --output "$scratch/claim-321"
node --input-type=module - "$scratch/claim-first" "$scratch/claim-321" "$scratch/first" <<'JS'
import {readFileSync} from 'node:fs';
import {join} from 'node:path';
import {deepStrictEqual, equal, ok, throws} from 'node:assert/strict';
const [claimDir, wrongProfileDir, wrongOperationDir] = process.argv.slice(2);
const readJson = path => JSON.parse(readFileSync(path, 'utf8'));
const defaultProfile = readJson('profiles/midnight-ledger-9.json');
function checkClaim(directory) {
  const metadata = readJson(join(directory, 'noctium.json'));
  equal(metadata.target, 'midnight-ledger-9', 'expected default profile');
  deepStrictEqual(metadata.targetProfile, defaultProfile);
  equal(metadata.targetProfile.zkir, '3.2.0');
  const contract = metadata.contracts.find(value => value.name === 'PrivateClaim');
  if (!contract) throw new Error('expected PrivateClaim contract');
  equal(contract.entrypoints.length, 1);
  const entrypoint = contract.entrypoints[0];
  equal(entrypoint.name, 'claim');
  equal(entrypoint.nativeCircuitFile, 'PrivateClaim.claim.zkir');
  equal(entrypoint.nativePlanFile, 'PrivateClaim.claim.impact.json');
  const circuit = readJson(join(directory, entrypoint.nativeCircuitFile));
  deepStrictEqual(circuit.do_communications_commitment, true);
  ok(circuit.instructions.some(value => value.op === 'transient_hash'));
  ok(circuit.instructions.some(value => value.op === 'impact'));
  const plan = readJson(join(directory, entrypoint.nativePlanFile));
  equal(plan.contractName, 'PrivateClaim');
  equal(plan.entrypoint, 'claim');
  deepStrictEqual(plan.circuit.outputs[0].expression, {tag: 'reference', name: 'suppliedNullifier'});
  deepStrictEqual(plan.reads.map(value => value.name),
    ['root', 'campaign', 'suppliedNullifier', 'storedRoot', 'storedCampaign', '_noctium_absence_5']);
}
checkClaim(claimDir);
throws(() => checkClaim(wrongProfileDir), /expected default profile/);
throws(() => checkClaim(wrongOperationDir), /PrivateClaim/);
JS
echo 'Unsigned CLI conformance passed'
