import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';

const [generatedDirectory] = process.argv.slice(2);
const runtimeDirectory = process.env.NOCTIUM_COMPACT_RUNTIME_DIR;
assert.ok(generatedDirectory && runtimeDirectory, 'pass the compiler output and set NOCTIUM_COMPACT_RUNTIME_DIR');
const runtimePackage = JSON.parse(readFileSync(resolve(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');
const { createCircuitContext, createConstructorContext, dummyContractAddress } = await import(
  pathToFileURL(resolve(runtimeDirectory, 'dist/index.js')).href,
);
const { Contract } = await import(
  pathToFileURL(resolve(generatedDirectory, 'contract/index.js')).href,
);

const contract = new Contract({});
const key = '00'.repeat(32);
const { currentContractState } = await contract.initialState(createConstructorContext(null, key));
const maxU64 = (1n << 64n) - 1n;
const maxSafeTime = Number.MAX_SAFE_INTEGER;
const cases = [
  ['before', 9, 10n],
  ['equal', 10, 10n],
  ['after', 11, 10n],
  ['zero', 0, 0n],
  ['u64 max deadline', 0, maxU64],
  ['max safe time equal', maxSafeTime, BigInt(maxSafeTime)],
  ['max safe time before', maxSafeTime, BigInt(maxSafeTime) + 1n],
  ['max safe time after', maxSafeTime, BigInt(maxSafeTime) - 1n],
];
const evidence = [];
for (const [label, time, cutoff] of cases) {
  for (const enabled of [true, false]) {
    const context = createCircuitContext({
      circuitId: 'checkTime',
      contractAddress: dummyContractAddress(),
      coinPublicKeyOrZswapState: key,
      contractState: currentContractState.data,
      privateState: null,
      time,
    });
    const { result } = await contract.circuits.checkTime(context, cutoff, enabled);
    const now = BigInt(time);
    const expected = [
      enabled && now < cutoff,
      enabled && now > cutoff,
      enabled && now >= cutoff,
      enabled && now <= cutoff,
    ];
    assert.deepEqual(result, expected);
    evidence.push({ label, time, cutoff: cutoff.toString(), enabled, result });
  }
}
console.log(JSON.stringify({
  compiler: 'Compact 0.36.1',
  runtime: runtimePackage.version,
  circuit: 'checkTime',
  outputOrder: ['blockTimeLessThan', 'blockTimeGreaterThan', 'blockTimeGte', 'blockTimeLte'],
  timeRepresentation: 'runtime context accepts Number, tested through Number.MAX_SAFE_INTEGER',
  cases: evidence,
}, null, 2));
