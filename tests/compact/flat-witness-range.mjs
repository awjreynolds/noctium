import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/flat-witness-range.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
assert.match(execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim(),
  /^0\.36\.1 \(7fa3a117c/);
const runtimeDirectory = resolve(runtimePath);
const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
assert.equal(runtime.versionString, '0.21.0');

const fixtures = dirname(fileURLToPath(import.meta.url));
const experiments = resolve(fixtures, '../../build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'flat-witness-range-'));
try {
  const generated = join(scratch, 'compact');
  execFileSync(compactc, ['--skip-zk', join(fixtures, 'FlatWitnessRange.compact'), generated]);
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const { Contract } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const wallet = '00'.repeat(32);
  for (const [circuitId, count] of [['shortRange', 3], ['longRange', 1025]]) {
    const calls = [];
    const contract = new Contract({
      visit: ({ privateState }, index) => {
        calls.push(index);
        return [privateState, []];
      },
    });
    const { currentContractState } = await contract.initialState(
      runtime.createConstructorContext(null, wallet));
    const context = runtime.createCircuitContext({
      circuitId,
      contractAddress: runtime.dummyContractAddress(),
      coinPublicKeyOrZswapState: wallet,
      contractState: currentContractState.data,
      privateState: null,
    });
    const call = await contract.circuits[circuitId](context);
    assert.equal(call.result, 0n);
    assert.deepEqual(calls, Array.from({ length: count }, (_, index) => BigInt(index)));
    console.log(`${circuitId}: ${count} ordered calls, result ${call.result}`);
  }
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
