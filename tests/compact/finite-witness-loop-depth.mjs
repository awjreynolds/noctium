import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/finite-witness-loop-depth.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
assert.match(execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim(),
  /^0\.36\.1 \(7fa3a117c/);
const runtimeDirectory = resolve(runtimePath);
const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
assert.equal(runtime.versionString, '0.21.0');

const fixtures = dirname(fileURLToPath(import.meta.url));
const experiments = resolve(fixtures, '../../build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'finite-witness-loop-depth-'));
try {
  const generated = join(scratch, 'compact');
  execFileSync(compactc, ['--skip-zk', join(fixtures, 'FiniteWitnessLoopDepth.compact'), generated]);
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const { Contract } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const wallet = '00'.repeat(32);
  for (const [circuitId, count] of [
    ['witnessLoop16', 16],
    ['witnessLoop32', 32],
    ['witnessLoop1025', 1025],
  ]) {
    const calls = [];
    const provider = ({ privateState }, index) => {
      calls.push(index);
      return [privateState, 0n];
    };
    const contract = new Contract({ visitValue: provider, visitValue16: provider });
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
    console.log(`${circuitId}: ${count} ordered witness arguments, result ${call.result}`);
  }
  const badCalls = [];
  const badContract = new Contract({
    visitValue: ({ privateState }) => [privateState, 0n],
    visitValue16: ({ privateState }, index) => {
      badCalls.push(index);
      return [privateState, index === 512n ? 1n : 0n];
    },
  });
  const { currentContractState } = await badContract.initialState(
    runtime.createConstructorContext(null, wallet));
  const badContext = runtime.createCircuitContext({
    circuitId: 'witnessLoop1025',
    contractAddress: runtime.dummyContractAddress(),
    coinPublicKeyOrZswapState: wallet,
    contractState: currentContractState.data,
    privateState: null,
  });
  await assert.rejects(async () => badContract.circuits.witnessLoop1025(badContext),
    /witness value must be zero/);
  assert.deepEqual(badCalls, Array.from({ length: 513 }, (_, index) => BigInt(index)));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
