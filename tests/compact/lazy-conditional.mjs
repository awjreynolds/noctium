import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/lazy-conditional.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const version = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(version, /^0\.36\.1 \(7fa3a117c/);
assert.equal(JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8')).version, '0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'lazy-conditional-'));
try {
  const generated = join(scratch, 'compact');
  const source = join(projectRoot, 'tests/compact/LazyConditional.compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, compile.stderr || compile.stdout);
  const incompatible = join(scratch, 'IncompatibleConditional.compact');
  writeFileSync(incompatible, `pragma language_version 0.28;
export circuit mismatch(choice: Boolean, value: Uint<8>): Uint<8> {
  return choice ? value : true;
}
`);
  const rejected = spawnSync(compactc, ['--skip-zk', incompatible, join(scratch, 'rejected')], {
    encoding: 'utf8',
  });
  assert.ok(rejected.status !== null && rejected.status !== 0, rejected.stderr || rejected.stdout);
  assert.match(rejected.stderr || rejected.stdout, /mismatch between type/i);
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');
  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  const { Contract } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);

  const calls = [];
  const contract = new Contract({
    loadLeft: ({ privateState }) => {
      calls.push('left');
      return [privateState, { amount: 7n, extra: { enabled: true } }];
    },
    loadRight: ({ privateState }) => {
      calls.push('right');
      return [privateState, { amount: 9n, extra: { enabled: false } }];
    },
    afterChoice: ({ privateState }, expected) => {
      calls.push(['tail', expected]);
      return [privateState, []];
    },
  });
  const wallet = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(runtime.createConstructorContext(null, wallet));
  const context = (circuitId) => runtime.createCircuitContext({
    circuitId, contractAddress: runtime.dummyContractAddress(),
    coinPublicKeyOrZswapState: wallet, contractState: currentContractState.data,
    privateState: null,
  });

  const branches = async (thenCondition, elseCondition, amount) =>
    contract.circuits.branches(context('branches'), thenCondition, elseCondition, amount);
  assert.deepEqual((await branches(false, true, 3n)).result, [true, true, 3n]);
  assert.deepEqual((await branches(true, true, 1n)).result, [true, true, 1n]);
  await assert.rejects(branches(true, true, 3n));
  await assert.rejects(branches(false, false, 3n));

  const valueChoice = async (choice, expected) =>
    contract.circuits.valueChoice(context('valueChoice'), choice, expected);
  assert.deepEqual((await valueChoice(true, 7n)).result, [7n, true]);
  assert.deepEqual(calls.splice(0), ['left']);
  assert.deepEqual((await valueChoice(false, 9n)).result, [9n, false]);
  assert.deepEqual(calls.splice(0), ['right']);
  await assert.rejects(valueChoice(true, 9n));
  assert.deepEqual(calls, ['left']);
  calls.length = 0;

  const branchChoice = async (choice, expected) =>
    contract.circuits.branchChoice(context('branchChoice'), choice, expected);
  assert.deepEqual((await branchChoice(true, 7n)).result, [7n, true]);
  assert.deepEqual(calls.splice(0), ['left', ['tail', 7n]]);
  assert.deepEqual((await branchChoice(false, 9n)).result, [9n, false]);
  assert.deepEqual(calls.splice(0), ['right', ['tail', 9n]]);
  await assert.rejects(branchChoice(true, 9n));
  assert.deepEqual(calls, ['left']);
  console.log(`Compact ${version} matched lazy scalar and aggregate value conditionals`);
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
