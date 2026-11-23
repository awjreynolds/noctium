import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/vector-set-keys.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/,
  `expected pinned Compact compiler, got ${compilerVersion}`);
const runtimeDirectory = resolve(runtimePath);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'vector-set-keys-'));

try {
  const generated = join(scratch, 'compact');
  const source = join(root, 'tests/compact/VectorSetKeys.compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');
  const runtimeUrl = pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href;
  const contractUrl = pathToFileURL(join(generated, 'contract/index.js')).href;
  const { createCircuitContext, createConstructorContext, dummyContractAddress } = await import(runtimeUrl);
  const { Contract, ledger } = await import(contractUrl);

  const contract = new Contract({});
  const walletKey = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(createConstructorContext(null, walletKey));
  const initial = currentContractState.data;
  const first = 11n;
  const second = 22n;
  const third = 23n;
  const vector = (left, right) => [left, right];
  const run = async (name, state, ...args) => {
    const { result, context } = await contract.circuits[name](createCircuitContext({
      circuitId: name,
      contractAddress: dummyContractAddress(),
      coinPublicKeyOrZswapState: walletKey,
      contractState: state,
      privateState: null,
    }), ...args);
    return [result, context.callContext.currentQueryContext.state];
  };

  assert.equal(ledger(initial).vectorKeys.size(), 0n);
  assert.equal(ledger(initial).vectorKeys.isEmpty(), true);

  let [result, state] = await run('update', initial, first, second, third);
  assert.deepEqual(result, [true, true, true, 3n]);
  const afterInsert = ledger(state).vectorKeys;
  assert.equal(afterInsert.size(), 3n);
  assert.equal(afterInsert.member(vector(first, second)), true);
  assert.equal(afterInsert.member(vector(first, third)), true);
  assert.equal(afterInsert.member(vector(second, first)), true);

  [result, state] = await run('remove', state, first, second, third);
  assert.deepEqual(result, [false, true, true, 2n]);
  const afterRemove = ledger(state).vectorKeys;
  assert.equal(afterRemove.size(), 2n);
  assert.equal(afterRemove.member(vector(first, second)), false);
  assert.equal(afterRemove.member(vector(first, third)), true);
  assert.equal(afterRemove.member(vector(second, first)), true);

  [result, state] = await run('reset', state);
  assert.deepEqual(result, [0n, true]);
  const afterReset = ledger(state).vectorKeys;
  assert.equal(afterReset.size(), 0n);
  assert.equal(afterReset.isEmpty(), true);
  assert.equal(afterReset.member(vector(first, second)), false);
  assert.equal(afterReset.member(vector(first, third)), false);
  assert.equal(afterReset.member(vector(second, first)), false);

  console.log(JSON.stringify({
    fixture: 'VectorSetKeys',
    compact: compilerVersion,
    runtime: runtimePackage.version,
    keys: { first: ['11', '22'], sameFirstDifferentSecond: ['11', '23'], reversed: ['22', '11'] },
    outputs: {
      update: [true, true, true, '3'],
      remove: [false, true, true, '2'],
      reset: ['0', true],
    },
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
