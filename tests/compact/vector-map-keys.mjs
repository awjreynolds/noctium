import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/vector-map-keys.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

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
const scratch = mkdtempSync(join(experiments, 'vector-map-keys-'));

try {
  const generated = join(scratch, 'compact');
  const source = join(root, 'tests/compact/VectorMapKeys.compact');
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
  const keyA = [first, second];
  const keyB = [first, third];
  const missingKey = [second, third];
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

  const initialMap = ledger(initial).vectorValues;
  assert.equal(initialMap.size(), 0n);
  assert.equal(initialMap.member(keyA), false);

  let [result, state] = await run('update', initial, first, second, third);
  assert.deepEqual(result, [true, true, 2n]);
  const afterUpdate = ledger(state).vectorValues;
  assert.equal(afterUpdate.size(), 2n);
  assert.equal(afterUpdate.member(keyA), true);
  assert.equal(afterUpdate.member(keyB), true);
  assert.equal(afterUpdate.lookup(keyA), 202n);
  assert.equal(afterUpdate.lookup(keyB), 303n);

  [result, state] = await run('lookup', state, first, second, third);
  assert.deepEqual(result, [202n, 303n, 0n]);

  [result, state] = await run('member', state, first, second, third);
  assert.deepEqual(result, [true, true, false]);

  [result, state] = await run('size', state);
  assert.equal(result, 2n);

  [result, state] = await run('remove', state, first, second, third);
  assert.deepEqual(result, [false, true, 0n, 1n]);
  const afterRemove = ledger(state).vectorValues;
  assert.equal(afterRemove.size(), 1n);
  assert.equal(afterRemove.member(keyA), false);
  assert.equal(afterRemove.member(keyB), true);
  assert.equal(afterRemove.lookup(keyB), 303n);

  console.log(JSON.stringify({
    fixture: 'VectorMapKeys',
    compact: compilerVersion,
    runtime: runtimePackage.version,
    keys: {
      first: ['11', '22'],
      sameFirstDifferentSecond: ['11', '23'],
      missing: ['22', '23'],
    },
    outputs: {
      update: [true, true, '2'],
      lookup: ['202', '303', '0'],
      member: [true, true, false],
      size: '2',
      remove: [false, true, '0', '1'],
    },
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
