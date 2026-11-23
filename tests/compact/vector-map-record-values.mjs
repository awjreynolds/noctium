import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, rmdirSync, symlinkSync } from 'node:fs';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/vector-map-record-values.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/,
  `expected pinned Compact 0.36.1 compiler, got ${compilerVersion}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0', 'expected pinned Compact runtime 0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/VectorMapRecordValues.compact');
const experiments = join(projectRoot, 'build/experiments/887-vector-key-record-values');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'run-'));

try {
  const generated = join(scratch, 'compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], {
    cwd: projectRoot,
    encoding: 'utf8',
  });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtimeUrl = pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href;
  const contractUrl = pathToFileURL(join(generated, 'contract/index.js')).href;
  const runtime = await import(runtimeUrl);
  const { Contract, ledger } = await import(contractUrl);
  assert.equal(runtime.versionString, '0.21.0');

  const contract = new Contract({});
  const walletKey = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(
    runtime.createConstructorContext(null, walletKey),
  );
  const initial = currentContractState.data;
  const keyA = [11n, 22n];
  const keyB = [11n, 23n];
  const run = async (name, state, ...args) => {
    const context = runtime.createCircuitContext({
      circuitId: name,
      contractAddress: runtime.dummyContractAddress(),
      coinPublicKeyOrZswapState: walletKey,
      contractState: state,
      privateState: null,
    });
    const call = await contract.circuits[name](context, ...args);
    return [call.result, call.context.callContext.currentQueryContext.state];
  };
  const assertReceipt = (actual, amount, active) => {
    assert.deepEqual(actual, { amount: BigInt(amount), active });
  };

  assert.equal(ledger(initial).receipts.size(), 0n);

  let [updateResult, state] = await run('update', initial, 11n, 22n, 23n);
  assert.deepEqual(updateResult, [true, true, 2n]);
  let receipts = ledger(state).receipts;
  assert.equal(receipts.size(), 2n);
  assert.equal(receipts.member(keyA), true);
  assert.equal(receipts.member(keyB), true);
  assertReceipt(receipts.lookup(keyA), 202, false);
  assertReceipt(receipts.lookup(keyB), 303, true);

  let [lookupResult] = await run('lookup', state, 11n, 22n, 23n);
  assert.deepEqual(lookupResult, [202n, false, 303n, true]);

  let [sizeResult] = await run('size', state);
  assert.equal(sizeResult, 2n);

  const [removeResult, afterRemove] = await run('remove', state, 11n, 22n, 23n);
  assert.deepEqual(removeResult, [false, true, 303n, true, 1n]);
  receipts = ledger(afterRemove).receipts;
  assert.equal(receipts.size(), 1n);
  assert.equal(receipts.member(keyA), false);
  assert.equal(receipts.member(keyB), true);
  assertReceipt(receipts.lookup(keyB), 303, true);

  console.log(JSON.stringify({
    fixture: 'VectorMapRecordValues',
    compiler: compilerVersion,
    runtime: runtimePackage.version,
    keys: { a: ['11', '22'], b: ['11', '23'] },
    update: { memberA: true, memberB: true, size: '2', receiptA: { amount: '202', active: false } },
    lookup: ['202', false, '303', true],
    remove: { memberA: false, memberB: true, receiptB: { amount: '303', active: true }, size: '1' },
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
  try {
    rmdirSync(experiments);
  } catch (error) {
    if (error.code !== 'ENOENT' && error.code !== 'ENOTEMPTY') throw error;
  }
}
