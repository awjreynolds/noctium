import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/fixed-byte-record-set.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/);
const runtimeDirectory = resolve(runtimePath);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'fixed-byte-record-set-'));
try {
  const generated = join(scratch, 'compact');
  const source = join(root, 'tests/compact/FixedByteRecordSet.compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');
  const { createCircuitContext, createConstructorContext, dummyContractAddress } = await import(
    pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href,
  );
  const { Contract, ledger } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);

  const contract = new Contract({});
  const wallet = '00'.repeat(32);
  const owner = new Uint8Array(32).fill(1);
  const siblingOwner = new Uint8Array(32).fill(2);
  const tag = new Uint8Array([7]);
  const firstId = new Uint8Array(33).fill(3);
  const lateId = new Uint8Array(firstId);
  lateId[32] = 4;
  const absentId = new Uint8Array(firstId);
  absentId[32] = 5;
  const { currentContractState } = await contract.initialState(
    createConstructorContext(null, wallet), owner, siblingOwner,
  );
  const initial = currentContractState.data;
  const run = async (state) => {
    const { result, context } = await contract.circuits.update(createCircuitContext({
      circuitId: 'update', contractAddress: dummyContractAddress(),
      coinPublicKeyOrZswapState: wallet, contractState: state, privateState: null,
    }), owner, siblingOwner, tag, firstId, lateId, absentId);
    return [result, context.callContext.currentQueryContext.state];
  };

  const view = ledger(initial);
  assert.equal(view.buckets.lookup(owner).size(), 0n);
  const [result, state] = await run(initial);
  assert.deepEqual(result, [true, true, false, true, 2n, 1n]);
  const updated = ledger(state);
  const selected = updated.buckets.lookup(owner);
  const sibling = updated.buckets.lookup(siblingOwner);
  const key = (id) => ({ tag, id });
  assert.equal(selected.size(), 2n);
  assert.equal(selected.member(key(firstId)), true);
  assert.equal(selected.member(key(lateId)), true);
  assert.equal(selected.member(key(absentId)), false);
  assert.equal(sibling.size(), 1n);
  assert.equal(sibling.member(key(firstId)), true);
  assert.equal(updated.buckets.size(), 2n);
  console.log(JSON.stringify({
    fixture: 'FixedByteRecordSet', compact: compilerVersion, runtime: runtimePackage.version,
    outputs: [true, true, false, true, '2', '1'],
    exactDistinctKeys: ['3'.repeat(32) + '3', '3'.repeat(32) + '4'],
    siblingBuckets: 2,
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
