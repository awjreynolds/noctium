import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/root-fixed-byte-record-set.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/);
const runtimeDirectory = resolve(runtimePath);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'root-fixed-byte-record-set-'));
try {
  const generated = join(scratch, 'compact');
  const source = join(root, 'tests/compact/RootFixedByteRecordSet.compact');
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
  const tag = new Uint8Array([7]);
  const firstId = new Uint8Array(33).fill(3);
  const lateId = new Uint8Array(firstId);
  lateId[32] = 4;
  const { currentContractState } = await contract.initialState(
    createConstructorContext(null, wallet),
  );
  const initial = currentContractState.data;
  const run = async (state, suppliedFirst = firstId, suppliedLate = lateId) => {
    const { result, context } = await contract.circuits.update(createCircuitContext({
      circuitId: 'update',
      contractAddress: dummyContractAddress(),
      coinPublicKeyOrZswapState: wallet,
      contractState: state,
      privateState: null,
    }), tag, suppliedFirst, suppliedLate);
    return [result, context.callContext.currentQueryContext.state];
  };

  const initialSet = ledger(initial).members;
  assert.equal(initialSet.size(), 0n);
  assert.equal(initialSet.isEmpty(), true);

  const [result, state] = await run(initial);
  assert.deepEqual(result, [true, true, false, true, 1n]);
  const members = ledger(state).members;
  const record = (id) => ({ tag, id });
  assert.equal(members.size(), 1n);
  assert.equal(members.member(record(firstId)), false);
  assert.equal(members.member(record(lateId)), true);

  await assert.rejects(() => run(initial, firstId.slice(0, 32), lateId));

  console.log(JSON.stringify({
    fixture: 'RootFixedByteRecordSet',
    compact: compilerVersion,
    runtime: runtimePackage.version,
    record: { tag: [7], firstId: '03'.repeat(33), lateId: '03'.repeat(32) + '04' },
    outputs: {
      beforeRemoval: [true, true],
      afterRemoval: [false, true],
      size: '1',
    },
    wrongKeyWidthRejected: true,
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
