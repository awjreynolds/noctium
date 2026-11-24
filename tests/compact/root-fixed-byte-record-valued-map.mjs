import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/root-fixed-byte-record-valued-map.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/);
const runtimeDirectory = resolve(runtimePath);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'root-fixed-byte-record-valued-map-'));
try {
  const generated = join(scratch, 'compact');
  const source = join(root, 'tests/compact/RootFixedByteRecordValuedMap.compact');
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
  const { currentContractState } = await contract.initialState(createConstructorContext(null, wallet));
  const initial = currentContractState.data;
  const tag = new Uint8Array([7]);
  const firstId = new Uint8Array(33).fill(3);
  const lateId = new Uint8Array(firstId);
  lateId[32] = 4;
  const firstReceipt = { label: new Uint8Array([11]), digest: new Uint8Array(33).fill(21) };
  const lateReceipt = { label: new Uint8Array([12]), digest: new Uint8Array(33).fill(22) };
  const firstAccount = new Uint8Array(32).fill(5);
  const lateAccount = new Uint8Array(32).fill(6);
  const firstProfile = { label: new Uint8Array([31]), digest: new Uint8Array(33).fill(41) };
  const lateProfile = { label: new Uint8Array([32]), digest: new Uint8Array(33).fill(42) };
  const arguments_ = [tag, firstId, lateId,
    firstReceipt.label, firstReceipt.digest, lateReceipt.label, lateReceipt.digest,
    firstAccount, lateAccount, firstProfile.label, firstProfile.digest,
    lateProfile.label, lateProfile.digest];
  const run = async (state, supplied = arguments_) => {
    const { result, context } = await contract.circuits.update(createCircuitContext({
      circuitId: 'update', contractAddress: dummyContractAddress(),
      coinPublicKeyOrZswapState: wallet, contractState: state, privateState: null,
    }), ...supplied);
    return [result, context.callContext.currentQueryContext.state];
  };

  assert.equal(ledger(initial).receipts.size(), 0n);
  assert.equal(ledger(initial).profiles.size(), 0n);
  const [result, state] = await run(initial);
  const names = [
    'first', 'late', 'firstStoredLabel', 'firstStoredDigest',
    'lateStoredLabel', 'lateStoredDigest', 'firstRemaining', 'lateRemaining',
    'retainedLabel', 'retainedDigest', 'firstProfile', 'lateProfile',
    'firstProfileStoredLabel', 'firstProfileStoredDigest',
    'lateProfileStoredLabel', 'lateProfileStoredDigest',
    'firstProfileRemaining', 'lateProfileRemaining',
    'retainedProfileLabel', 'retainedProfileDigest',
  ];
  const byteNames = new Set(names.filter(name => name.toLowerCase().includes('label') ||
    name.toLowerCase().includes('digest')));
  const outputs = Object.fromEntries(names.map((name, index) => [
    name, byteNames.has(name) ? { kind: 'bytes', values: Array.from(result[index]) } : result[index],
  ]));
  const expectedOutputs = {
    first: true,
    late: true,
    firstStoredLabel: { kind: 'bytes', values: [11] },
    firstStoredDigest: { kind: 'bytes', values: Array(33).fill(21) },
    lateStoredLabel: { kind: 'bytes', values: [12] },
    lateStoredDigest: { kind: 'bytes', values: Array(33).fill(22) },
    firstRemaining: false,
    lateRemaining: true,
    retainedLabel: { kind: 'bytes', values: [12] },
    retainedDigest: { kind: 'bytes', values: Array(33).fill(22) },
    firstProfile: true,
    lateProfile: true,
    firstProfileStoredLabel: { kind: 'bytes', values: [31] },
    firstProfileStoredDigest: { kind: 'bytes', values: Array(33).fill(41) },
    lateProfileStoredLabel: { kind: 'bytes', values: [32] },
    lateProfileStoredDigest: { kind: 'bytes', values: Array(33).fill(42) },
    firstProfileRemaining: false,
    lateProfileRemaining: true,
    retainedProfileLabel: { kind: 'bytes', values: [32] },
    retainedProfileDigest: { kind: 'bytes', values: Array(33).fill(42) },
  };
  assert.deepEqual(outputs, expectedOutputs);

  const receipts = ledger(state).receipts;
  const profiles = ledger(state).profiles;
  const key = id => ({ tag, id });
  assert.equal(receipts.size(), 1n);
  assert.equal(receipts.member(key(firstId)), false);
  assert.equal(receipts.member(key(lateId)), true);
  assert.deepEqual(receipts.lookup(key(lateId)), lateReceipt);
  assert.equal(profiles.size(), 1n);
  assert.equal(profiles.member(firstAccount), false);
  assert.equal(profiles.member(lateAccount), true);
  assert.deepEqual(profiles.lookup(lateAccount), lateProfile);

  const wrongKeyWidth = [...arguments_];
  wrongKeyWidth[2] = lateId.slice(0, 32);
  await assert.rejects(() => run(initial, wrongKeyWidth));
  const wrongRecordValueWidth = [...arguments_];
  wrongRecordValueWidth[6] = lateReceipt.digest.slice(0, 32);
  await assert.rejects(() => run(initial, wrongRecordValueWidth));
  const wrongValueWidth = [...arguments_];
  wrongValueWidth[12] = lateProfile.digest.slice(0, 32);
  await assert.rejects(() => run(initial, wrongValueWidth));

  console.log(JSON.stringify({
    fixture: 'RootFixedByteRecordValuedMap',
    compact: compilerVersion,
    runtime: runtimePackage.version,
    inputs: {
      recordKey: { tag: [7], firstId: '03'.repeat(33), lateId: '03'.repeat(32) + '04' },
      recordValues: {
        first: { label: [11], digest: Array(33).fill(21) },
        late: { label: [12], digest: Array(33).fill(22) },
      },
      scalarKey: { firstAccount: '05'.repeat(32), lateAccount: '06'.repeat(32) },
      scalarValues: {
        first: { label: [31], digest: Array(33).fill(41) },
        late: { label: [32], digest: Array(33).fill(42) },
      },
    },
    outputs,
    remainingEntries: { receipts: Number(receipts.size()), profiles: Number(profiles.size()) },
    wrongKeyWidthRejected: true,
    wrongRecordValueWidthRejected: true,
    wrongValueWidthRejected: true,
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
