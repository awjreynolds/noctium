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
  const firstReceipt = { accepted: true, code: 101n };
  const lateReceipt = { accepted: false, code: 303n };
  const run = async (state, suppliedFirstId = firstId, suppliedLateId = lateId) => {
    const { result, context } = await contract.circuits.update(createCircuitContext({
      circuitId: 'update', contractAddress: dummyContractAddress(),
      coinPublicKeyOrZswapState: wallet, contractState: state, privateState: null,
    }), tag, suppliedFirstId, suppliedLateId,
    firstReceipt.accepted, firstReceipt.code, lateReceipt.accepted, lateReceipt.code);
    return [result, context.callContext.currentQueryContext.state];
  };

  assert.equal(ledger(initial).receipts.size(), 0n);
  const [outputs, state] = await run(initial);
  assert.deepEqual(outputs, [true, true, true, 101n, false, 303n, false, true, false, 303n]);
  const receipts = ledger(state).receipts;
  const key = id => ({ tag, id });
  assert.equal(receipts.size(), 1n);
  assert.equal(receipts.member(key(firstId)), false);
  assert.equal(receipts.member(key(lateId)), true);
  assert.deepEqual(receipts.lookup(key(lateId)), lateReceipt);
  await assert.rejects(() => run(initial, firstId, lateId.slice(0, 32)));

  console.log(JSON.stringify({
    fixture: 'RootFixedByteRecordValuedMap',
    compact: compilerVersion,
    runtime: runtimePackage.version,
    key: { tag: [7], firstId: '03'.repeat(33), lateId: '03'.repeat(32) + '04' },
    receipts: {
      first: { accepted: firstReceipt.accepted, code: firstReceipt.code.toString() },
      late: { accepted: lateReceipt.accepted, code: lateReceipt.code.toString() },
    },
    outputs: {
      first: true,
      late: true,
      firstAcceptedResult: true,
      firstCodeResult: '101',
      lateAcceptedResult: false,
      lateCodeResult: '303',
      firstRemaining: false,
      lateRemaining: true,
      retainedAccepted: false,
      retainedCode: '303',
    },
    remainingEntries: 1,
    wrongKeyWidthRejected: true,
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
