import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/nested-fixed-bytes-record-cell.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
assert.match(execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim(),
  /^0\.36\.1 \(7fa3a117c/);
const runtimeDirectory = resolve(runtimePath);
const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
assert.equal(runtime.versionString, '0.21.0');

const fixtures = dirname(fileURLToPath(import.meta.url));
const experiments = resolve(fixtures, '../../build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'nested-fixed-bytes-record-cell-'));
try {
  const generated = join(scratch, 'compact');
  execFileSync(compactc, [
    '--skip-zk',
    join(fixtures, 'NestedFixedBytesRecordCell.compact'),
    generated,
  ]);
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const { Contract, ledger } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const wallet = '00'.repeat(32);
  const contract = new Contract({});
  const { currentContractState } = await contract.initialState(
    runtime.createConstructorContext(null, wallet));
  let state = currentContractState.data;

  async function invoke(circuitId, ...args) {
    const call = await contract.circuits[circuitId](runtime.createCircuitContext({
      circuitId,
      contractAddress: runtime.dummyContractAddress(),
      coinPublicKeyOrZswapState: wallet,
      contractState: state,
      privateState: null,
    }), ...args);
    state = call.context.callContext.currentQueryContext.state;
    return call.result;
  }

  const zeroPayload = new Uint8Array(40);
  const zeroRecord = {
    nested: { payload: zeroPayload, marker: 0n },
    count: 0n,
  };
  assert.deepEqual(ledger(state).record, zeroRecord);
  assert.deepEqual(await invoke('inspect'), [zeroPayload, 0n, 0n]);

  const payload = Uint8Array.from([
    ...Array.from({ length: 35 }, (_, index) => index + 1),
    0, 0, 0, 0, 0,
  ]);
  const marker = 0x123456789abcdefn;
  const counter = 18_446_744_073_709_551_615n;
  await assert.rejects(invoke('writeRecord', new Uint8Array(39), marker, counter));
  assert.deepEqual(ledger(state).record, zeroRecord, 'wrong byte length left the cell unchanged');

  await invoke('writeRecord', payload, marker, counter);
  assert.deepEqual(await invoke('inspect'), [payload, marker, counter]);
  assert.deepEqual(ledger(state).record, {
    nested: { payload, marker },
    count: counter,
  });

  assert.deepEqual(await invoke('clearRecord'), [zeroPayload, 0n, 0n]);
  assert.deepEqual(ledger(state).record, zeroRecord);
  console.log('Compact nested Bytes<40> Cell preserved trailing zeros, scalars, defaults, and reset behavior.');
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
