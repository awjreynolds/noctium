import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/nested-record-cell.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
assert.match(execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim(),
  /^0\.36\.1 \(7fa3a117c/);
const runtimeDirectory = resolve(runtimePath);
const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
assert.equal(runtime.versionString, '0.21.0');

const fixtures = dirname(fileURLToPath(import.meta.url));
const experiments = resolve(fixtures, '../../build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'nested-record-cell-'));
try {
  const generated = join(scratch, 'compact');
  execFileSync(compactc, ['--skip-zk', join(fixtures, 'NestedRecordCell.compact'), generated]);
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');
  const { Contract, ledger } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const wallet = '00'.repeat(32);
  const contract = new Contract({});
  const { currentContractState } = await contract.initialState(
    runtime.createConstructorContext(null, wallet), 241n, 513n, true);
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

  assert.deepEqual(await invoke('inspect'), [241n, 513n, true]);
  await invoke('replacePosition', 19n, 97n, false);
  assert.deepEqual(await invoke('inspect'), [19n, 97n, false]);
  await assert.rejects(invoke('replacePosition', 19n, 65536n, false));
  assert.deepEqual(ledger(state).position, { total: 19n, details: { count: 97n, active: false } });
  console.log('Compact nested record Cell matched both values and rejected UInt16 overflow.');
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
