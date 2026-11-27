import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/sealed-record-cell.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
assert.match(execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim(),
  /^0\.36\.1 \(7fa3a117c/);
const runtimeDirectory = resolve(runtimePath);
const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
assert.equal(runtime.versionString, '0.21.0');

const fixtures = dirname(fileURLToPath(import.meta.url));
const experiments = resolve(fixtures, '../../build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'sealed-record-cell-'));
try {
  const source = join(fixtures, 'SealedRecordCell.compact');
  const generated = join(scratch, 'compact');
  execFileSync(compactc, ['--skip-zk', source, generated]);
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const { Contract, ledger } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const wallet = '00'.repeat(32);
  const contract = new Contract({});
  const expected = { amount: 241n, count: 513n, active: true };
  const { currentContractState } = await contract.initialState(
    runtime.createConstructorContext(null, wallet), expected.amount, expected.count, expected.active);
  const initial = currentContractState.data;
  const invoke = (circuitId, contractState) => contract.circuits[circuitId](
    runtime.createCircuitContext({
      circuitId,
      contractAddress: runtime.dummyContractAddress(),
      coinPublicKeyOrZswapState: wallet,
      contractState,
      privateState: null,
    }));
  assert.deepEqual(ledger(initial).position, expected);
  assert.equal(ledger(initial).marker, 0n);
  assert.deepEqual((await invoke('inspect', initial)).result, [241n, 513n, true]);
  const touched = await invoke('touch', initial);
  const after = touched.context.callContext.currentQueryContext.state;
  assert.deepEqual(ledger(after).position, expected);
  assert.equal(ledger(after).marker, 37n);

  const invalid = join(scratch, 'mutated.compact');
  writeFileSync(invalid, readFileSync(source, 'utf8') + `
export circuit overwrite(): [] {
  position = Position { amount: 1 as Uint<8>, count: 2 as Uint<16>, active: false };
}
`);
  const rejected = spawnSync(compactc, ['--skip-zk', invalid, join(scratch, 'rejected')],
    { encoding: 'utf8' });
  assert.ok(rejected.status !== null && rejected.status !== 0, 'sealed record mutation should reject');
  assert.match(`${rejected.stderr}\n${rejected.stdout}`, /\bsealed\b.*\b(position|ledger|field)\b|\bposition\b.*\bsealed\b/i);
  console.log('Seeded record [241, 513, true] preserved after marker 37. Record mutation rejected.');
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
