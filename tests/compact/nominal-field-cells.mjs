import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/nominal-field-cells.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const runtimeDirectory = resolve(runtimePath);
assert.match(execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim(), /^0\.36\.1 \(7fa3a117c/);
assert.equal(JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8')).version, '0.21.0');

const source = fileURLToPath(new URL('NominalFieldCells.compact', import.meta.url));
const experiments = resolve(dirname(source), '../../build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'nominal-field-cells-'));
try {
  const generated = join(scratch, 'generated');
  execFileSync(compactc, ['--skip-zk', source, generated]);
  const link = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(link), { recursive: true });
  symlinkSync(runtimeDirectory, link, 'dir');

  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  const { Contract, ledger } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const contract = new Contract({});
  const wallet = '00'.repeat(32);
  const initial = await contract.initialState(runtime.createConstructorContext(null, wallet), 11n, 77n);
  const initialState = initial.currentContractState.data;
  assert.equal(ledger(initialState).balance, 11n);
  assert.equal(ledger(initialState).cap, 77n);

  for (const [enabled, expectedBalance] of [[false, 11n], [true, 22n]]) {
    const context = runtime.createCircuitContext({
      circuitId: 'update', contractAddress: runtime.dummyContractAddress(),
      coinPublicKeyOrZswapState: wallet, contractState: initialState, privateState: null,
    });
    const result = await contract.circuits.update(context, enabled, 9n, 13n, 23n);
    assert.deepEqual(result.result, [expectedBalance, 77n]);
    const after = ledger(result.context.callContext.currentQueryContext.state);
    assert.equal(after.balance, expectedBalance);
    assert.equal(after.cap, 77n);
  }

  const wrongAlias = join(scratch, 'wrong-alias.compact');
  const valid = readFileSync(source, 'utf8');
  const wrong = valid.replace('next + (raw as Amount)', 'other');
  assert.notEqual(wrong, valid);
  writeFileSync(wrongAlias, wrong);
  const rejected = spawnSync(compactc, ['--skip-zk', wrongAlias, join(scratch, 'invalid')], { encoding: 'utf8' });
  assert.notEqual(rejected.status, 0);
  assert.match(rejected.stderr + rejected.stdout, /incompatible|expected.*Amount|Count/);
  console.log('Pinned Compact matched the constructor, both Cell write outcomes, and alias rejection.');
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
