import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, rmdirSync, symlinkSync } from 'node:fs';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/generic-record-cell.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/,
  `expected pinned Compact 0.36.1 compiler, got ${compilerVersion}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0', 'expected pinned Compact runtime 0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/GenericRecordCell.compact');
const experiments = join(projectRoot, 'build/experiments/893-generic-record-cell');
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
  const readCell = state => ledger(state).cell_value;
  const expected = (issued, spent) => ({ issued: BigInt(issued), spent: BigInt(spent) });

  let state = currentContractState.data;
  assert.deepEqual(readCell(state), expected(5, 42));

  let [inspected] = await run('inspect', state);
  assert.deepEqual(inspected, expected(5, 42));

  let [disabledResult, afterDisabled] = await run('update', state, false, 11n, 13n);
  assert.deepEqual(disabledResult, expected(5, 42));
  assert.deepEqual(readCell(afterDisabled), expected(5, 42));
  state = afterDisabled;

  let [updatedResult, afterUpdate] = await run('update', state, true, 8n, 99n);
  assert.deepEqual(updatedResult, expected(8, 99));
  assert.deepEqual(readCell(afterUpdate), expected(8, 99));
  state = afterUpdate;

  [inspected, state] = await run('inspect', state);
  assert.deepEqual(inspected, expected(8, 99));
  assert.deepEqual(readCell(state), expected(8, 99));

  console.log(JSON.stringify({
    fixture: 'GenericRecordCell',
    compiler: compilerVersion,
    runtime: runtimePackage.version,
    initial: { issued: '5', spent: '42' },
    disabledWrite: { inputs: { enabled: false, nextIssued: '11', nextSpent: '13' }, result: { issued: '5', spent: '42' } },
    enabledWrite: { result: { issued: '8', spent: '99' } },
    reread: { issued: '8', spent: '99' },
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
  try {
    rmdirSync(experiments);
  } catch (error) {
    if (error.code !== 'ENOENT' && error.code !== 'ENOTEMPTY') throw error;
  }
}
