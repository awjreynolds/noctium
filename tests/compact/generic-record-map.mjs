import assert from 'node:assert/strict';
import {execFileSync, spawnSync} from 'node:child_process';
import {dirname, join, resolve} from 'node:path';
import {fileURLToPath, pathToFileURL} from 'node:url';
import {mkdirSync, mkdtempSync, readFileSync, rmSync, rmdirSync, symlinkSync} from 'node:fs';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node generic-record-map.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], {encoding: 'utf8'}).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/, `unexpected Compact compiler: ${compilerVersion}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/GenericRecordMap.compact');
const experiments = join(projectRoot, 'build/experiments/913-generic-record-map');
mkdirSync(experiments, {recursive: true});
const scratch = mkdtempSync(join(experiments, 'run-'));

try {
  const generated = join(scratch, 'compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], {
    cwd: projectRoot,
    encoding: 'utf8',
  });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), {recursive: true});
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  assert.equal(runtime.versionString, '0.21.0');
  const {Contract, ledger} = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const contract = new Contract({});
  const walletKey = '00'.repeat(32);
  const {currentContractState} = await contract.initialState(
    runtime.createConstructorContext(null, walletKey),
  );
  const receipt = (amount, active) => ({amount: BigInt(amount), active});
  const run = async (circuitId, state, ...args) => {
    const call = await contract.circuits[circuitId](runtime.createCircuitContext({
      circuitId,
      contractAddress: runtime.dummyContractAddress(),
      coinPublicKeyOrZswapState: walletKey,
      contractState: state,
      privateState: null,
    }), ...args);
    return [call.result, call.context.callContext.currentQueryContext.state];
  };
  const readMap = state => ledger(state).receiptMap_values;
  const initial = currentContractState.data;
  assert.equal(readMap(initial).size(), 0n);

  let [, state] = await run('put', initial, true, 11n, receipt(101, true));
  [, state] = await run('put', state, true, 12n, receipt(303, true));
  let entries = readMap(state);
  assert.equal(entries.size(), 2n);
  assert.equal(entries.member(11n), true);
  assert.equal(entries.member(12n), true);
  assert.deepEqual(entries.lookup(11n), receipt(101, true));
  assert.deepEqual(entries.lookup(12n), receipt(303, true));
  assert.deepEqual((await run('lookup', state, 11n))[0], receipt(101, true));
  assert.deepEqual((await run('lookup', state, 12n))[0], receipt(303, true));

  const [, afterDisabled] = await run('put', state, false, 11n, receipt(999, false));
  entries = readMap(afterDisabled);
  assert.equal(entries.size(), 2n);
  assert.deepEqual(entries.lookup(11n), receipt(101, true));
  assert.deepEqual(entries.lookup(12n), receipt(303, true));

  const [, afterOverwrite] = await run('put', afterDisabled, true, 11n, receipt(202, false));
  entries = readMap(afterOverwrite);
  assert.equal(entries.size(), 2n);
  assert.deepEqual(entries.lookup(11n), receipt(202, false));
  assert.deepEqual(entries.lookup(12n), receipt(303, true));
  assert.deepEqual((await run('lookup', afterOverwrite, 11n))[0], receipt(202, false));
  assert.deepEqual((await run('lookup', afterOverwrite, 12n))[0], receipt(303, true));
  await assert.rejects(() => run('lookup', afterOverwrite, 13n));

  console.log(`Compact ${compilerVersion} preserved guarded record Map insertions, overwrote key 11, and rejected missing key 13`);
} finally {
  rmSync(scratch, {recursive: true, force: true});
  try {
    rmdirSync(experiments);
  } catch (error) {
    if (error.code !== 'ENOENT' && error.code !== 'ENOTEMPTY') throw error;
  }
}
