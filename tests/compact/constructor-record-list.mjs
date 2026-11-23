import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, rmdirSync, symlinkSync } from 'node:fs';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/constructor-record-list.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/,
  `expected pinned Compact 0.36.1 compiler, got ${compilerVersion}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0', 'expected pinned Compact runtime 0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/ConstructorRecordList.compact');
const experiments = join(projectRoot, 'build/experiments/886-constructor-record-list');
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
    runtime.createConstructorContext(null, walletKey), 11n, 22n, false,
  );
  let state = currentContractState.data;
  const ownerFirst = { owner: 11n, active: false };
  const ownerSecond = { owner: 22n, active: true };
  const absent = { is_some: false, value: { owner: 0n, active: false } };

  assert.deepEqual([...ledger(state).history], [ownerSecond, ownerFirst]);

  const invoke = async name => {
    const context = runtime.createCircuitContext({
      circuitId: name,
      contractAddress: runtime.dummyContractAddress(),
      coinPublicKeyOrZswapState: walletKey,
      contractState: state,
      privateState: null,
    });
    const call = await contract.circuits[name](context);
    return [call.result, call.context.callContext.currentQueryContext.state];
  };

  const [initialHead] = await invoke('head');
  assert.deepEqual(initialHead, { is_some: true, value: ownerSecond });

  [, state] = await invoke('pop');
  assert.deepEqual([...ledger(state).history], [ownerFirst]);
  const [nextHead] = await invoke('head');
  assert.deepEqual(nextHead, { is_some: true, value: ownerFirst });

  [, state] = await invoke('pop');
  assert.deepEqual([...ledger(state).history], []);
  const [emptyHead] = await invoke('head');
  assert.deepEqual(emptyHead, absent);

  console.log(JSON.stringify({
    fixture: 'ConstructorRecordList',
    compiler: compilerVersion,
    runtime: runtimePackage.version,
    constructor: [{ owner: '11', active: false }, { owner: '22', active: true }],
    heads: [
      { is_some: true, value: { owner: '22', active: true } },
      { is_some: true, value: { owner: '11', active: false } },
      { is_some: false, value: { owner: '0', active: false } },
    ],
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
  try {
    rmdirSync(experiments);
  } catch (error) {
    if (error.code !== 'ENOENT' && error.code !== 'ENOTEMPTY') throw error;
  }
}
