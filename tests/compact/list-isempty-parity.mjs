import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, rmdirSync, symlinkSync } from 'node:fs';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/list-isempty-parity.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/,
  `expected pinned Compact 0.36.1 compiler, got ${compilerVersion}`);
const runtimeDirectory = resolve(runtimePath);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(root, 'build/experiments/list-isempty-parity');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'run-'));
try {
  const generated = join(scratch, 'compact');
  const source = join(root, 'tests/compact/ListIsEmptyParity.compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], {
    cwd: root,
    encoding: 'utf8',
  });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');
  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  const { Contract, ledger } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  assert.equal(runtime.versionString, '0.21.0');

  const contract = new Contract({});
  const wallet = '00'.repeat(32);
  const owner = new Uint8Array(32).fill(1);
  const emptySpender = new Uint8Array(32).fill(2);
  const populatedSpender = new Uint8Array(32).fill(3);
  const missingOwner = new Uint8Array(32).fill(4);
  const missingSpender = new Uint8Array(32).fill(5);
  const { currentContractState } = await contract.initialState(
    runtime.createConstructorContext(null, wallet),
  );
  let state = currentContractState.data;
  const context = (circuitId, contractState) => runtime.createCircuitContext({
    circuitId,
    contractAddress: runtime.dummyContractAddress(),
    coinPublicKeyOrZswapState: wallet,
    contractState,
    privateState: null,
  });
  const invoke = async (name, ...args) => {
    const call = await contract.circuits[name](context(name, state), ...args);
    state = call.context.callContext.currentQueryContext.state;
    return call.result;
  };
  await invoke('seed', owner, emptySpender, populatedSpender);
  assert.equal(ledger(state).oneEmptyByte.length(), 1n);
  assert.equal(ledger(state).memos.lookup(owner).lookup(emptySpender).length(), 0n);
  assert.equal(ledger(state).memos.lookup(owner).lookup(populatedSpender).length(), 1n);
  const args = [owner, emptySpender, populatedSpender, missingOwner, missingSpender];
  const read = await invoke('inspect', ...args, false);
  assert.deepEqual(read, [true, false, true, false, false]);

  await assert.rejects(
    () => invoke('inspect', ...args, true),
    error => error?.isCompactError === true && error.message.includes('tried to idx'),
  );
  console.log(JSON.stringify({
    fixture: 'ListIsEmptyParity',
    compiler: compilerVersion,
    runtime: runtimePackage.version,
    emptyBytes0List: true,
    oneElementBytes0List: false,
    emptyRecordList: true,
    populatedRecordList: false,
    inactiveMissingPath: false,
    activeMissingPath: 'rejected by Compact 0.36.1 for absent map parent',
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
  try {
    rmdirSync(experiments);
  } catch (error) {
    if (error.code !== 'ENOENT' && error.code !== 'ENOTEMPTY') throw error;
  }
}
