import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/nested-record-list.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/,
  `expected pinned Compact 0.36.1 compiler, got ${compilerVersion}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0', 'expected pinned Compact runtime 0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'nested-record-list-'));

try {
  const source = join(projectRoot, 'tests/compact/NestedRecordList.compact');
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
  const { createCircuitContext, createConstructorContext, dummyContractAddress } = await import(runtimeUrl);
  const { Contract } = await import(contractUrl);
  const contract = new Contract({});
  const walletKey = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(
    createConstructorContext(null, walletKey),
  );

  const invoke = async (name, state, ...args) => {
    const context = createCircuitContext({
      circuitId: name,
      contractAddress: dummyContractAddress(),
      coinPublicKeyOrZswapState: walletKey,
      contractState: state,
      privateState: null,
    });
    const call = await contract.circuits[name](context, ...args);
    return [call.result, call.context.callContext.currentQueryContext.state];
  };

  const first = { memo: { first: 11n, active: true }, tag: 101n };
  const second = { memo: { first: 22n, active: false }, tag: 202n };
  const absent = {
    is_some: false,
    value: { memo: { first: 0n, active: false }, tag: 0n },
  };

  let state = currentContractState.data;
  const [initialHead] = await invoke('head', state);
  assert.deepEqual(initialHead, absent, 'empty list head should be None');

  [, state] = await invoke('push', state, first);
  [, state] = await invoke('push', state, second);
  const [newestHead] = await invoke('head', state);
  assert.deepEqual(newestHead, { is_some: true, value: second },
    'head should return the second pushed Envelope');

  [, state] = await invoke('pop', state);
  const [olderHead] = await invoke('head', state);
  assert.deepEqual(olderHead, { is_some: true, value: first },
    'one pop should reveal the first pushed Envelope');

  [, state] = await invoke('pop', state);
  const [emptyHead] = await invoke('head', state);
  assert.deepEqual(emptyHead, absent, 'head should be None after both records are popped');

  console.log('Compact 0.36.1 matched nested Envelope List pushFront, head, popFront and empty Maybe behavior');
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
