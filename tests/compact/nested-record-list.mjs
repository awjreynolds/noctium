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

  const absent = {
    is_some: false,
    value: { memo: { first: 0n, active: false }, tag: 0n },
  };

  let uintState = currentContractState.data;
  const [initialUIntHead] = await invoke('head', uintState);
  assert.deepEqual(initialUIntHead, absent,
    'empty Uint<16> list head should return a typed zero');

  const firstUInt = { memo: { first: 513n, active: true }, tag: 17n };
  const secondUInt = { memo: { first: 65_535n, active: false }, tag: 23n };
  [, uintState] = await invoke('push', uintState, firstUInt);
  [, uintState] = await invoke('push', uintState, secondUInt);
  const [newestUIntHead] = await invoke('head', uintState);
  assert.deepEqual(newestUIntHead, { is_some: true, value: secondUInt },
    'head should return the newest Uint<16> nested record');

  [, uintState] = await invoke('pop', uintState);
  const [olderUIntHead] = await invoke('head', uintState);
  assert.deepEqual(olderUIntHead, { is_some: true, value: firstUInt },
    'one pop should reveal the first Uint<16> nested record');
  await assert.rejects(() => invoke('push', uintState, {
    memo: { first: 65_536n, active: true }, tag: 17n,
  }));

  let nativeState = currentContractState.data;
  const firstNative = { memo: { first: 11n, active: true }, tag: 101n };
  const secondNative = { memo: { first: 22n, active: false }, tag: 202n };
  const [initialNativeHead] = await invoke('headNative', nativeState);
  assert.deepEqual(initialNativeHead, absent, 'empty Native list head should be None');
  [, nativeState] = await invoke('pushNative', nativeState, firstNative);
  [, nativeState] = await invoke('pushNative', nativeState, secondNative);
  const [newestNativeHead] = await invoke('headNative', nativeState);
  assert.deepEqual(newestNativeHead, { is_some: true, value: secondNative },
    'Native and Bool nested records should retain their existing list behavior');
  [, nativeState] = await invoke('popNative', nativeState);
  const [olderNativeHead] = await invoke('headNative', nativeState);
  assert.deepEqual(olderNativeHead, { is_some: true, value: firstNative },
    'one Native list pop should reveal the first nested record');
  [, nativeState] = await invoke('popNative', nativeState);
  const [emptyNativeHead] = await invoke('headNative', nativeState);
  assert.deepEqual(emptyNativeHead, absent,
    'Native list head should be None after both records are popped');

  console.log('Compact 0.36.1 matched nested Uint<16> List defaults, pushFront, head, popFront, bounds, and the Native/Bool route');
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
