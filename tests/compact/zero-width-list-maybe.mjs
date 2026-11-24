import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/zero-width-list-maybe.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/,
  `expected Compact 0.36.1 compiler, got ${compilerVersion}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'zero-width-list-maybe-'));

try {
  const source = join(projectRoot, 'tests/compact/ZeroWidthListMaybe.compact');
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

  const invoke = async (name, state) => {
    const context = createCircuitContext({
      circuitId: name,
      contractAddress: dummyContractAddress(),
      coinPublicKeyOrZswapState: walletKey,
      contractState: state,
      privateState: null,
    });
    const call = await contract.circuits[name](context);
    return [call.result, call.context.callContext.currentQueryContext.state];
  };

  const emptyBytes = new Uint8Array(0);
  const absent = { is_some: false, value: emptyBytes };
  let state = currentContractState.data;

  const [initialHead] = await invoke('head', state);
  assert.deepEqual(initialHead, absent, 'empty List head should be None with a zero-width value');

  [, state] = await invoke('push', state);
  const [presentHead] = await invoke('head', state);
  assert.deepEqual(presentHead, { is_some: true, value: emptyBytes },
    'pushing Bytes<0> should preserve Some and its empty typed value');

  [, state] = await invoke('pop', state);
  const [emptyAfterPop] = await invoke('head', state);
  assert.deepEqual(emptyAfterPop, absent, 'popping the populated List should restore None');

  const [, activeEmptyState] = await invoke('pop', state);
  await assert.rejects(invoke('head', activeEmptyState),
    'reading after popFront on an already empty List rejects');

  console.log(JSON.stringify({
    compact: compilerVersion,
    runtime: runtimePackage.version,
    empty: { is_some: initialHead.is_some, value: Array.from(initialHead.value) },
    populated: { is_some: presentHead.is_some, value: Array.from(presentHead.value) },
    afterPop: { is_some: emptyAfterPop.is_some, value: Array.from(emptyAfterPop.value) },
    emptyPopRead: 'rejected',
  }));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
