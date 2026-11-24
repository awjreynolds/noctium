import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/opaque-lists.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/);
const runtimeDirectory = resolve(runtimePath);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const sourceDirectory = dirname(fileURLToPath(import.meta.url));
const experiments = resolve(sourceDirectory, '../../build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'opaque-lists-'));
try {
  const generated = join(scratch, 'compact');
  execFileSync(compactc, ['--skip-zk', join(sourceDirectory, 'OpaqueLists.compact'), generated]);
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');
  const { createCircuitContext, createConstructorContext, dummyContractAddress } =
    await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  const { Contract, ledger } =
    await import(pathToFileURL(join(generated, 'contract/index.js')).href);

  const contract = new Contract({});
  const walletKey = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(createConstructorContext(null, walletKey));
  const invoke = (entrypoint, state, ...args) => contract.circuits[entrypoint](createCircuitContext({
    circuitId: entrypoint, contractAddress: dummyContractAddress(),
    coinPublicKeyOrZswapState: walletKey, contractState: state, privateState: null,
  }), ...args);
  const nextState = ({ context }) => context.callContext.currentQueryContext.state;
  const inspect = async state => (await invoke('inspect', state)).result.map(({is_some, value}) =>
    [is_some, value]);
  const textBytes = value => Buffer.from(value, 'utf8').toString('hex');
  const byteHex = value => Buffer.from(value).toString('hex');
  const first = {text: 'first\0middle', bytes: Uint8Array.from([0, 23, 0, 17])};
  const second = {text: 'second\0middle', bytes: Uint8Array.from([0, 42, 0, 99])};
  const absent = [[false, ''], [false, new Uint8Array(0)]];
  const expected = value => [[true, value.text], [true, value.bytes]];
  const snapshot = state => {
    const view = ledger(state);
    return {
      texts: [...view.texts].map(textBytes),
      blobs: [...view.blobs].map(byteHex),
    };
  };

  const initial = currentContractState.data;
  assert.deepEqual(await inspect(initial), absent);
  let state = nextState(await invoke('push', initial, first.text, first.bytes));
  state = nextState(await invoke('push', state, second.text, second.bytes));
  const afterTwoPushes = snapshot(state);
  assert.deepEqual(afterTwoPushes, {
    texts: [textBytes(second.text), textBytes(first.text)],
    blobs: [byteHex(second.bytes), byteHex(first.bytes)],
  });
  assert.deepEqual(await inspect(state), expected(second));

  state = nextState(await invoke('pop', state));
  const afterFirstPop = snapshot(state);
  assert.deepEqual(afterFirstPop, {
    texts: [textBytes(first.text)], blobs: [byteHex(first.bytes)],
  });
  assert.deepEqual(await inspect(state), expected(first));

  state = nextState(await invoke('pop', state));
  assert.deepEqual(snapshot(state), {texts: [], blobs: []});
  assert.deepEqual(await inspect(state), absent);

  state = nextState(await invoke('pop', state));
  const afterEmptyPop = state.state.asArray().map(cell => cell.type());
  assert.deepEqual(afterEmptyPop, ['null', 'null']);
  await assert.rejects(() => inspect(state));

  await assert.rejects(() => invoke('push', initial, 'trailing\0', second.bytes), /not in normal form/);
  await assert.rejects(() => invoke('push', initial, second.text, Uint8Array.from([1, 2, 0])), /not in normal form/);

  console.log(JSON.stringify({
    compact: compilerVersion,
    runtime: runtimePackage.version,
    initial: absent.map(([present]) => present),
    afterTwoPushes,
    afterFirstPop,
    afterSecondPop: {heads: absent.map(([present]) => present), lists: {texts: [], blobs: []}},
    afterEmptyPop,
  }));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
