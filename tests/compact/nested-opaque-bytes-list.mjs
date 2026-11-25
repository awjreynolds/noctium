import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/nested-opaque-bytes-list.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/,
  `expected pinned Compact 0.36.1 compiler, got ${compilerVersion}`);
const runtimeDirectory = resolve(runtimePath);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0', 'expected pinned Compact runtime 0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'nested-opaque-bytes-list-compact.'));

try {
  const generated = join(scratch, 'compact');
  const source = join(dirname(fileURLToPath(import.meta.url)), 'NestedOpaqueBytesList.compact');
  execFileSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtimeUrl = pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href;
  const contractUrl = pathToFileURL(join(generated, 'contract/index.js')).href;
  const { createCircuitContext, createConstructorContext, dummyContractAddress } = await import(runtimeUrl);
  const { Contract } = await import(contractUrl);
  const contract = new Contract({});
  const wallet = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(createConstructorContext(null, wallet));
  const owner = new Uint8Array(32).fill(0x11);
  const sibling = new Uint8Array(32).fill(0x22);
  const missingOwner = new Uint8Array(32).fill(0x33);
  const siblingValue = Uint8Array.of(0x80, 0x00, 0xfe);
  const emptyValue = new Uint8Array();
  const binaryValue = Uint8Array.of(0x00, 0xff);
  const invoke = (state, entrypoint, ...args) => contract.circuits[entrypoint](createCircuitContext({
    circuitId: entrypoint,
    contractAddress: dummyContractAddress(),
    coinPublicKeyOrZswapState: wallet,
    contractState: state,
    privateState: null,
  }), ...args);
  const nextState = ({ context }) => context.callContext.currentQueryContext.state;
  const inspect = async (state, key) => (await invoke(state, 'inspect', key)).result;
  const jsonMaybe = maybe => ({ is_some: maybe.is_some, value: [...maybe.value] });
  const observe = async state => ({
    owner: jsonMaybe(await inspect(state, owner)),
    sibling: jsonMaybe(await inspect(state, sibling)),
  });
  const absent = { is_some: false, value: [] };
  const siblingSome = { is_some: true, value: [...siblingValue] };

  let state = currentContractState.data;
  await assert.rejects(() => inspect(state, missingOwner),
    'strict inspect rejects an owner with no initialized list');
  state = nextState(await invoke(state, 'clear', owner));
  state = nextState(await invoke(state, 'clear', sibling));
  state = nextState(await invoke(state, 'push', sibling, siblingValue));
  const afterClear = await observe(state);
  assert.deepEqual(afterClear, { owner: absent, sibling: siblingSome },
    'clear initializes an empty owner list and sibling data remains readable');

  state = nextState(await invoke(state, 'push', owner, emptyValue));
  const afterEmptyPush = await observe(state);
  assert.deepEqual(afterEmptyPush, {
    owner: { is_some: true, value: [] },
    sibling: siblingSome,
  }, 'an empty byte vector remains a present list entry');

  state = nextState(await invoke(state, 'push', owner, binaryValue));
  const afterBinaryPush = await observe(state);
  assert.deepEqual(afterBinaryPush, {
    owner: { is_some: true, value: [0x00, 0xff] },
    sibling: siblingSome,
  }, 'binary bytes preserve zeros and high bytes');

  state = nextState(await invoke(state, 'pop', owner));
  const afterFirstPop = await observe(state);
  assert.deepEqual(afterFirstPop, {
    owner: { is_some: true, value: [] },
    sibling: siblingSome,
  }, 'popping binary bytes exposes the present empty byte vector');

  state = nextState(await invoke(state, 'pop', owner));
  const afterFinalPop = await observe(state);
  assert.deepEqual(afterFinalPop, { owner: absent, sibling: siblingSome },
    'popping the final item leaves the owner list empty');

  console.log(JSON.stringify({
    compact: compilerVersion,
    runtime: runtimePackage.version,
    owner: Buffer.from(owner).toString('hex'),
    sibling: Buffer.from(sibling).toString('hex'),
    missingOwner: Buffer.from(missingOwner).toString('hex'),
    absent,
    siblingValue: [...siblingValue],
    afterClear,
    afterEmptyPush,
    afterBinaryPush,
    afterFirstPop,
    afterFinalPop,
    missingOwnerRejected: true,
  }));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
