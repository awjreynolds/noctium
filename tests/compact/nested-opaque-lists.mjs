import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/nested-opaque-lists.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/);
const runtimeDirectory = resolve(runtimePath);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const sourceDirectory = dirname(fileURLToPath(import.meta.url));
const experiments = resolve(sourceDirectory, '../../build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'nested-opaque-lists-compact.'));
try {
  const generated = join(scratch, 'compact');
  execFileSync(compactc, ['--skip-zk', join(sourceDirectory, 'NestedOpaqueLists.compact'), generated]);
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');
  const { createCircuitContext, createConstructorContext, dummyContractAddress } =
    await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  const { Contract } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);

  const contract = new Contract({});
  const walletKey = '00'.repeat(32);
  const owner = Uint8Array.from({ length: 32 }, (_, index) => index + 1);
  const sibling = Uint8Array.from({ length: 32 }, (_, index) => index + 33);
  const deepOwner = new Uint8Array(32).fill(0x51);
  const groupA = new Uint8Array(32).fill(0x52);
  const groupB = new Uint8Array(32).fill(0x53);
  const missingOwner = new Uint8Array(32).fill(0x54);
  const missingGroup = new Uint8Array(32).fill(0x55);
  const address = dummyContractAddress();
  const initial = (await contract.initialState(createConstructorContext(null, walletKey))).currentContractState.data;
  const invoke = (entrypoint, state, ...args) => contract.circuits[entrypoint](createCircuitContext({
    circuitId: entrypoint, contractAddress: address,
    coinPublicKeyOrZswapState: walletKey, contractState: state, privateState: null,
  }), ...args);
  const nextState = ({ context }) => context.callContext.currentQueryContext.state;
  const maybe = async (state, key) => (await invoke('inspect', state, key)).result;
  const absence = { is_some: false, value: '' };
  const first = 'A\0夜\0B';
  const second = 'second';
  const siblingValue = 'sibling';
  const deepFirst = first;
  const deepSecond = 'deep-second';
  const deepSiblingValue = 'group-b';

  await assert.rejects(() => invoke('inspect', initial, owner));
  let state = nextState(await invoke('reset', initial, owner));
  state = nextState(await invoke('reset', state, sibling));
  assert.deepEqual(await maybe(state, owner), absence);
  state = nextState(await invoke('push', state, owner, first));
  state = nextState(await invoke('push', state, sibling, siblingValue));
  state = nextState(await invoke('push', state, owner, second));
  const afterPushes = {
    owner: await maybe(state, owner),
    sibling: await maybe(state, sibling),
  };
  assert.deepEqual(afterPushes, {
    owner: { is_some: true, value: second },
    sibling: { is_some: true, value: siblingValue },
  });

  state = nextState(await invoke('pop', state, owner));
  const afterPop = {
    owner: await maybe(state, owner),
    sibling: await maybe(state, sibling),
  };
  assert.deepEqual(afterPop, {
    owner: { is_some: true, value: first },
    sibling: { is_some: true, value: siblingValue },
  });

  state = nextState(await invoke('pop', state, owner));
  const afterFinalPop = {
    owner: await maybe(state, owner),
    sibling: await maybe(state, sibling),
  };
  assert.deepEqual(afterFinalPop, {
    owner: absence,
    sibling: { is_some: true, value: siblingValue },
  });

  let deepState = state;
  const maybeDeep = async (ledgerState, ownerKey, groupKey) =>
    (await invoke('inspectDeep', ledgerState, ownerKey, groupKey)).result;
  await assert.rejects(() => maybeDeep(deepState, missingOwner, groupA));
  deepState = nextState(await invoke('clearDeep', deepState, deepOwner, groupA));
  const emptyAfterClear = await maybeDeep(deepState, deepOwner, groupA);
  assert.deepEqual(emptyAfterClear, absence, 'clearing a new owner creates an empty group');
  await assert.rejects(() => maybeDeep(deepState, deepOwner, missingGroup));
  deepState = nextState(await invoke('clearDeep', deepState, deepOwner, groupB));

  deepState = nextState(await invoke('pushDeep', deepState, deepOwner, groupA, deepFirst));
  deepState = nextState(await invoke('pushDeep', deepState, deepOwner, groupB, deepSiblingValue));
  deepState = nextState(await invoke('pushDeep', deepState, deepOwner, groupA, deepSecond));
  const deepAfterPush = {
    groupA: await maybeDeep(deepState, deepOwner, groupA),
    groupB: await maybeDeep(deepState, deepOwner, groupB),
  };
  assert.deepEqual(deepAfterPush, {
    groupA: { is_some: true, value: deepSecond },
    groupB: { is_some: true, value: deepSiblingValue },
  });

  deepState = nextState(await invoke('popDeep', deepState, deepOwner, groupA));
  const deepAfterPop = {
    groupA: await maybeDeep(deepState, deepOwner, groupA),
    groupB: await maybeDeep(deepState, deepOwner, groupB),
  };
  assert.deepEqual(deepAfterPop, {
    groupA: { is_some: true, value: deepFirst },
    groupB: { is_some: true, value: deepSiblingValue },
  });

  deepState = nextState(await invoke('popDeep', deepState, deepOwner, groupA));
  const deepAfterFinalPop = {
    groupA: await maybeDeep(deepState, deepOwner, groupA),
    groupB: await maybeDeep(deepState, deepOwner, groupB),
  };
  assert.deepEqual(deepAfterFinalPop, {
    groupA: absence,
    groupB: { is_some: true, value: deepSiblingValue },
  });

  console.log(JSON.stringify({
    compact: compilerVersion,
    runtime: runtimePackage.version,
    owner: Buffer.from(owner).toString('hex'),
    sibling: Buffer.from(sibling).toString('hex'),
    absent: absence,
    first,
    second,
    siblingValue,
    afterPushes,
    afterPop,
    afterFinalPop,
    deep: {
      owner: Buffer.from(deepOwner).toString('hex'),
      groupA: Buffer.from(groupA).toString('hex'),
      groupB: Buffer.from(groupB).toString('hex'),
      missingOwner: Buffer.from(missingOwner).toString('hex'),
      missingGroup: Buffer.from(missingGroup).toString('hex'),
      first: deepFirst,
      second: deepSecond,
      siblingValue: deepSiblingValue,
      missingOwnerRejected: true,
      missingGroupRejected: true,
      emptyAfterClear,
      afterPush: deepAfterPush,
      afterPop: deepAfterPop,
      afterFinalPop: deepAfterFinalPop,
    },
  }));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
