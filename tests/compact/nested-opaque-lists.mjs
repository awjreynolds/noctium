import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
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
const scratch = join(experiments, '1237-nested-opaque-lists-compact');
rmSync(scratch, { recursive: true, force: true });
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
  }));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
