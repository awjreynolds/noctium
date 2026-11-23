import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdirSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/list-pop-front.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/, `expected pinned Compact 0.36.1 compiler, got ${compilerVersion}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0', 'expected pinned Compact runtime 0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/ListPopFront.compact');
const scratch = join(projectRoot, 'build/experiments/749-compact');
rmSync(scratch, { recursive: true, force: true });
mkdirSync(scratch, { recursive: true });

try {
  const generated = join(scratch, 'generated');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  const { Contract } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const contract = new Contract({});
  const walletKey = '00'.repeat(32);
  const owner = new Uint8Array(32).fill(7);
  const firstMemo = Uint8Array.from({ length: 128 }, (_, index) => index);
  const secondMemo = Uint8Array.from({ length: 128 }, (_, index) => index + 128);
  const zeroMemo = new Uint8Array(128);
  const { currentContractState } = await contract.initialState(runtime.createConstructorContext(null, walletKey));
  const invoke = async (name, state, ...args) => {
    const context = runtime.createCircuitContext({
      circuitId: name,
      contractAddress: runtime.dummyContractAddress(),
      coinPublicKeyOrZswapState: walletKey,
      contractState: state,
      privateState: null,
    });
    const call = await contract.circuits[name](context, ...args);
    return [call.result, call.context.callContext.currentQueryContext.state];
  };
  const expectStandalone = async (state, length, present, value) => {
    const [result] = await invoke('inspectStandalone', state);
    assert.deepEqual(result, [length, present, value]);
  };
  const expectNested = async (state, length, present, value) => {
    const [result] = await invoke('inspectNested', state, owner);
    assert.deepEqual(result, [length, present, value]);
  };
  const ledgerFields = (state) => {
    const fields = state.state.asArray();
    assert.ok(fields, 'expected a two-field contract state array');
    assert.equal(fields.length, 2);
    return fields;
  };
  const nestedEntries = (state) => {
    const nestedMap = ledgerFields(state)[1].asMap();
    assert.ok(nestedMap, 'expected nested ledger field to be a Map');
    return nestedMap.keys().map((key) => nestedMap.get(key).type());
  };

  const [, initializedRoot] = await invoke('initializeStandalone', currentContractState.data);
  const initialRootSummary = ledgerFields(initializedRoot)[0].toString(false);
  const initialNestedSummary = ledgerFields(initializedRoot)[1].toString(false);
  const [, inactiveRoot] = await invoke('popStandalone', initializedRoot, false);
  assert.equal(inactiveRoot.state.toString(false), initializedRoot.state.toString(false));
  await expectStandalone(inactiveRoot, 0n, false, 0n);
  const [, inactiveAbsentNested] = await invoke('popNested', initializedRoot, owner, false);
  assert.equal(inactiveAbsentNested.state.toString(false), initializedRoot.state.toString(false));
  const [absent] = await invoke('hasNested', inactiveAbsentNested, owner);
  assert.equal(absent, false);

  const [, activeEmptyRoot] = await invoke('popStandalone', initializedRoot, true);
  const [rootAfterPop, nestedAfterRootPop] = ledgerFields(activeEmptyRoot);
  assert.equal(rootAfterPop.type(), 'null');
  assert.equal(nestedAfterRootPop.toString(false), initialNestedSummary);
  await assert.rejects(invoke('inspectStandalone', activeEmptyRoot), /tried to idx/);

  const [, initializedEmpty] = await invoke('initializeNested', initializedRoot, owner);
  assert.deepEqual(nestedEntries(initializedEmpty), ['array']);
  await expectNested(initializedEmpty, 0n, false, zeroMemo);
  const rootBeforeNestedPop = ledgerFields(initializedEmpty)[0].toString(false);
  const [, activeEmptyNested] = await invoke('popNested', initializedEmpty, owner, true);
  const [rootAfterNestedPop] = ledgerFields(activeEmptyNested);
  assert.equal(rootAfterNestedPop.toString(false), rootBeforeNestedPop);
  assert.deepEqual(nestedEntries(activeEmptyNested), ['null']);
  await assert.rejects(invoke('inspectNested', activeEmptyNested, owner), /tried to idx/);
  await assert.rejects(invoke('popNested', initializedRoot, owner, true), /tried to idx/);

  let [, populated] = await invoke('pushBoth', initializedEmpty, owner, 5n, firstMemo);
  [, populated] = await invoke('pushBoth', populated, owner, 300n, secondMemo);
  const [, rootPopped] = await invoke('popStandalone', populated, true);
  await expectStandalone(rootPopped, 1n, true, 5n);
  await expectNested(rootPopped, 2n, true, secondMemo);
  const [, nestedPopped] = await invoke('popNested', rootPopped, owner, true);
  await expectStandalone(nestedPopped, 1n, true, 5n);
  await expectNested(nestedPopped, 1n, true, firstMemo);

  console.log('Compact 0.36.1 List.popFront: active empty pops write Null, guarded calls preserve state, and nonempty pops remove one item');
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
