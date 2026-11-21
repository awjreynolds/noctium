import assert from 'node:assert/strict';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';

const [generatedDirectory] = process.argv.slice(2);
const runtimeDirectory = process.env.NOCTIUM_COMPACT_RUNTIME_DIR;
assert.ok(generatedDirectory && runtimeDirectory, 'pass compiler output and set NOCTIUM_COMPACT_RUNTIME_DIR');
const { createCircuitContext, createConstructorContext, dummyContractAddress } = await import(
  pathToFileURL(resolve(runtimeDirectory, 'dist/index.js')).href,
);
const { Contract, ledger } = await import(
  pathToFileURL(resolve(generatedDirectory, 'contract/index.js')).href,
);

const contract = new Contract({});
const walletKey = '00'.repeat(32);
const { currentContractState } = await contract.initialState(createConstructorContext(null, walletKey));
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

let [result, state] = await invoke('seed', currentContractState.data, 1n, 19n);
assert.deepEqual(result, [true, 1n, 19n]);
[result, state] = await invoke('seed', state, 2n, 23n);
assert.deepEqual(result, [true, 2n, 23n]);
[result, state] = await invoke('clearMap', state, 1n);
assert.deepEqual(result, [false, 0n]);

const clearedValues = ledger(state).values;
assert.equal(clearedValues.size(), 0n);
assert.equal(clearedValues.member(1n), false);
assert.equal(clearedValues.member(2n), false);

const [, nestedState] = await invoke(
  'seedNested', state, 10n, 1n, 19n, 2n, 23n, 20n, 3n, 31n,
);
let nestedValues = ledger(nestedState).nestedValues;
assert.equal(nestedValues.size(), 2n);
assert.equal(nestedValues.lookup(10n).size(), 2n);
assert.equal(nestedValues.lookup(10n).lookup(1n), 19n);
assert.equal(nestedValues.lookup(10n).lookup(2n), 23n);
assert.equal(nestedValues.lookup(20n).size(), 1n);
assert.equal(nestedValues.lookup(20n).lookup(3n), 31n);

const [, inactiveMissingState] = await invoke('clearInner', nestedState, 30n, false);
const assertNestedValues = (values, hasMissingParent = false) => {
  assert.equal(values.size(), hasMissingParent ? 3n : 2n);
  assert.equal(values.member(10n), true);
  assert.equal(values.lookup(10n).size(), 2n);
  assert.equal(values.lookup(10n).lookup(1n), 19n);
  assert.equal(values.lookup(10n).lookup(2n), 23n);
  assert.equal(values.member(20n), true);
  assert.equal(values.lookup(20n).size(), 1n);
  assert.equal(values.lookup(20n).lookup(3n), 31n);
  assert.equal(values.member(30n), hasMissingParent);
  if (hasMissingParent) assert.equal(values.lookup(30n).size(), 0n);
};
assertNestedValues(ledger(inactiveMissingState).nestedValues);
const [, activeMissingState] = await invoke('clearInner', nestedState, 30n, true);
assertNestedValues(ledger(activeMissingState).nestedValues, true);
const [, inactiveExistingState] = await invoke('clearInner', activeMissingState, 10n, false);
assertNestedValues(ledger(inactiveExistingState).nestedValues, true);

const [, resetState] = await invoke('clearInner', inactiveExistingState, 10n, true);
nestedValues = ledger(resetState).nestedValues;
assert.equal(nestedValues.size(), 3n, 'reset retains all initialized parent entries');
assert.equal(nestedValues.member(10n), true, 'reset retains the selected parent');
assert.equal(nestedValues.lookup(10n).size(), 0n, 'reset empties the selected inner Map');
assert.equal(nestedValues.member(20n), true, 'reset preserves the sibling parent');
assert.equal(nestedValues.lookup(20n).size(), 1n);
assert.equal(nestedValues.lookup(20n).lookup(3n), 31n);
assert.equal(nestedValues.member(30n), true, 'active reset initializes a missing parent');
assert.equal(nestedValues.lookup(30n).size(), 0n);
console.log('Compact 0.36.1 matched root and nested Map reset, retaining initialized empty parents and sibling state');
