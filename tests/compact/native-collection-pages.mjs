import assert from 'node:assert/strict';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';

const [generatedDirectory] = process.argv.slice(2);
const runtimeDirectory = process.env.NOCTIUM_COMPACT_RUNTIME_DIR;
assert.ok(generatedDirectory && runtimeDirectory, 'pass the compiler output and set NOCTIUM_COMPACT_RUNTIME_DIR');
const { createCircuitContext, createConstructorContext, dummyContractAddress } = await import(
  pathToFileURL(resolve(runtimeDirectory, 'dist/index.js')).href,
);
const { Contract, ledger } = await import(
  pathToFileURL(resolve(generatedDirectory, 'contract/index.js')).href,
);
const contract = new Contract({});
const walletKey = '00'.repeat(32);
const { currentContractState } = await contract.initialState(createConstructorContext(null, walletKey));
const call = async (state, entrypoint, ...args) => {
  const context = createCircuitContext({
    circuitId: entrypoint,
    contractAddress: dummyContractAddress(),
    coinPublicKeyOrZswapState: walletKey,
    contractState: state,
    privateState: null,
  });
  const result = await contract.circuits[entrypoint](context, ...args);
  return result.context.callContext.currentQueryContext.state;
};

const flags = [[10n, true], [2n, false], [1n, true]];
const members = [9, 1, 4];
for (const reverse of [false, true]) {
  let state = currentContractState.data;
  for (const [key, value] of reverse ? [...flags].reverse() : flags) {
    state = await call(state, 'put', key, value);
  }
  for (const value of reverse ? [...members].reverse() : members) {
    state = await call(state, 'add', new Uint8Array(32).fill(value));
  }
  const snapshot = ledger(state);
  // Compact iteration order is outside the comparison. Compare canonical contents.
  const actualFlags = [...snapshot.flags].sort(([a], [b]) => a < b ? -1 : a > b ? 1 : 0);
  const actualMembers = [...snapshot.members].sort((a, b) => Buffer.compare(a, b));
  assert.deepEqual(actualFlags, [[1n, true], [2n, false], [10n, true]]);
  assert.deepEqual(actualMembers, [1, 4, 9].map(value => new Uint8Array(32).fill(value)));
}
let listState = currentContractState.data;
assert.deepEqual([...ledger(listState).values], []);
for (const value of [33n, 22n, 11n]) {
  listState = await call(listState, 'prepend', value);
}
assert.deepEqual([...ledger(listState).values], [11n, 22n, 33n]);

const owner = new Uint8Array(32).fill(7);
let nestedState = currentContractState.data;
for (const [key, value] of flags) {
  nestedState = await call(nestedState, 'putNested', owner, key, value);
}
for (const value of members) {
  nestedState = await call(nestedState, 'addNested', owner, new Uint8Array(32).fill(value));
}
for (const value of [33n, 22n, 11n]) {
  nestedState = await call(nestedState, 'prependNested', owner, value);
}
const nested = ledger(nestedState);
const nestedFlags = [...nested.nestedFlags.lookup(owner)].sort(([a], [b]) => a < b ? -1 : a > b ? 1 : 0);
const nestedMembers = [...nested.nestedMembers.lookup(owner)].sort((a, b) => Buffer.compare(a, b));
assert.deepEqual(nestedFlags, [[1n, true], [2n, false], [10n, true]]);
assert.deepEqual(nestedMembers, [1, 4, 9].map(value => new Uint8Array(32).fill(value)));
assert.deepEqual([...nested.nestedValues.lookup(owner)], [11n, 22n, 33n]);
const mapped = { c1x: 1n, c1y: 2n, c2x: 3n, c2y: 4n };
const listed = { c1x: 5n, c1y: 6n, c2x: 7n, c2y: 8n };
const recordState = await call(currentContractState.data, 'seedRecords', owner, mapped, listed);
const records = ledger(recordState);
assert.deepEqual([...records.records], [[owner, mapped]]);
assert.deepEqual([...records.recordList], [listed]);
console.log('Compact 0.36.1 matched scalar and checked record collection contents');
