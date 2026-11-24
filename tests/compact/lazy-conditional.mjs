import assert from 'node:assert/strict';
import { createCircuitContext, createConstructorContext, dummyContractAddress } from '@midnight-ntwrk/compact-runtime';
import { Contract } from './compact/contract/index.js';

const calls = [];
const contract = new Contract({
  loadLeft: ({ privateState }) => {
    calls.push('left');
    return [privateState, { amount: 7n, extra: { enabled: true } }];
  },
  loadRight: ({ privateState }) => {
    calls.push('right');
    return [privateState, { amount: 9n, extra: { enabled: false } }];
  },
  afterChoice: ({ privateState }, expected) => {
    calls.push(['tail', expected]);
    return [privateState, []];
  },
});
const wallet = '00'.repeat(32);
const { currentContractState } = await contract.initialState(createConstructorContext(null, wallet));
const context = (circuitId) => createCircuitContext({
  circuitId,
  contractAddress: dummyContractAddress(),
  coinPublicKeyOrZswapState: wallet,
  contractState: currentContractState.data,
  privateState: null,
});
const invoke = (thenCondition, elseCondition) =>
  contract.circuits.branches(context('branches'), thenCondition, elseCondition, 3n);

assert.deepEqual((await invoke(false, true)).result, [true, true]);
await assert.rejects(invoke(true, true));
await assert.rejects(invoke(false, false));

const branchChoice = (choice, expected) => contract.circuits.branchChoice(
  context('branchChoice'), choice, expected,
);
assert.deepEqual((await branchChoice(true, 7n)).result, [7n, true]);
assert.deepEqual(calls.splice(0), ['left', ['tail', 7n]]);
assert.deepEqual((await branchChoice(false, 9n)).result, [9n, false]);
assert.deepEqual(calls.splice(0), ['right', ['tail', 9n]]);
await assert.rejects(branchChoice(true, 9n));
assert.deepEqual(calls, ['left']);

calls.length = 0;
const branchShadowing = (choice, expected) => contract.circuits.branchShadowing(
  context('branchShadowing'), choice, expected,
);
assert.deepEqual((await branchShadowing(true, 7n)).result, [7n, true]);
assert.deepEqual(calls.splice(0), ['left', ['tail', 7n]]);
assert.deepEqual((await branchShadowing(false, 8n)).result, [8n, false]);
assert.deepEqual(calls.splice(0), ['right', ['tail', 8n]]);
await assert.rejects(branchShadowing(true, 9n));
assert.deepEqual(calls, ['left']);
