import assert from 'node:assert/strict';
import { createCircuitContext, createConstructorContext, dummyContractAddress } from '@midnight-ntwrk/compact-runtime';
import { Contract, ledger } from './compact/contract/index.js';

const blockCalls = [];
let blockOffset = 10n;
const emptyNativeMapCalls = [];
const contract = new Contract({
  iterationSeed: ({ privateState }) => [[...privateState, 'seed'], 7n],
  iterationBytes: ({ privateState }) => [[...privateState, 'bytes'], Uint8Array.from([4, 5])],
  iterationVisit: ({ privateState }, item) => [[...privateState, `visit:${item}`], item * 2n],
  emptyTupleItems: ({ privateState }) => {
    emptyNativeMapCalls.push('emptyTupleItems');
    return [privateState, []];
  },
  acceptEmptyNativeVector: ({ privateState }, values) => {
    emptyNativeMapCalls.push('acceptEmptyNativeVector');
    assert.deepEqual(values, []);
    return [privateState, 41n];
  },
  blockItems: ({ privateState }, seed) => {
    blockCalls.push(`items:${seed}`);
    return [privateState, [2n, 3n]];
  },
  blockOffset: ({ privateState }, seed) => {
    blockCalls.push(`offset:${seed}`);
    return [privateState, blockOffset];
  },
});
const wallet = '00'.repeat(32);
const { currentContractState } = await contract.initialState(createConstructorContext([], wallet));
const { result, context } = await contract.circuits.update(createCircuitContext({
  circuitId: 'update', contractAddress: dummyContractAddress(), coinPublicKeyOrZswapState: wallet,
  contractState: currentContractState.data, privateState: [],
}), 3n);
const total = ledger(context.callContext.currentQueryContext.state).total;
assert.equal(result, 31n);
assert.equal(total, 31n);
assert.deepEqual(context.callContext.currentPrivateState, ['seed', 'bytes', 'visit:4', 'visit:5']);
console.log(JSON.stringify({ result: result.toString(), total: total.toString(), order: context.callContext.currentPrivateState }));

const runBlock = () => contract.circuits.runBlock(createCircuitContext({
  circuitId: 'runBlock', contractAddress: dummyContractAddress(), coinPublicKeyOrZswapState: wallet,
  contractState: currentContractState.data, privateState: [],
}), 7n);
assert.deepEqual((await runBlock()).result, [12n, 13n, 25n]);
assert.deepEqual(blockCalls.splice(0), ['items:7', 'offset:8']);

const emptyNativeMap = await contract.circuits.emptyNativeMap(createCircuitContext({
  circuitId: 'emptyNativeMap', contractAddress: dummyContractAddress(), coinPublicKeyOrZswapState: wallet,
  contractState: currentContractState.data, privateState: [],
}));
assert.equal(emptyNativeMap.result, 41n);
assert.deepEqual(emptyNativeMapCalls, ['emptyTupleItems', 'acceptEmptyNativeVector']);
console.log(JSON.stringify({ result: emptyNativeMap.result.toString(), order: emptyNativeMapCalls }));

blockOffset = 40n;
await assert.rejects(async () => runBlock(), /fold assertion/);
assert.deepEqual(blockCalls, ['items:7', 'offset:8']);
