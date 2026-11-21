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
console.log('Compact 0.36.1 cleared a two-entry Map to an empty final state');
