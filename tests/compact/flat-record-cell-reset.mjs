import assert from 'node:assert/strict';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';

const [generated] = process.argv.slice(2);
const runtime = process.env.NOCTIUM_COMPACT_RUNTIME_DIR;
assert.ok(generated && runtime, 'pass compiler output and set NOCTIUM_COMPACT_RUNTIME_DIR');
const { createCircuitContext, createConstructorContext, dummyContractAddress } = await import(
  pathToFileURL(resolve(runtime, 'dist/index.js')).href,
);
const { Contract, ledger } = await import(pathToFileURL(resolve(generated, 'contract/index.js')).href);

const contract = new Contract({});
const key = '00'.repeat(32);
const { currentContractState } = await contract.initialState(createConstructorContext(null, key));
const context = (circuitId, contractState) => createCircuitContext({
  circuitId, contractState, privateState: null,
  contractAddress: dummyContractAddress(), coinPublicKeyOrZswapState: key,
});
const defaults = { issued: 0n, spent: 0n };
const seed = { issued: 5n, spent: 42n };
assert.deepEqual(ledger(currentContractState.data).counters, defaults);
const seeded = await contract.circuits.seed(context('seed', currentContractState.data));
const state = seeded.context.callContext.currentQueryContext.state;
assert.deepEqual(ledger(state).counters, seed);
for (const enabled of [false, true]) {
  const call = await contract.circuits.guardedClear(context('guardedClear', state), enabled);
  const after = ledger(call.context.callContext.currentQueryContext.state);
  assert.equal(after.marker, 37n);
  assert.deepEqual(after.counters, enabled ? defaults : seed);
}
console.log('Compact 0.36.1 matched active and inactive flat record Cell reset');
