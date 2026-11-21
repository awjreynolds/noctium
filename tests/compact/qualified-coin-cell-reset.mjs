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
const coin = {
  nonce: new Uint8Array(32).fill(2),
  color: new Uint8Array(32).fill(1),
  value: 5n,
  mt_index: 42n,
};
const defaults = { nonce: new Uint8Array(32), color: new Uint8Array(32), value: 0n, mt_index: 0n };
assert.deepEqual(ledger(currentContractState.data).coinSlot, defaults);
const seeded = await contract.circuits.seed(context('seed', currentContractState.data), coin);
const state = seeded.context.callContext.currentQueryContext.state;
assert.equal(ledger(state).marker, 37n);
assert.deepEqual(ledger(state).coinSlot, coin);
for (const enabled of [false, true]) {
  const call = await contract.circuits.guardedClear(context('guardedClear', state), enabled);
  const after = ledger(call.context.callContext.currentQueryContext.state);
  assert.equal(after.marker, 37n);
  assert.deepEqual(after.coinSlot, enabled ? defaults : coin);
}
console.log('Compact 0.36.1 matched active and inactive qualified Coin Cell reset');
