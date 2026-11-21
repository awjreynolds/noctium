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
const coinPublicKey = '00'.repeat(32);
const initial = await contract.initialState(createConstructorContext(null, coinPublicKey), 5n, 42n);
const before = initial.currentContractState.data;
const context = (circuitId) => createCircuitContext({
  circuitId, contractState: before, privateState: null,
  contractAddress: dummyContractAddress(), coinPublicKeyOrZswapState: coinPublicKey,
});
function checkMaps(state) {
  const view = ledger(state);
  assert.equal(view.entries.size(), 1n);
  assert.equal(view.entries.lookup(5n), 42n);
  assert.equal(view.emptyEntries.size(), 0n);
}
checkMaps(before);
assert.equal((await contract.circuits.get(context('get'), 5n)).result, 42n);
const touched = await contract.circuits.touch(context('touch'));
const after = touched.context.callContext.currentQueryContext.state;
assert.equal(ledger(after).marker, 37n);
checkMaps(after);
console.log('Compact 0.36.1 preserved the seeded and empty sealed Maps');
