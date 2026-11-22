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

const coinPublicKey = '00'.repeat(32);
const contract = new Contract({});
const { currentContractState } = await contract.initialState(createConstructorContext(null, coinPublicKey));
const context = (id, state) => createCircuitContext({
  circuitId: id, contractAddress: dummyContractAddress(), contractState: state,
  privateState: null, coinPublicKeyOrZswapState: coinPublicKey,
});
const stateOf = (result) => result.context.callContext.currentQueryContext.state;
const text = 'é\0λ';
const bytes = Uint8Array.of(0, 1, 255);
const seeded = stateOf(await contract.circuits.seed(context('seed', currentContractState.data), text, bytes));

for (const enabled of [false, true]) {
  const result = await contract.circuits.clear(context(String(enabled), seeded), enabled);
  const expectedText = enabled ? '' : text;
  const expectedBytes = enabled ? [] : [...bytes];
  const stored = ledger(stateOf(result));
  assert.equal(stored.text, expectedText);
  assert.deepEqual([...stored.bytes], expectedBytes);
  assert.equal(result.result[0], expectedText);
  assert.deepEqual([...result.result[1]], expectedBytes);
}

console.log('Compact 0.36.1 matched both guarded opaque Cell resets and their typed returns');
