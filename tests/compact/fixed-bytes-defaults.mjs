import assert from 'node:assert/strict';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';

const [generated] = process.argv.slice(2);
const runtime = process.env.NOCTIUM_COMPACT_RUNTIME_DIR;
assert.ok(generated && runtime, 'pass compiler output and set NOCTIUM_COMPACT_RUNTIME_DIR');
const { createCircuitContext, createConstructorContext, dummyContractAddress } = await import(
  pathToFileURL(resolve(runtime, 'dist/index.js')).href,
);
const { Contract } = await import(pathToFileURL(resolve(generated, 'contract/index.js')).href);

const coinPublicKey = '00'.repeat(32);
const contract = new Contract({});
const { currentContractState } = await contract.initialState(createConstructorContext(null, coinPublicKey));
const result = await contract.circuits.defaults(createCircuitContext({
  circuitId: 'defaults', contractAddress: dummyContractAddress(), contractState: currentContractState.data,
  privateState: null, coinPublicKeyOrZswapState: coinPublicKey,
}));
for (const [index, length] of [0, 4, 32].entries()) {
  assert.deepEqual([...result.result[index]], Array(length).fill(0));
}
console.log('Compact 0.36.1 returned zero-filled defaults at widths 0, 4 and 32');

const { result: readable } = await contract.circuits.readableDefaults(createCircuitContext({
  circuitId: 'readableDefaults', contractAddress: dummyContractAddress(), contractState: currentContractState.data,
  privateState: null, coinPublicKeyOrZswapState: coinPublicKey,
}));
assert.deepEqual(readable, [0n, false, 0n, new Uint8Array(0), new Uint8Array(3),
  new Uint8Array(32), [0n, 0n], []]);
