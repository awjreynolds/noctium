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
assert.equal(result.result[0], '');
assert.deepEqual([...result.result[1]], []);
console.log('Compact 0.36.1 returned both typed opaque defaults');
