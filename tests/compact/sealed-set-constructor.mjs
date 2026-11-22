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

const contract = new Contract({});
const coinPublicKey = '00'.repeat(32);
const { currentContractState } = await contract.initialState(
  createConstructorContext(null, coinPublicKey), 17n,
);
const inspect = (key) => contract.circuits.inspect(createCircuitContext({
  circuitId: 'inspect', contractState: currentContractState.data, privateState: null,
  contractAddress: dummyContractAddress(), coinPublicKeyOrZswapState: coinPublicKey,
}), key);

assert.deepEqual((await inspect(17n)).result, [true, 1n, true]);
assert.deepEqual((await inspect(42n)).result, [false, 1n, true]);
console.log('Compact 0.36.1 deduplicated sealed Set constructor inserts and kept its neighbor empty');
