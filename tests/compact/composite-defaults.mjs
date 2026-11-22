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
const limits = { count: 0n, enabled: false, memo: new Uint8Array(4) };
assert.deepEqual(result.result, [
  limits,
  [limits, limits],
  { is_some: false, value: limits },
  { is_left: false, left: 0n, right: false },
]);
console.log('Compact 0.36.1 returned checked record, vector, Maybe and Either defaults');
