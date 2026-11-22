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
const sample = { count: 17n, enabled: true, memo: Uint8Array.of(0, 1, 2, 255) };
const result = await contract.circuits.options(createCircuitContext({
  circuitId: 'options', contractAddress: dummyContractAddress(), contractState: currentContractState.data,
  privateState: null, coinPublicKeyOrZswapState: coinPublicKey,
}), sample);
assert.deepEqual(result.result, [
  { is_some: true, value: sample },
  { is_some: false, value: { count: 0n, enabled: false, memo: new Uint8Array(4) } },
]);
console.log('Compact 0.36.1 matched present and absent composite Maybe values');
