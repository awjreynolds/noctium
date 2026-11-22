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
const context = circuitId => createCircuitContext({
  circuitId, contractAddress: dummyContractAddress(),
  contractState: currentContractState.data, privateState: null, coinPublicKeyOrZswapState: coinPublicKey,
});
const left = { count: 17n, enabled: true, memo: Uint8Array.of(0, 1, 2, 255) };
const right = [true, false];

assert.deepEqual((await contract.circuits.choose(context('left'), true, left, right)).result,
  { is_left: true, left, right: [false, false] });
assert.deepEqual((await contract.circuits.choose(context('right'), false, left, right)).result,
  { is_left: false, left: { count: 0n, enabled: false, memo: new Uint8Array(4) }, right });
console.log('Compact 0.36.1 matched both composite Either arms');
