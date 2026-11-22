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
const { currentContractState } = await contract.initialState(createConstructorContext(null, coinPublicKey), 5n, 17n);
const state = currentContractState.data;
assert.equal(ledger(state).total, 70005n);
const read = await contract.circuits.inspect(createCircuitContext({
  circuitId: 'inspect', contractState: state, privateState: null,
  contractAddress: dummyContractAddress(), coinPublicKeyOrZswapState: coinPublicKey,
}));
assert.deepEqual(read.result, [70005n, 2n, 42n]);
console.log('Compact 0.36.1 seeded and read the sealed Counter and List');
