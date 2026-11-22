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
const wallet = '00'.repeat(32);
const { currentContractState } = await contract.initialState(createConstructorContext(null, wallet));
const { result } = await contract.circuits.inspect(createCircuitContext({
  circuitId: 'inspect', contractAddress: dummyContractAddress(), coinPublicKeyOrZswapState: wallet,
  contractState: currentContractState.data, privateState: null,
}));
const edwardsIdentity = { x: 0n, y: 1n };
const weierstrassIdentity = { x: 0n, y: 0n, identity: true };
assert.deepEqual(result, [
  0n, edwardsIdentity,
  0n, 0n, weierstrassIdentity,
  0n, 0n, weierstrassIdentity,
  0n, 0n, edwardsIdentity,
]);
