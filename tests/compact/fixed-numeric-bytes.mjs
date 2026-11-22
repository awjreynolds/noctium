import assert from 'node:assert/strict';
import { createCircuitContext, createConstructorContext, dummyContractAddress } from '@midnight-ntwrk/compact-runtime';
import { Contract } from './compact/contract/index.js';

const contract = new Contract({});
const wallet = '00'.repeat(32);
const { currentContractState } = await contract.initialState(createConstructorContext(null, wallet));
const invoke = (name, value) => contract.circuits[name](createCircuitContext({
  circuitId: name,
  contractAddress: dummyContractAddress(),
  coinPublicKeyOrZswapState: wallet,
  contractState: currentContractState.data,
  privateState: null,
}), value);

for (const name of ['fieldOne', 'uintOne']) {
  assert.deepEqual((await invoke(name, 255n)).result, Uint8Array.of(255));
  await assert.rejects(invoke(name, 256n), /does not fit into 1 bytes/);
}
assert.deepEqual((await invoke('field31', (1n << 248n) - 1n)).result, new Uint8Array(31).fill(255));
await assert.rejects(invoke('field31', 1n << 248n), /does not fit into 31 bytes/);

const { result: wide } = await invoke('fieldWide', 0x0201n);
for (const [index, size] of [32, 33, 64].entries()) {
  assert.deepEqual(wide[index], Uint8Array.from([1, 2, ...Array(size - 2).fill(0)]));
}
