import assert from 'node:assert/strict';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';

const [generatedDirectory, runtimeDirectory] = process.argv.slice(2);
assert.ok(generatedDirectory && runtimeDirectory, 'pass generated output and Compact runtime directories');
const runtime = await import(pathToFileURL(resolve(runtimeDirectory, 'dist/index.js')).href);
assert.equal(runtime.versionString, '0.21.0');
const { createCircuitContext, createConstructorContext, dummyContractAddress } = runtime;
const { Contract } = await import(pathToFileURL(resolve(generatedDirectory, 'contract/index.js')).href);

const calls = [];
const contract = new Contract({
  inspect: ({ privateState }, payload, amount) => {
    calls.push({ payload, amount });
    const accepted = payload.count === 17n
      && payload.enabled === true
      && Buffer.from(payload.memo).equals(Buffer.from([0, 1, 2, 255]))
      && amount === 5n;
    return [privateState, accepted];
  },
});
const wallet = '00'.repeat(32);
const { currentContractState } = await contract.initialState(createConstructorContext(null, wallet));
const payload = { count: 17n, enabled: true, memo: Uint8Array.from([0, 1, 2, 255]) };
const amount = 5n;
const context = (contractState = currentContractState.data) => createCircuitContext({
  circuitId: 'inspectLimits',
  contractAddress: dummyContractAddress(),
  coinPublicKeyOrZswapState: wallet,
  contractState,
  privateState: null,
});

const result = await contract.circuits.inspectLimits(context(), payload, amount);
assert.equal(result.result, true);
assert.deepEqual(calls, [{ payload, amount }]);

const malformedContract = new Contract({
  inspect: ({ privateState }) => [privateState, 'true'],
});
await assert.rejects(
  malformedContract.circuits.inspectLimits(context(), payload, amount),
);

console.log('Compact 0.36.1 passed composite witness argument, disclosure, and malformed Boolean result checks');
