import assert from 'node:assert/strict';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';

const [generated] = process.argv.slice(2);
const runtime = process.env.NOCTIUM_COMPACT_RUNTIME_DIR;
assert.ok(generated && runtime, 'pass compiler output and set NOCTIUM_COMPACT_RUNTIME_DIR');
const { createCircuitContext, createConstructorContext, dummyContractAddress, versionString } = await import(
  pathToFileURL(resolve(runtime, 'dist/index.js')).href,
);
assert.equal(versionString, '0.21.0');
const { Contract, ledger } = await import(pathToFileURL(resolve(generated, 'contract/index.js')).href);

const wallet = '00'.repeat(32);
const contract = new Contract({});
const { currentContractState } = await contract.initialState(createConstructorContext(null, wallet));
const context = () => createCircuitContext({
  circuitId: 'echo',
  contractAddress: dummyContractAddress(),
  coinPublicKeyOrZswapState: wallet,
  contractState: currentContractState.data,
  privateState: null,
});
const zero = { count: 0n, enabled: false, memo: new Uint8Array(4) };
const nonzero = { count: 17n, enabled: true, memo: Uint8Array.of(0, 1, 2, 255) };

for (const value of [
  { is_some: true, value: nonzero },
  { is_some: false, value: zero },
  { is_some: false, value: nonzero },
]) {
  const { result, context: nextContext } = await contract.circuits.echo(context(), value);
  assert.deepEqual(result, value);
  assert.equal(ledger(nextContext.callContext.currentQueryContext.state).seen, value.is_some);
}

await assert.rejects(contract.circuits.echo(context(), { is_some: 'false', value: zero }));
await assert.rejects(contract.circuits.echo(context(), {
  is_some: false,
  value: { ...nonzero, memo: Uint8Array.of(0, 1, 2) },
}));
console.log('Compact 0.36.1 preserved all Maybe argument fields and wrote the supplied tag');
