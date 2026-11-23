import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { createCircuitContext, createConstructorContext } from '@midnight-ntwrk/compact-runtime';
import { Contract, ledger } from './compact/contract/index.js';

const contract = new Contract({});
const wallet = '00'.repeat(32);
const own = '09'.repeat(32);
const coin = { color: new Uint8Array(32).fill(1), nonce: new Uint8Array(32).fill(2), value: 5n };
const secondCoin = { color: new Uint8Array(32).fill(1), nonce: new Uint8Array(32).fill(3), value: 7n };
const { currentContractState } = await contract.initialState(createConstructorContext(null, wallet));
const view = (state) => {
  const { coinSlot, coinSet, coinList } = ledger(state);
  return { coinSlot, coinSet: [...coinSet], coinList: [...coinList] };
};
const initial = view(currentContractState.data);
const contextFor = (entry, contractState = currentContractState.data) => createCircuitContext({
  circuitId: entry, contractAddress: own, coinPublicKeyOrZswapState: wallet,
  contractState, privateState: null,
});
const receipt = { impact: {} };

for (const [entry, field] of [['putInCell', 'coinSlot'], ['putInSet', 'coinSet'], ['putInList', 'coinList']]) {
  const unbooked = contextFor(entry);
  await assert.rejects(contract.circuits[entry](unbooked, coin, false), /Coin commitment not found/);
  assert.deepEqual(view(unbooked.callContext.currentQueryContext.state), initial);

  const { context } = await contract.circuits[entry](contextFor(entry), coin, true);
  const query = context.callContext.currentQueryContext;
  const zswap = context.callContext.currentZswapLocalState;
  assert.equal(zswap.currentIndex, 1n);
  assert.equal(zswap.outputs.length, 1);
  assert.deepEqual(zswap.outputs[0].coinInfo, coin);
  assert.equal(query.effects.claimedShieldedReceives.length, 1);
  const qualified = { ...coin, mt_index: 0n };
  assert.deepEqual(view(query.state), { ...initial, [field]: field === 'coinSlot' ? qualified : [qualified] });

  const artifact = new URL(`./compact/zkir/${entry}.zkir`, import.meta.url);
  const relation = JSON.parse(await readFile(artifact, 'utf8'));
  const impact = relation.instructions.filter(({ op }) => op === 'impact');
  const qualifiedLookup = impact.findIndex(({ inputs }) => inputs[0] === '0x61');
  assert.ok(qualifiedLookup > 0);
  assert.deepEqual(impact[qualifiedLookup].inputs, ['0x61', '0x01', '0x01', '0x01', '-0x01']);
  const [commitment, lookup, fields, swap, concatenate] = impact.slice(qualifiedLookup - 1, qualifiedLookup + 4);
  assert.equal(commitment.guard, '0x01');
  assert.equal(lookup.guard, '0x01');
  assert.deepEqual(commitment.inputs, ['0x10', '0x01', '0x01', '0x20', '%hash.17', '%hash.16']);
  assert.deepEqual(fields.inputs, [
    '0x10', '0x01', '0x03', '0x20', '0x20', '0x10', '%coin.0', '%coin.1', '%coin.2', '%coin.3', '%coin.4',
  ]);
  assert.deepEqual(swap.inputs, ['0x40']);
  assert.deepEqual(concatenate.inputs, ['0x17', '0x5b']);
  receipt.impact[entry] = impact;
}

const firstSet = await contract.circuits.putInSet(contextFor('putInSet'), coin, true);
const stateWithFirstCoin = firstSet.context.callContext.currentQueryContext.state;
const secondSet = await contract.circuits.putInSet(
  contextFor('putInSet', stateWithFirstCoin), secondCoin, true,
);
const qualifiedFirst = { ...coin, mt_index: 0n };
const qualifiedSecond = { ...secondCoin, mt_index: 0n };
const qualifiedSet = ledger(secondSet.context.callContext.currentQueryContext.state).coinSet;
assert.equal(qualifiedSet.size().toString(), '2');
assert.equal(qualifiedSet.member(qualifiedFirst), true);
assert.equal(qualifiedSet.member(qualifiedSecond), true);
for (const altered of [
  { ...qualifiedFirst, color: new Uint8Array(32).fill(2) },
  { ...qualifiedFirst, nonce: new Uint8Array(32).fill(4) },
  { ...qualifiedFirst, value: 6n },
  { ...qualifiedFirst, mt_index: 1n },
]) {
  assert.equal(qualifiedSet.member(altered), false);
}
const compareBytes = (left, right) => Buffer.compare(left, right);
const compareQualified = (left, right) =>
  compareBytes(left.nonce, right.nonce)
  || compareBytes(left.color, right.color)
  || (left.value < right.value ? -1 : left.value > right.value ? 1 : 0)
  || (left.mt_index < right.mt_index ? -1 : left.mt_index > right.mt_index ? 1 : 0);
// Compact Set iteration order is unspecified. Compare complete records in schema order.
assert.deepEqual(
  [...qualifiedSet].sort(compareQualified),
  [qualifiedFirst, qualifiedSecond],
);

const owners = [new Uint8Array(32).fill(1), new Uint8Array(32).fill(2)];
const thirdCoin = { color: coin.color, nonce: new Uint8Array(32).fill(4), value: 11n };
let nestedState = currentContractState.data;
const nestedLists = () => owners.map(owner => [...ledger(nestedState).coinLists.lookup(owner)]);
for (const owner of owners) {
  const { context } = await contract.circuits.initializeOwner(
    contextFor('initializeOwner', nestedState), owner,
  );
  nestedState = context.callContext.currentQueryContext.state;
}

await assert.rejects(contract.circuits.putInNestedList(
  contextFor('putInNestedList', nestedState), owners[0], coin, false,
), /Coin commitment not found/);
assert.deepEqual(nestedLists(), [[], []]);

for (const [owner, entry] of [[owners[0], coin], [owners[1], thirdCoin], [owners[0], secondCoin]]) {
  const { context } = await contract.circuits.putInNestedList(
    contextFor('putInNestedList', nestedState), owner, entry, true,
  );
  const query = context.callContext.currentQueryContext;
  assert.equal(query.effects.claimedShieldedReceives.length, 1);
  nestedState = query.state;
}
assert.deepEqual(nestedLists(), [
  [qualifiedSecond, qualifiedFirst],
  [{ ...thirdCoin, mt_index: 0n }],
]);

console.log(JSON.stringify(receipt, null, 2));
