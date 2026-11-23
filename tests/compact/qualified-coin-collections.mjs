import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { readFile } from 'node:fs/promises';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectoryArgument] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectoryArgument,
  'usage: node tests/compact/qualified-coin-collections.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/,
  `expected pinned Compact 0.36.1 compiler, got ${compilerVersion}`);
const runtimeDirectory = resolve(runtimeDirectoryArgument);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0', 'expected pinned Compact runtime 0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/QualifiedCoinCollections.compact');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'qualified-coin-collections-'));

try {
  const generated = join(scratch, 'compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');
  const runtimeUrl = pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href;
  const contractUrl = pathToFileURL(join(generated, 'contract/index.js')).href;
  const { createCircuitContext, createConstructorContext } = await import(runtimeUrl);
  const { Contract, ledger } = await import(contractUrl);

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
let bookedCellReceiveEffects;

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
  if (entry === 'putInCell') {
    bookedCellReceiveEffects = [...query.effects.claimedShieldedReceives];
  }
  const qualified = { ...coin, mt_index: 0n };
  assert.deepEqual(view(query.state), { ...initial, [field]: field === 'coinSlot' ? qualified : [qualified] });

  const relation = JSON.parse(await readFile(join(generated, 'zkir', `${entry}.zkir`), 'utf8'));
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

const self = Uint8Array.from(Buffer.from(own, 'hex'));
let nestedSetState = currentContractState.data;
const missingOwner = contextFor('putInNestedSet', nestedSetState);
await assert.rejects(
  contract.circuits.putInNestedSet(missingOwner, owners[0], coin, true, self),
  /invalid operation for type: attempted to ins/,
);
assert.equal(ledger(missingOwner.callContext.currentQueryContext.state).coinSets.member(owners[0]), false);
for (const owner of owners) {
  const { context } = await contract.circuits.initializeSetOwner(
    contextFor('initializeSetOwner', nestedSetState), owner,
  );
  nestedSetState = context.callContext.currentQueryContext.state;
}
for (const [owner, entry] of [[owners[0], coin], [owners[1], thirdCoin], [owners[0], secondCoin]]) {
  const { context } = await contract.circuits.putInNestedSet(
    contextFor('putInNestedSet', nestedSetState), owner, entry, true, self,
  );
  assert.equal(context.callContext.currentQueryContext.effects.claimedShieldedReceives.length, 1);
  nestedSetState = context.callContext.currentQueryContext.state;
}
const nestedMembers = state => owners.map(owner =>
  [...ledger(state).coinSets.lookup(owner)].sort(compareQualified));
const expectedSets = [[qualifiedFirst, qualifiedSecond], [{ ...thirdCoin, mt_index: 0n }]];
assert.deepEqual(nestedMembers(nestedSetState), expectedSets);
for (const [book, recipient] of [[false, self], [true, new Uint8Array(32).fill(10)]]) {
  const context = contextFor('putInNestedSet', nestedSetState);
  await assert.rejects(
    contract.circuits.putInNestedSet(context, owners[0], secondCoin, book, recipient),
    /Coin commitment not found/,
  );
  assert.deepEqual(nestedMembers(context.callContext.currentQueryContext.state), expectedSets);
}
const nestedRelation = JSON.parse(await readFile(
  join(generated, 'zkir', 'putInNestedSet.zkir'), 'utf8',
));
const storage = nestedRelation.instructions.filter(({ op }) => op === 'impact').slice(-10);
assert.deepEqual(storage[0].inputs.slice(0, 6), ['0x71', '0x01', '0x01', '0x04', '0x01', '0x20']);
assert.deepEqual(storage[1].inputs, ['0x36']);
assert.deepEqual(storage.at(-1).inputs, ['0xa2']);

const mapKey = new Uint8Array(32).fill(7);
const map = state => ledger(state).coinMap;
assert.equal(map(currentContractState.data).member(mapKey), false);
const unbookedMap = contextFor('putInMap');
await assert.rejects(
  contract.circuits.putInMap(unbookedMap, mapKey, coin, false, self),
  /Coin commitment not found/,
);
assert.equal(unbookedMap.callContext.currentQueryContext.effects.claimedShieldedReceives.length, 0);
assert.deepEqual(view(unbookedMap.callContext.currentQueryContext.state), initial);
assert.equal(map(unbookedMap.callContext.currentQueryContext.state).member(mapKey), false);

const firstMapCall = await contract.circuits.putInMap(
  contextFor('putInMap'), mapKey, coin, true, self,
);
const firstMapQuery = firstMapCall.context.callContext.currentQueryContext;
const firstMapZswap = firstMapCall.context.callContext.currentZswapLocalState;
const qualifiedMapFirst = { ...coin, mt_index: 0n };
assert.equal(firstMapZswap.currentIndex, 1n);
assert.equal(firstMapZswap.outputs.length, 1);
assert.deepEqual(firstMapZswap.outputs[0].coinInfo, coin);
assert.equal(firstMapQuery.effects.claimedShieldedReceives.length, 1);
assert.deepEqual(firstMapQuery.effects.claimedShieldedReceives, bookedCellReceiveEffects,
  'Map insertion keeps the single receive effect from the fixture booking');
assert.equal(map(firstMapQuery.state).size(), 1n);
assert.equal(map(firstMapQuery.state).member(mapKey), true);
assert.deepEqual(map(firstMapQuery.state).lookup(mapKey), qualifiedMapFirst);

const secondMapCall = await contract.circuits.putInMap(
  contextFor('putInMap', firstMapQuery.state), mapKey, secondCoin, true, self,
);
const secondMapQuery = secondMapCall.context.callContext.currentQueryContext;
const secondMapZswap = secondMapCall.context.callContext.currentZswapLocalState;
const qualifiedMapSecond = { ...secondCoin, mt_index: 0n };
const secondCellCall = await contract.circuits.putInCell(
  contextFor('putInCell'), secondCoin, true,
);
assert.equal(secondMapZswap.currentIndex, 1n);
assert.equal(secondMapZswap.outputs.length, 1);
assert.deepEqual(secondMapZswap.outputs[0].coinInfo, secondCoin);
assert.equal(secondMapQuery.effects.claimedShieldedReceives.length, 1,
  'overwriting through insertCoin adds no receive claim');
assert.deepEqual(secondMapQuery.effects.claimedShieldedReceives,
  secondCellCall.context.callContext.currentQueryContext.effects.claimedShieldedReceives);
assert.equal(map(secondMapQuery.state).size(), 1n);
assert.equal(map(secondMapQuery.state).member(mapKey), true);
assert.deepEqual(map(secondMapQuery.state).lookup(mapKey), qualifiedMapSecond);

const mapStorageBeforeRejections = view(secondMapQuery.state);
for (const [book, recipient] of [[false, self], [true, new Uint8Array(32).fill(10)]]) {
  const context = contextFor('putInMap', secondMapQuery.state);
  await assert.rejects(
    contract.circuits.putInMap(context, mapKey, secondCoin, book, recipient),
    /Coin commitment not found/,
  );
  assert.deepEqual(view(context.callContext.currentQueryContext.state), mapStorageBeforeRejections);
  assert.equal(map(context.callContext.currentQueryContext.state).size(), 1n);
  assert.deepEqual(
    map(context.callContext.currentQueryContext.state).lookup(mapKey), qualifiedMapSecond,
  );
}

const nestedMapOwner = new Uint8Array(32).fill(8);
const uninitializedMapOwner = new Uint8Array(32).fill(9);
const nestedMapKey = new Uint8Array(32).fill(11);
const nestedMap = state => ledger(state).coinMaps;
const nestedMapValue = (state, owner) => nestedMap(state).lookup(owner);
let nestedMapState = currentContractState.data;
for (const owner of [nestedMapOwner, owners[1]]) {
  const { context } = await contract.circuits.initializeMapOwner(
    contextFor('initializeMapOwner', nestedMapState), owner,
  );
  nestedMapState = context.callContext.currentQueryContext.state;
}
assert.equal(nestedMap(nestedMapState).member(nestedMapOwner), true);
assert.equal(nestedMapValue(nestedMapState, nestedMapOwner).size(), 0n);

const missingMapOwnerContext = contextFor('putInNestedMap', nestedMapState);
await assert.rejects(
  contract.circuits.putInNestedMap(
    missingMapOwnerContext, uninitializedMapOwner, nestedMapKey, coin, true, self,
  ),
  /invalid operation for type: attempted to ins/,
);
assert.equal(nestedMap(missingMapOwnerContext.callContext.currentQueryContext.state)
  .member(uninitializedMapOwner), false);

const acceptedNestedMapCall = await contract.circuits.putInNestedMap(
  contextFor('putInNestedMap', nestedMapState), nestedMapOwner, nestedMapKey, coin, true, self,
);
const acceptedNestedMapQuery = acceptedNestedMapCall.context.callContext.currentQueryContext;
const qualifiedNestedMapCoin = { ...coin, mt_index: 0n };
assert.equal(acceptedNestedMapQuery.effects.claimedShieldedReceives.length, 1);
assert.equal(nestedMapValue(acceptedNestedMapQuery.state, nestedMapOwner).size(), 1n);
assert.equal(nestedMapValue(acceptedNestedMapQuery.state, nestedMapOwner).member(nestedMapKey), true);
assert.deepEqual(
  nestedMapValue(acceptedNestedMapQuery.state, nestedMapOwner).lookup(nestedMapKey),
  qualifiedNestedMapCoin,
);

const overwrittenNestedMapCall = await contract.circuits.putInNestedMap(
  contextFor('putInNestedMap', acceptedNestedMapQuery.state),
  nestedMapOwner, nestedMapKey, secondCoin, true, self,
);
const overwrittenNestedMapQuery = overwrittenNestedMapCall.context.callContext.currentQueryContext;
const qualifiedOverwrittenNestedMapCoin = { ...secondCoin, mt_index: 0n };
assert.equal(overwrittenNestedMapQuery.effects.claimedShieldedReceives.length, 1);
assert.equal(nestedMapValue(overwrittenNestedMapQuery.state, nestedMapOwner).size(), 1n);
assert.deepEqual(
  nestedMapValue(overwrittenNestedMapQuery.state, nestedMapOwner).lookup(nestedMapKey),
  qualifiedOverwrittenNestedMapCoin,
);

for (const [book, recipient] of [[false, self], [true, new Uint8Array(32).fill(10)]]) {
  const context = contextFor('putInNestedMap', overwrittenNestedMapQuery.state);
  await assert.rejects(
    contract.circuits.putInNestedMap(
      context, nestedMapOwner, nestedMapKey, secondCoin, book, recipient,
    ),
    /Coin commitment not found/,
  );
  assert.deepEqual(
    nestedMapValue(context.callContext.currentQueryContext.state, nestedMapOwner)
      .lookup(nestedMapKey),
    qualifiedOverwrittenNestedMapCoin,
  );
}

const nestedMapRelation = JSON.parse(await readFile(
  join(generated, 'zkir', 'putInNestedMap.zkir'), 'utf8',
));
const nestedMapImpact = nestedMapRelation.instructions.filter(({ op }) => op === 'impact');
receipt.impact.putInNestedMap = nestedMapImpact;
receipt.impact.putInNestedMapSuffix = nestedMapImpact.slice(-12);
assert.deepEqual(nestedMapImpact.slice(-12), [
  { op: 'impact', guard: '%book.9', inputs: ['0xa2'] },
  { op: 'impact', guard: '%book.9', inputs: ['0x40'] },
  {
    op: 'impact', guard: '0x01',
    inputs: ['0x71', '0x01', '0x01', '0x06', '0x01', '0x20', '%owner.0', '%owner.1'],
  },
  {
    op: 'impact', guard: '0x01',
    inputs: ['0x10', '0x01', '0x01', '0x20', '%key.2', '%key.3'],
  },
  { op: 'impact', guard: '0x01', inputs: ['0x37'] },
  {
    op: 'impact', guard: '0x01',
    inputs: ['0x10', '0x01', '0x01', '0x20', '%hash.21', '%hash.20'],
  },
  {
    op: 'impact', guard: '0x01',
    inputs: ['0x61', '0x01', '0x01', '0x01', '-0x01'],
  },
  {
    op: 'impact', guard: '0x01',
    inputs: [
      '0x10', '0x01', '0x03', '0x20', '0x20', '0x10',
      '%coin.4', '%coin.5', '%coin.6', '%coin.7', '%coin.8',
    ],
  },
  { op: 'impact', guard: '0x01', inputs: ['0x40'] },
  { op: 'impact', guard: '0x01', inputs: ['0x17', '0x5b'] },
  { op: 'impact', guard: '0x01', inputs: ['0x91'] },
  { op: 'impact', guard: '0x01', inputs: ['0xa2'] },
]);

console.log(
  'Pinned Compact 0.36.1 and Runtime 0.21.0 matched direct and nested qualified coin maps, booking, overwrite, missing-owner rejection, and Impact suffix',
);
console.log(JSON.stringify(receipt, null, 2));
console.log('Nested Map Impact suffix (last 12 impact instructions):');
console.log(JSON.stringify(nestedMapImpact.slice(-12), null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
