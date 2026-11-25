import assert from 'node:assert/strict';
import { existsSync, mkdirSync, readFileSync, symlinkSync } from 'node:fs';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';

const [generatedDirectory] = process.argv.slice(2);
const runtimeDirectory = process.env.NOCTIUM_COMPACT_RUNTIME_DIR;
assert.ok(generatedDirectory && runtimeDirectory, 'pass the compiler output and set NOCTIUM_COMPACT_RUNTIME_DIR');
const manifest = JSON.parse(readFileSync(
  new URL('../fixtures/native-collection-pages/manifest.json', import.meta.url), 'utf8',
));
assert.equal(manifest.schemaVersion, 1, 'expected native collection page fixture schema version 1');
assert.ok(Array.isArray(manifest.cases) && manifest.cases.length > 0, 'fixture manifest must contain cases');
const runtimeLink = resolve(generatedDirectory, 'node_modules/@midnight-ntwrk/compact-runtime');
mkdirSync(resolve(runtimeLink, '..'), { recursive: true });
if (!existsSync(runtimeLink)) symlinkSync(resolve(runtimeDirectory), runtimeLink, 'dir');
const { createCircuitContext, createConstructorContext, dummyContractAddress, versionString } = await import(
  pathToFileURL(resolve(runtimeDirectory, 'dist/index.js')).href,
);
assert.equal(versionString, '0.21.0', `expected Compact runtime 0.21.0, got ${versionString}`);
const { Contract, ledger } = await import(
  pathToFileURL(resolve(generatedDirectory, 'contract/index.js')).href,
);
const contract = new Contract({});
const walletKey = '00'.repeat(32);
const { currentContractState } = await contract.initialState(createConstructorContext(null, walletKey));
const callWithResult = async (state, entrypoint, ...args) => {
  const context = createCircuitContext({
    circuitId: entrypoint,
    contractAddress: dummyContractAddress(),
    coinPublicKeyOrZswapState: walletKey,
    contractState: state,
    privateState: null,
  });
  const result = await contract.circuits[entrypoint](context, ...args);
  return [result.result, result.context.callContext.currentQueryContext.state];
};
const call = async (...args) => (await callWithResult(...args))[1];

const flags = [[10n, true], [2n, false], [1n, true]];
const members = [9, 1, 4];
const listValues = [11n, 22n, 33n];
let pagePopulatedState;
for (const reverse of [false, true]) {
  let state = currentContractState.data;
  if (!reverse) state = await call(state, 'put', 2n, true);
  for (const [key, value] of reverse ? [...flags].reverse() : flags) {
    state = await call(state, 'put', key, value);
  }
  for (const value of reverse ? [...members].reverse() : members) {
    state = await call(state, 'add', new Uint8Array(32).fill(value));
  }
  if (!reverse) {
    state = await call(state, 'add', new Uint8Array(32).fill(1));
    for (const value of [...listValues].reverse()) {
      state = await call(state, 'prepend', value);
    }
    pagePopulatedState = state;
  }
  const snapshot = ledger(state);
  // Compact iteration order is outside the comparison. Compare canonical contents.
  const actualFlags = [...snapshot.flags].sort(([a], [b]) => a < b ? -1 : a > b ? 1 : 0);
  const actualMembers = [...snapshot.members].sort((a, b) => Buffer.compare(a, b));
  assert.deepEqual(actualFlags, [[1n, true], [2n, false], [10n, true]]);
  assert.equal(snapshot.flags.lookup(2n), false);
  assert.equal(snapshot.flags.member(3n), false);
  assert.deepEqual(actualMembers, [1, 4, 9].map(value => new Uint8Array(32).fill(value)));
  assert.equal(snapshot.flags.size(), 3n);
  assert.equal(snapshot.members.size(), 3n);
}
assert.deepEqual([...ledger(currentContractState.data).values], []);
assert.equal(ledger(currentContractState.data).values.length(), 0n);
assert.deepEqual([...ledger(pagePopulatedState).values], listValues);
assert.equal(ledger(pagePopulatedState).values.length(), BigInt(listValues.length));
const removedMember = new Uint8Array(32).fill(4);
const pageRemovedState = await call(pagePopulatedState, 'remove', removedMember);
const pageStates = {
  empty: currentContractState.data,
  populated: pagePopulatedState,
  removed: pageRemovedState,
};

const collectionPage = (state, name, offset, limit) => {
  assert.ok(Number.isSafeInteger(offset) && offset >= 0, `invalid page offset ${offset}`);
  assert.ok(Number.isSafeInteger(limit) && limit > 0, `invalid page limit ${limit}`);
  assert.ok(Number.isSafeInteger(offset + limit), 'page offset plus limit must be a safe integer');
  const snapshot = ledger(state);
  let kind;
  let entries;
  if (name === 'flags') {
    kind = 'map';
    entries = [...snapshot.flags]
      .sort(([left], [right]) => left < right ? -1 : left > right ? 1 : 0)
      .map(([key, value]) => ({ key: key.toString(), value }));
  } else if (name === 'members') {
    kind = 'set';
    entries = [...snapshot.members]
      .sort((left, right) => Buffer.compare(left, right))
      .map((value) => ({ kind: 'bytes', values: Array.from(value) }));
  } else if (name === 'values') {
    kind = 'list';
    entries = [...snapshot.values].map((value) => value.toString());
  } else {
    assert.fail(`unknown native collection page case ${name}`);
  }
  const end = offset + limit;
  return {
    abiVersion: 1,
    kind,
    entries: entries.slice(offset, end),
    nextOffset: end < entries.length ? end : null,
  };
};

for (const pageCase of manifest.cases) {
  assert.ok(Object.hasOwn(pageStates, pageCase.snapshot), `unknown page snapshot ${pageCase.snapshot}`);
  const actual = collectionPage(
    pageStates[pageCase.snapshot], pageCase.name, pageCase.offset, pageCase.limit,
  );
  assert.deepEqual(actual, pageCase.expected,
    `${pageCase.snapshot}.${pageCase.name} page at ${pageCase.offset} with limit ${pageCase.limit}`);
}
const removedSnapshot = ledger(pageRemovedState);
assert.equal(removedSnapshot.members.member(removedMember), false);
assert.equal(removedSnapshot.members.size(), 2n);
assert.deepEqual(
  [...removedSnapshot.members].sort((left, right) => Buffer.compare(left, right)),
  [1, 9].map((value) => new Uint8Array(32).fill(value)),
);
assert.deepEqual(
  [...removedSnapshot.flags].sort(([left], [right]) => left < right ? -1 : left > right ? 1 : 0),
  [[1n, true], [2n, false], [10n, true]],
);
assert.deepEqual([...removedSnapshot.values], listValues);

const owner = new Uint8Array(32).fill(7);
let nestedState = currentContractState.data;
for (const [key, value] of flags) {
  nestedState = await call(nestedState, 'putNested', owner, key, value);
}
for (const value of members) {
  nestedState = await call(nestedState, 'addNested', owner, new Uint8Array(32).fill(value));
}
for (const value of [...listValues].reverse()) {
  nestedState = await call(nestedState, 'prependNested', owner, value);
}
const nested = ledger(nestedState);
const nestedFlags = [...nested.nestedFlags.lookup(owner)].sort(([a], [b]) => a < b ? -1 : a > b ? 1 : 0);
const nestedMembers = [...nested.nestedMembers.lookup(owner)].sort((a, b) => Buffer.compare(a, b));
assert.deepEqual(nestedFlags, [[1n, true], [2n, false], [10n, true]]);
assert.equal(nested.nestedFlags.lookup(owner).lookup(10n), true);
assert.equal(nested.nestedFlags.lookup(owner).member(3n), false);
assert.deepEqual(nestedMembers, [1, 4, 9].map(value => new Uint8Array(32).fill(value)));
assert.deepEqual([...nested.nestedValues.lookup(owner)], listValues);
assert.equal(nested.nestedFlags.lookup(owner).size(), 3n);
assert.equal(nested.nestedMembers.lookup(owner).size(), 3n);
assert.equal(nested.nestedValues.lookup(owner).length(), 3n);
const mapped = { c1x: 1n, c1y: 2n, c2x: 3n, c2y: 4n };
const listed = { c1x: 5n, c1y: 6n, c2x: 7n, c2y: 8n };
const recordState = await call(currentContractState.data, 'seedRecords', owner, mapped, listed);
const records = ledger(recordState);
assert.deepEqual([...records.records], [[owner, mapped]]);
assert.deepEqual(records.records.lookup(owner), mapped);
assert.deepEqual([...records.recordList], [listed]);

assert.deepEqual([...ledger(currentContractState.data).recordMembers], []);
let recordMemberState = currentContractState.data;
const memoTrue513 = { active: true, amount: 513n };
const memoFalse513 = { active: false, amount: 513n };
const memoTrue514 = { active: true, amount: 514n };
let recordMapState = currentContractState.data;
for (const [key, value] of [[memoTrue513, 33n], [memoFalse513, 22n], [memoTrue514, 44n]]) {
  recordMapState = await call(recordMapState, 'putRecordFlag', key.active, key.amount, value);
}
const recordFlags = ledger(recordMapState).recordFlags;
assert.equal(recordFlags.lookup(memoTrue513), 33n);
assert.equal(recordFlags.lookup(memoFalse513), 22n);
assert.equal(recordFlags.lookup(memoTrue514), 44n);
assert.equal(recordFlags.member({ active: false, amount: 514n }), false);

const normalizedRecordMembers = (state) => [...ledger(state).recordMembers]
  .map(({ active, amount }) => ({ active, amount }))
  .sort((left, right) => Number(left.active) - Number(right.active) ||
    (left.amount < right.amount ? -1 : left.amount > right.amount ? 1 : 0));
for (const [memo, expectedSize] of [
  [memoTrue513, 1n], [memoFalse513, 2n], [memoTrue514, 3n], [memoTrue513, 3n],
]) {
  const [result, next] = await callWithResult(
    recordMemberState, 'updateRecordMember', memo.active, memo.amount, true, false,
  );
  assert.deepEqual(result, [true, expectedSize]);
  recordMemberState = next;
}
assert.deepEqual(normalizedRecordMembers(recordMemberState), [memoFalse513, memoTrue513, memoTrue514]);
const [removed, finalRecords] = await callWithResult(
  recordMemberState, 'updateRecordMember', memoFalse513.active, memoFalse513.amount, false, true,
);
assert.deepEqual(removed, [false, 2n]);
assert.deepEqual(normalizedRecordMembers(finalRecords), [memoTrue513, memoTrue514]);
console.log('Compact 0.36.1 matched canonical native collection pages and scalar and checked record contents');
