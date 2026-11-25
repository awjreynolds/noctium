import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';

const [circuitPath, checkerPath, ledgerPath, ...extra] = process.argv.slice(2);
if (!circuitPath || !checkerPath || !ledgerPath || extra.length) {
  throw Error('Usage: node check-scalar-cell-transcript.mjs CIRCUIT.zkir OFFICIAL_CHECKER_MODULE LEDGER_V9_MODULE');
}

const { Zkir, check } = await import(pathToFileURL(resolve(checkerPath)).href);
const ledger = await import(pathToFileURL(resolve(ledgerPath)).href);
const relation = Zkir.fromJson(await readFile(circuitPath, 'utf8'));
const material = { ir: relation.serialize(), proverKey: new Uint8Array(), verifierKey: new Uint8Array() };
const provider = { lookupKey: async () => material };

const empty = { value: [], alignment: [] };
const field = number => ({
  value: ledger.bigIntToValue(number),
  alignment: [{ tag: 'atom', value: { tag: 'field' } }],
});
const push = (number, storage = false) => ({
  push: { storage, value: { tag: 'cell', content: field(number) } },
});
const read = number => ({ popeq: { cached: false, result: field(number) } });
const dup = { dup: { n: 0 } };
const targetCell = {
  idx: { cached: false, pushPath: false, path: [{ tag: 'value', value: field(0n) }] },
};

// Start with total 10 and add delta 3. The write and committed return
// both carry 13. Change each read expectation without changing the write
// operand, public delta, or committed return.
const operations = (before, after) => [
  push(3n), read(3n),
  dup, targetCell, read(before),
  push(0n), push(13n, true), { ins: { cached: false, n: 1 } },
  dup, targetCell, read(after),
];
const preimage = (before, after) => ledger.proofDataIntoSerializedPreimage(
  empty, field(13n), operations(before, after), [], 'noctium/scalar-cell-transcript',
);

const activity = await check(preimage(10n, 13n), provider);
assert.equal(activity.length, operations(10n, 13n).length);
const rejections = [];
for (const [name, before, after, expected] of [
  ['changed-before', 11n, 13n, /Public transcript input mismatch/],
  ['changed-after', 10n, 14n, /Communications commitment mismatch/],
]) {
  const tampered = preimage(before, after);
  await assert.rejects(() => check(tampered, provider), expected);
  rejections.push(name);
}

console.log(JSON.stringify({
  initialTotal: 10,
  delta: 3,
  committedReturn: 13,
  activityGroups: activity.length,
  honestAccepted: true,
  rejectedCases: rejections,
}));
