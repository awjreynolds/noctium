import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/nested-fixed-byte-record-values.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/);
const runtimeDirectory = resolve(runtimePath);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'nested-fixed-byte-record-values-'));
try {
  const generated = join(scratch, 'compact');
  const source = join(root, 'tests/compact/NestedFixedByteRecordValues.compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');
  const { createCircuitContext, createConstructorContext, dummyContractAddress } = await import(
    pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href,
  );
  const { Contract, ledger } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const contract = new Contract({});
  const wallet = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(createConstructorContext(null, wallet));
  const ownerA = new Uint8Array(32).fill(1);
  const ownerB = new Uint8Array(32).fill(2);
  const firstKey = new Uint8Array(32).fill(0x10);
  const siblingKey = new Uint8Array(32).fill(0x20);
  const missingKey = new Uint8Array(32).fill(0x30);
  const trailingPayload = finalByte => new Uint8Array([...new Array(32).fill(3), finalByte]);
  const firstProfile = { label: new Uint8Array([11]), digest: trailingPayload(4) };
  const siblingProfile = { label: new Uint8Array([12]), digest: trailingPayload(5) };
  const ownerBProfile = { label: new Uint8Array([21]), digest: trailingPayload(6) };
  const replacementProfile = { label: new Uint8Array([13]), digest: trailingPayload(7) };
  const exerciseArgs = [
    ownerA, ownerB, firstKey, siblingKey,
    firstProfile.label, firstProfile.digest,
    siblingProfile.label, siblingProfile.digest,
    ownerBProfile.label, ownerBProfile.digest,
    replacementProfile.label, replacementProfile.digest,
  ];
  const invoke = async (state, name, ...args) => {
    const { result, context } = await contract.circuits[name](createCircuitContext({
      circuitId: name,
      contractAddress: dummyContractAddress(),
      coinPublicKeyOrZswapState: wallet,
      contractState: state,
      privateState: null,
    }), ...args);
    return [result, context.callContext.currentQueryContext.state];
  };
  const bytes = value => ({ kind: 'bytes', values: Array.from(value) });
  const byteOutputNames = new Set([
    'firstLabel', 'firstDigest', 'siblingLabel', 'siblingDigest',
    'ownerBLabel', 'ownerBDigest', 'replacedLabel', 'replacedDigest',
  ]);
  const exerciseNames = [
    'firstBefore', 'siblingBefore', 'ownerBBefore',
    'firstPresent', 'siblingPresent', 'ownerBPresent',
    'firstLabel', 'firstDigest', 'siblingLabel', 'siblingDigest',
    'ownerBLabel', 'ownerBDigest', 'replacedLabel', 'replacedDigest',
    'firstAfterRemove', 'siblingAfterRemove', 'ownerBAfterRemove',
  ];
  const inspectNames = [
    'firstPresent', 'siblingPresent', 'ownerBPresent',
    'siblingLabel', 'siblingDigest', 'ownerBLabel', 'ownerBDigest',
  ];
  const normalize = (names, result) => Object.fromEntries(names.map((name, index) => [
    name,
    byteOutputNames.has(name) || name.endsWith('Digest') || name.endsWith('Label')
      ? bytes(result[index])
      : result[index],
  ]));

  let state = currentContractState.data;
  [, state] = await invoke(state, 'initializeOwner', ownerA);
  [, state] = await invoke(state, 'initializeOwner', ownerB);
  const initial = state;
  const [exerciseResult, afterExercise] = await invoke(state, 'exercise', ...exerciseArgs);
  const outputs = normalize(exerciseNames, exerciseResult);
  assert.deepEqual(outputs, {
    firstBefore: false,
    siblingBefore: false,
    ownerBBefore: false,
    firstPresent: true,
    siblingPresent: true,
    ownerBPresent: true,
    firstLabel: bytes(firstProfile.label),
    firstDigest: bytes(firstProfile.digest),
    siblingLabel: bytes(siblingProfile.label),
    siblingDigest: bytes(siblingProfile.digest),
    ownerBLabel: bytes(ownerBProfile.label),
    ownerBDigest: bytes(ownerBProfile.digest),
    replacedLabel: bytes(replacementProfile.label),
    replacedDigest: bytes(replacementProfile.digest),
    firstAfterRemove: false,
    siblingAfterRemove: true,
    ownerBAfterRemove: true,
  });

  const profileLedger = ledger(afterExercise).profiles;
  assert.equal(profileLedger.size(), 2n);
  assert.equal(profileLedger.lookup(ownerA).size(), 1n);
  assert.equal(profileLedger.lookup(ownerB).size(), 1n);
  assert.equal(profileLedger.lookup(ownerA).member(firstKey), false);
  assert.deepEqual(profileLedger.lookup(ownerA).lookup(siblingKey), siblingProfile);
  assert.deepEqual(profileLedger.lookup(ownerB).lookup(firstKey), ownerBProfile);

  const wrongDigestWidth = [...exerciseArgs];
  wrongDigestWidth[5] = firstProfile.digest.slice(0, 32);
  await assert.rejects(() => invoke(initial, 'exercise', ...wrongDigestWidth));

  const [absentCheck] = await invoke(afterExercise, 'inspect', ownerA, ownerB, firstKey, siblingKey);
  assert.deepEqual(normalize(inspectNames, absentCheck), {
    firstPresent: false,
    siblingPresent: true,
    ownerBPresent: true,
    siblingLabel: bytes(siblingProfile.label),
    siblingDigest: bytes(siblingProfile.digest),
    ownerBLabel: bytes(ownerBProfile.label),
    ownerBDigest: bytes(ownerBProfile.digest),
  });
  await assert.rejects(() => invoke(afterExercise, 'lookupAbsent', ownerA, firstKey));
  const [afterRejectedLookup] = await invoke(afterExercise, 'inspect', ownerA, ownerB, firstKey, siblingKey);
  assert.deepEqual(normalize(inspectNames, afterRejectedLookup), normalize(inspectNames, absentCheck));

  console.log(JSON.stringify({
    fixture: 'NestedFixedByteRecordValues',
    compact: compilerVersion,
    runtime: runtimePackage.version,
    parents: {
      ownerA: '01'.repeat(32),
      ownerB: '02'.repeat(32),
      buckets: Number(profileLedger.size()),
    },
    leafKeys: {
      first: '10'.repeat(32),
      sibling: '20'.repeat(32),
      sharedAcrossParents: true,
    },
    trailingPayloadBytes: {
      first: firstProfile.digest[32],
      sibling: siblingProfile.digest[32],
      ownerB: ownerBProfile.digest[32],
      replacement: replacementProfile.digest[32],
    },
    outputs,
    entriesPerParentAfterRemoval: [Number(profileLedger.lookup(ownerA).size()), Number(profileLedger.lookup(ownerB).size())],
    wrongDigestWidthRejected: true,
    absentLookupRejectedWithoutChangingSiblingOrOtherParent: true,
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
