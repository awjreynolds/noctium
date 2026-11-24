import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/nested-two-parent-record-key-values.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/);
const runtimeDirectory = resolve(runtimePath);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'nested-two-parent-record-key-values-'));
try {
  const generated = join(scratch, 'compact');
  const source = join(root, 'tests/compact/NestedTwoParentRecordKeyValues.compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const { createCircuitContext, createConstructorContext, dummyContractAddress } = await import(
    pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href,
  );
  const { Contract, ledger } = await import(
    pathToFileURL(join(generated, 'contract/index.js')).href,
  );
  const contract = new Contract({});
  const wallet = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(
    createConstructorContext(null, wallet),
  );
  const owner = new Uint8Array(32).fill(1);
  const groupA = new Uint8Array(32).fill(1);
  const groupB = new Uint8Array(32).fill(2);
  const tag = new Uint8Array([7]);
  const keyId = tail => new Uint8Array([...new Array(32).fill(3), tail]);
  const digest = tail => new Uint8Array([...new Array(32).fill(6), tail]);
  const firstId = keyId(4);
  const siblingId = keyId(5);
  const firstProfile = { label: new Uint8Array([11]), digest: digest(4) };
  const siblingProfile = { label: new Uint8Array([12]), digest: digest(5) };
  const otherGroupProfile = { label: new Uint8Array([21]), digest: digest(6) };
  const replacementProfile = { label: new Uint8Array([13]), digest: digest(7) };

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
  const recordKey = id => ({ tag, id });
  const jsonBytes = value => ({ kind: 'bytes', values: Array.from(value) });
  const jsonProfile = profile => ({
    label: jsonBytes(profile.label),
    digest: jsonBytes(profile.digest),
  });
  const jsonLookup = result => jsonProfile({ label: result[0], digest: result[1] });
  const lookup = async (state, group, id) => {
    const [result] = await invoke(state, 'lookup', owner, group, tag, id);
    return jsonLookup(result);
  };

  let state = currentContractState.data;
  [, state] = await invoke(
    state, 'store', owner, groupA, tag, firstId, firstProfile.label, firstProfile.digest,
  );
  const initialFirst = await lookup(state, groupA, firstId);
  assert.deepEqual(initialFirst, jsonProfile(firstProfile));

  [, state] = await invoke(
    state, 'store', owner, groupA, tag, siblingId, siblingProfile.label, siblingProfile.digest,
  );
  const initialSibling = await lookup(state, groupA, siblingId);
  assert.deepEqual(initialSibling, jsonProfile(siblingProfile));

  [, state] = await invoke(
    state, 'store', owner, groupB, tag, firstId, otherGroupProfile.label, otherGroupProfile.digest,
  );
  const initialOtherOwner = await lookup(state, groupB, firstId);
  assert.deepEqual(initialOtherOwner, jsonProfile(otherGroupProfile));

  const malformedId = firstId.slice(0, 32);
  await assert.rejects(() => invoke(
    state, 'store', owner, groupA, tag, malformedId, firstProfile.label, firstProfile.digest,
  ));
  const malformedDigest = firstProfile.digest.slice(0, 32);
  await assert.rejects(() => invoke(
    state, 'store', owner, groupA, tag, firstId, firstProfile.label, malformedDigest,
  ));

  [, state] = await invoke(
    state, 'store', owner, groupA, tag, firstId,
    replacementProfile.label, replacementProfile.digest,
  );
  const overwritten = await lookup(state, groupA, firstId);
  assert.deepEqual(overwritten, jsonProfile(replacementProfile));

  [, state] = await invoke(state, 'remove', owner, groupA, tag, firstId);
  await assert.rejects(() => invoke(state, 'lookup', owner, groupA, tag, firstId));
  const survivingSibling = await lookup(state, groupA, siblingId);
  const survivingOtherOwner = await lookup(state, groupB, firstId);
  assert.deepEqual(survivingSibling, jsonProfile(siblingProfile));
  assert.deepEqual(survivingOtherOwner, jsonProfile(otherGroupProfile));

  const profileLedger = ledger(state).profiles;
  const ownerGroups = profileLedger.lookup(owner);
  const groupAProfiles = ownerGroups.lookup(groupA);
  const groupBProfiles = ownerGroups.lookup(groupB);
  assert.equal(profileLedger.size(), 1n);
  assert.equal(ownerGroups.size(), 2n);
  assert.equal(groupAProfiles.size(), 1n);
  assert.equal(groupBProfiles.size(), 1n);
  assert.equal(groupAProfiles.member(recordKey(firstId)), false);
  assert.equal(groupAProfiles.member(recordKey(siblingId)), true);
  assert.equal(groupBProfiles.member(recordKey(firstId)), true);
  assert.deepEqual(groupAProfiles.lookup(recordKey(siblingId)), siblingProfile);
  assert.deepEqual(groupBProfiles.lookup(recordKey(firstId)), otherGroupProfile);

  console.log(JSON.stringify({
    fixture: 'NestedTwoParentRecordKeyValues',
    compact: compilerVersion,
    runtime: runtimePackage.version,
    outputs: {
      initialFirst,
      initialSibling,
      initialOtherOwner,
      overwritten,
      survivingSibling,
      survivingOtherOwner,
    },
    ownerBucketsAfterRemoval: Number(profileLedger.size()),
    groupBucketsAfterRemoval: Number(ownerGroups.size()),
    entriesPerParentAfterRemoval: [Number(groupAProfiles.size()), Number(groupBProfiles.size())],
    wrongIdWidthRejected: true,
    wrongDigestWidthRejected: true,
    removedLookupRejected: true,
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
