import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/nested-fixed-byte-record-map.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/);
const runtimeDirectory = resolve(runtimePath);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'nested-fixed-byte-record-map-'));
try {
  const generated = join(scratch, 'compact');
  const source = join(root, 'tests/compact/NestedFixedByteRecordMap.compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, 'Compact compilation failed:\n' + (compile.stderr || compile.stdout));
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
  const { currentContractState } = await contract.initialState(createConstructorContext(null, wallet));
  const ownerOne = new Uint8Array(32).fill(1);
  const ownerTwo = new Uint8Array(32).fill(2);
  const tag = new Uint8Array([7]);
  const firstId = new Uint8Array(33).fill(3);
  const lateId = new Uint8Array(firstId);
  lateId[32] = 4;
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
  const exerciseArgs = (owner, values) => [
    owner, tag, firstId, lateId,
    values.firstScalar, values.lateScalar,
    values.firstAccepted, values.firstCode, values.lateAccepted, values.lateCode,
  ];
  const normalize = (names, values) => Object.fromEntries(names.map((name, index) => [
    name, typeof values[index] === 'bigint' ? values[index].toString() : values[index],
  ]));
  const exerciseNames = [
    'scalarBeforeFirst', 'scalarBeforeLate', 'scalarInsertedFirst', 'scalarInsertedLate',
    'scalarValueFirst', 'scalarValueLate', 'recordBeforeFirst', 'recordBeforeLate',
    'recordInsertedFirst', 'recordInsertedLate', 'recordAcceptedFirst', 'recordCodeFirst',
    'recordAcceptedLate', 'recordCodeLate', 'scalarAfterFirst', 'scalarAfterLate',
    'recordAfterFirst', 'recordAfterLate', 'scalarRetainedValue',
    'recordRetainedAccepted', 'recordRetainedCode',
  ];
  const inspectNames = [
    'scalarFirstPresent', 'scalarLatePresent', 'scalarLateValue',
    'recordFirstPresent', 'recordLatePresent', 'recordLateAccepted', 'recordLateCode',
  ];

  let state = currentContractState.data;
  [, state] = await invoke(state, 'initializeOwner', ownerOne);
  [, state] = await invoke(state, 'initializeOwner', ownerTwo);
  const valuesOne = {
    firstScalar: 101n, lateScalar: 303n,
    firstAccepted: true, firstCode: 101n, lateAccepted: false, lateCode: 303n,
  };
  const valuesTwo = {
    firstScalar: 707n, lateScalar: 909n,
    firstAccepted: false, firstCode: 707n, lateAccepted: true, lateCode: 909n,
  };
  const [exerciseOne, afterOne] = await invoke(
    state, 'exercise', ...exerciseArgs(ownerOne, valuesOne),
  );
  const [exerciseTwo, afterTwo] = await invoke(
    afterOne, 'exercise', ...exerciseArgs(ownerTwo, valuesTwo),
  );
  const key = id => ({ tag, id });
  const scalarLedger = ledger(afterTwo).scalars;
  const recordLedger = ledger(afterTwo).records;
  for (const [owner, values] of [[ownerOne, valuesOne], [ownerTwo, valuesTwo]]) {
    const scalars = scalarLedger.lookup(owner);
    const records = recordLedger.lookup(owner);
    assert.equal(scalars.size(), 1n);
    assert.equal(records.size(), 1n);
    assert.equal(scalars.member(key(firstId)), false);
    assert.equal(scalars.member(key(lateId)), true);
    assert.equal(scalars.lookup(key(lateId)), values.lateScalar);
    assert.equal(records.member(key(firstId)), false);
    assert.equal(records.member(key(lateId)), true);
    assert.deepEqual(records.lookup(key(lateId)), {
      accepted: values.lateAccepted, code: values.lateCode,
    });
  }
  const [inspectOne] = await invoke(afterTwo, 'inspect', ownerOne, tag, firstId, lateId);
  const [inspectTwo] = await invoke(afterTwo, 'inspect', ownerTwo, tag, firstId, lateId);
  assert.equal(scalarLedger.size(), 2n);
  assert.equal(recordLedger.size(), 2n);
  const wrongWidth = new Uint8Array(firstId.slice(0, 32));
  await assert.rejects(() => invoke(
    afterTwo, 'exercise', ownerOne, tag, wrongWidth, lateId,
    valuesOne.firstScalar, valuesOne.lateScalar,
    valuesOne.firstAccepted, valuesOne.firstCode, valuesOne.lateAccepted, valuesOne.lateCode,
  ));

  const result = {
    fixture: 'NestedFixedByteRecordMap',
    compact: compilerVersion,
    runtime: runtimePackage.version,
    keys: {
      tag: [7],
      firstId: '03'.repeat(33),
      lateId: '03'.repeat(32) + '04',
    },
    owners: {
      first: {
        owner: '01'.repeat(32),
        exercise: normalize(exerciseNames, exerciseOne),
        inspect: normalize(inspectNames, inspectOne),
      },
      second: {
        owner: '02'.repeat(32),
        exercise: normalize(exerciseNames, exerciseTwo),
        inspect: normalize(inspectNames, inspectTwo),
      },
    },
    entriesPerParentAfterRemoval: 1,
    wrongKeyWidthRejected: true,
  };
  console.log(JSON.stringify(result, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
