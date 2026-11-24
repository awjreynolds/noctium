import assert from 'node:assert/strict';
import {execFileSync, spawnSync} from 'node:child_process';
import {dirname, join, resolve} from 'node:path';
import {fileURLToPath, pathToFileURL} from 'node:url';
import {mkdirSync, mkdtempSync, readFileSync, rmSync, rmdirSync, symlinkSync, writeFileSync} from 'node:fs';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node generic-record-map.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], {encoding: 'utf8'}).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/, `unexpected Compact compiler: ${compilerVersion}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/GenericRecordMap.compact');
const experiments = join(projectRoot, 'build/experiments/917-generic-byte-map-keys');
mkdirSync(experiments, {recursive: true});
const scratch = mkdtempSync(join(experiments, 'run-'));

try {
  const generated = join(scratch, 'compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], {
    cwd: projectRoot,
    encoding: 'utf8',
  });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), {recursive: true});
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  assert.equal(runtime.versionString, '0.21.0');
  const {Contract, ledger} = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const contract = new Contract({});
  const walletKey = '00'.repeat(32);
  const {currentContractState} = await contract.initialState(
    runtime.createConstructorContext(null, walletKey),
  );
  const receipt = (amount, active) => ({amount: BigInt(amount), active});
  const run = async (circuitId, state, ...args) => {
    const call = await contract.circuits[circuitId](runtime.createCircuitContext({
      circuitId,
      contractAddress: runtime.dummyContractAddress(),
      coinPublicKeyOrZswapState: walletKey,
      contractState: state,
      privateState: null,
    }), ...args);
    return [call.result, call.context.callContext.currentQueryContext.state];
  };
  const readFieldMap = state => ledger(state).fieldReceiptMap_values;
  const readByteMap = state => ledger(state).byteReceiptMap_values;
  const readRecordKeyReceiptMap = state => ledger(state).recordKeyReceiptMap_values;
  const initial = currentContractState.data;
  assert.equal(readFieldMap(initial).size(), 0n);
  assert.equal(readByteMap(initial).size(), 0n);
  const readRecordKeyMap = state => ledger(state).recordKeyMap_values;
  assert.equal(readRecordKeyMap(initial).size(), 0n);
  assert.equal(readRecordKeyReceiptMap(initial).size(), 0n);
  const keyBytes = last => Uint8Array.from({length: 32}, (_, index) =>
    index < 31 ? index + 1 : last);
  const byteKeyA = keyBytes(11);
  const byteKeyB = keyBytes(12);
  const missingByteKey = keyBytes(13);

  const recordKey = (active, epoch) => ({active, epoch: BigInt(epoch)});
  const recordKeyA = recordKey(true, 513);
  const recordKeyB = recordKey(false, 513);
  const missingRecordKey = recordKey(true, 514);
  const receiptKeyA = recordKey(true, 513);
  const receiptKeyB = recordKey(false, 513);
  const missingReceiptKey = recordKey(true, 514);

  let [, state] = await run('put', initial, true, 11n, receipt(101, true));
  [, state] = await run('put', state, true, 12n, receipt(303, true));
  let entries = readFieldMap(state);
  assert.equal(entries.size(), 2n);
  assert.equal(entries.member(11n), true);
  assert.equal(entries.member(12n), true);
  assert.deepEqual(entries.lookup(11n), receipt(101, true));
  assert.deepEqual(entries.lookup(12n), receipt(303, true));
  assert.deepEqual((await run('lookup', state, 11n))[0], receipt(101, true));
  assert.deepEqual((await run('lookup', state, 12n))[0], receipt(303, true));

  [, state] = await run('putBytes', state, true, byteKeyA, receipt(101, true));
  [, state] = await run('putBytes', state, true, byteKeyB, receipt(303, true));
  let byteEntries = readByteMap(state);
  assert.equal(byteEntries.size(), 2n);
  assert.equal(byteEntries.member(byteKeyA), true);
  assert.equal(byteEntries.member(byteKeyB), true);
  assert.deepEqual(byteEntries.lookup(byteKeyA), receipt(101, true));
  assert.deepEqual(byteEntries.lookup(byteKeyB), receipt(303, true));
  assert.deepEqual((await run('lookupBytes', state, byteKeyA))[0], receipt(101, true));
  assert.deepEqual((await run('lookupBytes', state, byteKeyB))[0], receipt(303, true));

  [, state] = await run('putRecordKey', state, true, recordKeyA, 101n);
  [, state] = await run('putRecordKey', state, true, recordKeyB, 303n);
  let recordKeyEntries = readRecordKeyMap(state);
  assert.equal(recordKeyEntries.size(), 2n);
  assert.deepEqual(recordKeyEntries.lookup(recordKeyA), 101n);
  assert.deepEqual(recordKeyEntries.lookup(recordKeyB), 303n);
  assert.deepEqual((await run('lookupRecordKey', state, recordKeyA))[0], 101n);
  assert.deepEqual((await run('lookupRecordKey', state, recordKeyB))[0], 303n);

  [, state] = await run('putRecordKeyReceipt', state, true, receiptKeyA, receipt(101, true));
  [, state] = await run('putRecordKeyReceipt', state, true, receiptKeyB, receipt(303, true));
  let recordKeyReceiptEntries = readRecordKeyReceiptMap(state);
  assert.equal(recordKeyReceiptEntries.size(), 2n);
  assert.deepEqual(recordKeyReceiptEntries.lookup(receiptKeyA), receipt(101, true));
  assert.deepEqual(recordKeyReceiptEntries.lookup(receiptKeyB), receipt(303, true));
  assert.deepEqual(
    (await run('lookupRecordKeyReceipt', state, receiptKeyA))[0], receipt(101, true),
  );
  assert.deepEqual(
    (await run('lookupRecordKeyReceipt', state, receiptKeyB))[0], receipt(303, true),
  );

  const [, afterDisabled] = await run('put', state, false, 11n, receipt(999, false));
  entries = readFieldMap(afterDisabled);
  assert.equal(entries.size(), 2n);
  assert.deepEqual(entries.lookup(11n), receipt(101, true));
  assert.deepEqual(entries.lookup(12n), receipt(303, true));
  const [, afterByteDisabled] = await run(
    'putBytes', afterDisabled, false, byteKeyA, receipt(999, false),
  );
  byteEntries = readByteMap(afterByteDisabled);
  assert.equal(byteEntries.size(), 2n);
  assert.deepEqual(byteEntries.lookup(byteKeyA), receipt(101, true));
  assert.deepEqual(byteEntries.lookup(byteKeyB), receipt(303, true));
  const [, afterRecordKeyDisabled] = await run(
    'putRecordKey', afterByteDisabled, false, recordKeyA, 999n,
  );
  recordKeyEntries = readRecordKeyMap(afterRecordKeyDisabled);
  assert.equal(recordKeyEntries.size(), 2n);
  assert.equal(recordKeyEntries.lookup(recordKeyA), 101n);
  assert.equal(recordKeyEntries.lookup(recordKeyB), 303n);

  const [, afterRecordKeyReceiptDisabled] = await run(
    'putRecordKeyReceipt', afterRecordKeyDisabled, false, receiptKeyA, receipt(999, false),
  );
  recordKeyReceiptEntries = readRecordKeyReceiptMap(afterRecordKeyReceiptDisabled);
  assert.equal(recordKeyReceiptEntries.size(), 2n);
  assert.deepEqual(recordKeyReceiptEntries.lookup(receiptKeyA), receipt(101, true));
  assert.deepEqual(recordKeyReceiptEntries.lookup(receiptKeyB), receipt(303, true));

  const [, afterOverwrite] = await run('put', afterByteDisabled, true, 11n, receipt(202, false));
  entries = readFieldMap(afterOverwrite);
  assert.equal(entries.size(), 2n);
  assert.deepEqual(entries.lookup(11n), receipt(202, false));
  assert.deepEqual(entries.lookup(12n), receipt(303, true));
  assert.deepEqual((await run('lookup', afterOverwrite, 11n))[0], receipt(202, false));
  assert.deepEqual((await run('lookup', afterOverwrite, 12n))[0], receipt(303, true));

  const [, afterByteOverwrite] = await run(
    'putBytes', afterOverwrite, true, byteKeyA, receipt(202, false),
  );
  byteEntries = readByteMap(afterByteOverwrite);
  assert.equal(byteEntries.size(), 2n);
  assert.deepEqual(byteEntries.lookup(byteKeyA), receipt(202, false));
  assert.deepEqual(byteEntries.lookup(byteKeyB), receipt(303, true));
  assert.deepEqual((await run('lookupBytes', afterByteOverwrite, byteKeyA))[0], receipt(202, false));
  assert.deepEqual((await run('lookupBytes', afterByteOverwrite, byteKeyB))[0], receipt(303, true));

  const [, afterRecordKeyOverwrite] = await run(
    'putRecordKey', afterRecordKeyDisabled, true, recordKeyA, 202n,
  );
  recordKeyEntries = readRecordKeyMap(afterRecordKeyOverwrite);
  assert.equal(recordKeyEntries.size(), 2n);
  assert.equal(recordKeyEntries.lookup(recordKeyA), 202n);
  assert.equal(recordKeyEntries.lookup(recordKeyB), 303n);
  assert.equal((await run('lookupRecordKey', afterRecordKeyOverwrite, recordKeyA))[0], 202n);
  assert.equal((await run('lookupRecordKey', afterRecordKeyOverwrite, recordKeyB))[0], 303n);

  const [, afterRecordKeyReceiptOverwrite] = await run(
    'putRecordKeyReceipt', afterRecordKeyReceiptDisabled, true, receiptKeyA, receipt(202, false),
  );
  recordKeyReceiptEntries = readRecordKeyReceiptMap(afterRecordKeyReceiptOverwrite);
  assert.equal(recordKeyReceiptEntries.size(), 2n);
  assert.deepEqual(recordKeyReceiptEntries.lookup(receiptKeyA), receipt(202, false));
  assert.deepEqual(recordKeyReceiptEntries.lookup(receiptKeyB), receipt(303, true));
  assert.deepEqual(
    (await run('lookupRecordKeyReceipt', afterRecordKeyReceiptOverwrite, receiptKeyA))[0],
    receipt(202, false),
  );
  assert.deepEqual(
    (await run('lookupRecordKeyReceipt', afterRecordKeyReceiptOverwrite, receiptKeyB))[0],
    receipt(303, true),
  );

  await assert.rejects(() => run('lookup', afterOverwrite, 13n));
  await assert.rejects(() => run('lookupBytes', afterByteOverwrite, missingByteKey));

  await assert.rejects(() => run('lookupRecordKey', afterRecordKeyOverwrite, missingRecordKey));
  await assert.rejects(() => run(
    'lookupRecordKeyReceipt', afterRecordKeyReceiptOverwrite, missingReceiptKey,
  ));

  const wrongNominalSource = join(scratch, 'WrongNominalMapKey.compact');
  writeFileSync(wrongNominalSource, `pragma language_version 0.28;
import CompactStandardLibrary;
struct Key { active: Boolean; epoch: Uint<16>; }
struct OtherKey { active: Boolean; epoch: Uint<16>; }
export ledger values: Map<Key, Uint<16>>;
export circuit insertWrongKey(key: OtherKey): [] {
  values.insert(disclose(key), 1 as Uint<16>);
  return [];
}
`);
  const wrongNominalCompile = spawnSync(compactc, [
    '--skip-zk', wrongNominalSource, join(scratch, 'wrong-nominal-compact'),
  ], {cwd: projectRoot, encoding: 'utf8'});
  assert.notEqual(wrongNominalCompile.status, 0,
    'Compact must reject a same-layout record with the wrong nominal Map key');

  const wrongValueSource = join(scratch, 'WrongNominalMapValue.compact');
  writeFileSync(wrongValueSource, `pragma language_version 0.28;
import CompactStandardLibrary;
struct Key { active: Boolean; epoch: Uint<16>; }
struct Receipt { amount: Field; active: Boolean; }
struct OtherReceipt { amount: Field; active: Boolean; }
export ledger values: Map<Key, Receipt>;
export circuit insertWrongValue(key: Key, next: OtherReceipt): [] {
  values.insert(disclose(key), disclose(next));
  return [];
}
`);
  const wrongValueCompile = spawnSync(compactc, [
    '--skip-zk', wrongValueSource, join(scratch, 'wrong-value-compact'),
  ], {cwd: projectRoot, encoding: 'utf8'});
  assert.notEqual(wrongValueCompile.status, 0,
    'Compact must reject a same-layout record with the wrong nominal Map value');

  console.log(`Compact ${compilerVersion} matched guarded generic Maps for Field, Bytes<32>, checked record keys, and checked record keys with record values, and rejected wrong nominal record keys and values`);
} finally {
  rmSync(scratch, {recursive: true, force: true});
  try {
    rmdirSync(experiments);
  } catch (error) {
    if (error.code !== 'ENOENT' && error.code !== 'ENOTEMPTY') throw error;
  }
}
