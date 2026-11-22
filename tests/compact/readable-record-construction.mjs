import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { pathToFileURL } from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/readable-record-construction.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const version = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(version, /^0\.36\.1 \(7fa3a117c/, `expected pinned Compact 0.36.1 compiler, got ${version}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0', 'expected pinned Compact runtime 0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/ReadableRecordConstruction.compact');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'readable-record-construction-'));

try {
  const generated = join(scratch, 'compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');
  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  assert.equal(runtime.versionString, '0.21.0');
  const { createCircuitContext, createConstructorContext, dummyContractAddress } = runtime;
  const { Contract } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);

  const calls = [];
  const contract = new Contract({
  observeActive: ({ privateState }, value) => {
    calls.push(['active', value]);
    return [privateState, true];
  },
  observeCount: ({ privateState }, value) => {
    calls.push(['count', value]);
    return [privateState, 17n];
  },
  observeReading: ({ privateState }, value) => {
    calls.push(['reading', value]);
    return [privateState, 9n];
  },
  loadBase: ({ privateState }, value) => {
    calls.push(['base', value]);
    return [privateState, { reading: 13n, count: 19n, active: false }];
  },
  loadPair: ({ privateState }, value) => {
    calls.push(['pair', value]);
    return [privateState, [11n, true]];
  },
  loadVector: ({ privateState }, value) => {
    calls.push(['vector', value]);
    return [privateState, [17n, 19n]];
  },
  loadBytes: ({ privateState }, value) => {
    calls.push(['bytes', value]);
    return [privateState, new Uint8Array([165, 60])];
  },
  loadUnit: ({ privateState }, value) => {
    calls.push(['unit', value]);
    return [privateState, []];
  },
  });
  const wallet = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(createConstructorContext([], wallet));
  const context = circuitId => createCircuitContext({
    circuitId,
    contractAddress: dummyContractAddress(),
    coinPublicKeyOrZswapState: wallet,
    contractState: currentContractState.data,
    privateState: null,
  });
  const { result } = await contract.circuits.build(context('build'), 7n);

  assert.deepEqual(calls, [['reading', 10n], ['count', 9n], ['active', 8n]]);
  assert.deepEqual(result, { reading: 9n, count: 17n, active: true });
  const constructionCalls = calls.splice(0);
  const { result: spread } = await contract.circuits.patch(context('patch'), 7n);
  assert.deepEqual(calls, [['base', 7n], ['count', 9n], ['active', 8n], ['base', 10n]]);
  assert.deepEqual(spread, { reading: 13n, count: 17n, active: true });
  const recordSpreadCalls = calls.splice(0);
  const { result: tuple } = await contract.circuits.spreadTuple(context('spreadTuple'), 7n);
  assert.deepEqual(calls, [['pair', 8n], ['vector', 9n], ['bytes', 10n], ['unit', 11n]]);
  assert.deepEqual(tuple, [[7n, 11n, true], [17n, 19n, 165n, 60n], [true, 1n]]);
  const tupleSpreadCalls = calls.splice(0);
  const { result: packedOctets } = await contract.circuits.packOctets(context('packOctets'), 7n);
  assert.deepEqual(calls, [['vector', 9n], ['bytes', 10n], ['unit', 11n]]);
  assert.deepEqual([...packedOctets], [23, 60, 165, 19, 17, 7]);
  const packCalls = calls.splice(0);
  const { result: slicedSequences } = await contract.circuits.sliceSequences(context('sliceSequences'), 7n);
  assert.deepEqual(calls, [['pair', 8n], ['vector', 9n], ['pair', 10n], ['bytes', 11n]]);
  assert.deepEqual(slicedSequences, [[true], [19n], [], new Uint8Array([60])]);
  const sequenceSliceCalls = calls.splice(0);
  console.log(JSON.stringify({
    calls: constructionCalls.map(([name, value]) => [name, value.toString()]),
    result: { reading: result.reading.toString(), count: result.count.toString(), active: result.active },
    spread: {
      calls: recordSpreadCalls.map(([name, value]) => [name, value.toString()]),
      result: { reading: spread.reading.toString(), count: spread.count.toString(), active: spread.active },
    },
    tupleSpread: { calls: tupleSpreadCalls, result: tuple },
    packedOctets: { calls: packCalls, result: [...packedOctets] },
    sequenceSlice: {
      calls: sequenceSliceCalls,
      result: [[true], slicedSequences[1], slicedSequences[2], [...slicedSequences[3]]],
    },
  }, (_, value) => typeof value === 'bigint' ? value.toString() : value));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
