import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/fixed-byte-collection-keys.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/,
  `expected pinned Compact 0.36.1 compiler, got ${compilerVersion}`);
const runtimeDirectory = resolve(runtimePath);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0', 'expected pinned Compact runtime 0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'fixed-byte-collection-keys-'));

try {
  const generated = join(scratch, 'compact');
  const source = join(projectRoot, 'tests/compact/FixedByteCollectionKeys.compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  assert.equal(runtime.versionString, '0.21.0');
  const { Contract } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const contract = new Contract({});
  const wallet = '00'.repeat(32);
  const initial = await contract.initialState(runtime.createConstructorContext(null, wallet));
  const run = async (circuitId, state, ...args) => {
    const context = runtime.createCircuitContext({
      circuitId,
      contractAddress: runtime.dummyContractAddress(),
      coinPublicKeyOrZswapState: wallet,
      contractState: state,
      privateState: null,
    });
    const call = await contract.circuits[circuitId](context, ...args);
    return [call.result, call.context.callContext.currentQueryContext.state];
  };

  const key0 = new Uint8Array(0);
  const key1 = Uint8Array.of(167);
  const key33 = Uint8Array.from({ length: 33 }, (_, index) => index + 1);
  const [insert0, state0] = await run('insertBytes0', initial.currentContractState.data, key0, 9n);
  assert.equal(insert0, 9n);
  const [insert1, state1] = await run('insertBytes1', state0, key1, 17n);
  assert.equal(insert1, 17n);
  const [insert33, state33] = await run('insertBytes33', state1, key33, 42n);
  assert.equal(insert33, 42n);

  const [read0, stateRead0] = await run('readBytes0', state33, key0);
  assert.equal(read0, 9n);
  const [read1, stateRead1] = await run('readBytes1', stateRead0, key1);
  assert.equal(read1, 17n);
  const [read33, stateRead33] = await run('readBytes33', stateRead1, key33);
  assert.equal(read33, 42n);

  const [setMember, stateSet] = await run('insertOneByteSet', stateRead33, key1);
  assert.equal(setMember, true);
  const [setRead] = await run('containsOneByteSet', stateSet, key1);
  assert.equal(setRead, true);

  const [nestedFirst, stateNestedFirst] = await run('insertNestedOneByteSet', stateSet, key0, key1);
  assert.deepEqual(nestedFirst, [false, false, true]);
  const [nestedDuplicate, stateNestedDuplicate] = await run(
    'insertNestedOneByteSet', stateNestedFirst, key0, key1);
  assert.deepEqual(nestedDuplicate, [true, true, true]);
  const [nestedSibling, stateNestedSibling] = await run(
    'insertNestedOneByteSet', stateNestedDuplicate, key0, Uint8Array.of(168));
  assert.deepEqual(nestedSibling, [true, false, true]);

  await assert.rejects(run('insertBytes0', stateSet, Uint8Array.of(1), 1n));
  await assert.rejects(run('insertBytes1', stateSet, Uint8Array.of(167, 1), 1n));
  await assert.rejects(run('insertBytes33', stateSet, key33.subarray(1), 1n));
  await assert.rejects(run('insertNestedOneByteSet', stateNestedSibling, Uint8Array.of(0), key1));
  await assert.rejects(run('insertNestedOneByteSet', stateNestedSibling, key0, Uint8Array.of(167, 168)));

  console.log(JSON.stringify({
    fixture: 'FixedByteCollectionKeys',
    compact: compilerVersion,
    runtime: runtimePackage.version,
    maps: [
      { keyType: 'Bytes<0>', key: [], valueType: 'Uint<8>', insertReturn: '9', readBack: '9' },
      { keyType: 'Bytes<1>', key: [167], valueType: 'Uint<8>', insertReturn: '17', readBack: '17' },
      { keyType: 'Bytes<33>', key: Array.from(key33), valueType: 'Field', insertReturn: '42', readBack: '42' },
    ],
    set: { keyType: 'Bytes<1>', key: [167], insertThenMember: true, readBack: true },
    nestedSet: {
      keyType: 'Map<Bytes<0>, Set<Bytes<1>>>',
      firstInsert: nestedFirst,
      duplicateInsert: nestedDuplicate,
      siblingInsert: nestedSibling,
      rejectedLengths: { parent: 1, member: 2 },
    },
    rejectedLengths: { bytes0: 1, bytes1: 2, bytes33: 32 },
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
