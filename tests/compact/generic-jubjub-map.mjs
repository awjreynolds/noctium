import assert from 'node:assert/strict';
import {execFileSync, spawnSync} from 'node:child_process';
import {dirname, join, resolve} from 'node:path';
import {fileURLToPath, pathToFileURL} from 'node:url';
import {mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync} from 'node:fs';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node generic-jubjub-map.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compilerVersion = execFileSync(compactc, ['--version'], {encoding: 'utf8'}).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/,
  `unexpected Compact compiler: ${compilerVersion}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/GenericJubjubMap.compact');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, {recursive: true});
const scratch = mkdtempSync(join(experiments, '1157-generic-jubjub-map-'));

try {
  const generated = join(scratch, 'compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], {
    cwd: projectRoot,
    encoding: 'utf8',
  });
  assert.equal(compile.status, 0,
    `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

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

  const readScalarMap = state => ledger(state).scalar_values;
  const readPointMap = state => ledger(state).point_values;
  const point = scalar => runtime.ecMulGenerator(scalar);
  const pointIdentity = {x: 0n, y: 1n};
  const scalarKeyA = 1n;
  const scalarKeyB = 2n;
  const scalarValueA = 5n;
  const scalarValueB = 17n;
  const scalarValueOverwrite = 23n;
  const pointKeyA = new Uint8Array(32).fill(1);
  const pointKeyB = new Uint8Array(32).fill(2);
  const missingPointKey = new Uint8Array(32).fill(3);
  const pointValueA = pointIdentity;
  const pointValueB = point(1n);
  const pointValueOverwrite = point(2n);

  let state = currentContractState.data;
  assert.equal(readScalarMap(state).size(), 0n);
  assert.equal(readPointMap(state).size(), 0n);

  [, state] = await run('scalar_put', state, scalarKeyA, scalarValueA);
  [, state] = await run('scalar_put', state, scalarKeyB, scalarValueB);
  let scalarEntries = readScalarMap(state);
  assert.equal(scalarEntries.size(), 2n);
  assert.equal(scalarEntries.member(scalarKeyA), true);
  assert.equal(scalarEntries.member(scalarKeyB), true);
  assert.equal(scalarEntries.lookup(scalarKeyA), scalarValueA);
  assert.equal(scalarEntries.lookup(scalarKeyB), scalarValueB);
  assert.equal((await run('scalar_lookup', state, scalarKeyA))[0], scalarValueA);
  assert.equal((await run('scalar_lookup', state, scalarKeyB))[0], scalarValueB);

  [, state] = await run('point_put', state, pointKeyA, pointValueA);
  [, state] = await run('point_put', state, pointKeyB, pointValueB);
  let pointEntries = readPointMap(state);
  assert.equal(pointEntries.size(), 2n);
  assert.equal(pointEntries.member(pointKeyA), true);
  assert.equal(pointEntries.member(pointKeyB), true);
  assert.deepEqual(pointEntries.lookup(pointKeyA), pointValueA);
  assert.deepEqual(pointEntries.lookup(pointKeyB), pointValueB);
  assert.deepEqual((await run('point_lookup', state, pointKeyA))[0], pointValueA);
  assert.deepEqual((await run('point_lookup', state, pointKeyB))[0], pointValueB);

  [, state] = await run('scalar_put', state, scalarKeyA, scalarValueOverwrite);
  scalarEntries = readScalarMap(state);
  assert.equal(scalarEntries.size(), 2n);
  assert.equal(scalarEntries.lookup(scalarKeyA), scalarValueOverwrite);
  assert.equal(scalarEntries.lookup(scalarKeyB), scalarValueB);
  assert.equal((await run('scalar_lookup', state, scalarKeyA))[0], scalarValueOverwrite);
  assert.equal((await run('scalar_lookup', state, scalarKeyB))[0], scalarValueB);

  [, state] = await run('point_put', state, pointKeyA, pointValueOverwrite);
  pointEntries = readPointMap(state);
  assert.equal(pointEntries.size(), 2n);
  assert.deepEqual(pointEntries.lookup(pointKeyA), pointValueOverwrite);
  assert.deepEqual(pointEntries.lookup(pointKeyB), pointValueB);
  assert.deepEqual((await run('point_lookup', state, pointKeyA))[0], pointValueOverwrite);
  assert.deepEqual((await run('point_lookup', state, pointKeyB))[0], pointValueB);
  await assert.rejects(() => run('point_lookup', state, missingPointKey));

  console.log(JSON.stringify({
    fixture: 'GenericJubjubMap',
    compiler: compilerVersion,
    runtime: runtimePackage.version,
    scalarMap: {
      keys: [scalarKeyA.toString(), scalarKeyB.toString()],
      valuesAfterOverwrite: [scalarValueOverwrite.toString(), scalarValueB.toString()],
    },
    pointMap: {
      keys: ['01'.repeat(32), '02'.repeat(32)],
      valuesAfterOverwrite: [pointValueOverwrite, pointValueB].map(({x, y}) => ({
        x: x.toString(), y: y.toString(),
      })),
    },
    missingPointKeyRejected: true,
  }, null, 2));
} finally {
  rmSync(scratch, {recursive: true, force: true});
}
