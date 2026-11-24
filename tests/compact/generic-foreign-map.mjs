import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/generic-foreign-map.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

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
const scratch = mkdtempSync(join(experiments, 'generic-foreign-map-'));

try {
  const source = join(projectRoot, 'tests/compact/GenericForeignMap.compact');
  const generated = join(scratch, 'compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], {
    cwd: projectRoot,
    encoding: 'utf8',
  });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const wrongFamilySource = join(scratch, 'GenericForeignMapWrongFamily.compact');
  writeFileSync(wrongFamilySource, `${readFileSync(source, 'utf8')}
export pure circuit wrongFamily(
  key: Secp256r1Point,
  next: Secp256r1Base
): Secp256r1Base {
  return secpPointToR1Base_insert(disclose(key), disclose(next));
}
`);
  const wrongFamily = spawnSync(compactc, ['--skip-zk', wrongFamilySource, join(scratch, 'wrong-family')], {
    cwd: projectRoot,
    encoding: 'utf8',
  });
  const wrongFamilyOutput = wrongFamily.stderr || wrongFamily.stdout;
  assert.notEqual(wrongFamily.status, 0, 'Compact accepted Secp256r1Point for Secp256k1Point map key');
  assert.match(wrongFamilyOutput, /(?:Secp256r1Point[\s\S]*Secp256k1Point|Secp256k1Point[\s\S]*Secp256r1Point)/,
    `expected a wrong-family key diagnostic, got:\n${wrongFamilyOutput}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');
  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  assert.equal(runtime.versionString, '0.21.0');
  const { Contract, ledger } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
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

  const secpKey = runtime.secp256k1MulGenerator(1n);
  const secpSibling = runtime.secp256k1MulGenerator(2n);
  const secpValue = 17n;
  const c255Key = 19n;
  const c255Sibling = 20n;
  const c255Value = runtime.curve25519MulGenerator(1n);
  const secpMap = state => ledger(state).secpPointToR1Base_values;
  const c255Map = state => ledger(state).c255ScalarToC255Point_values;

  let state = initial.currentContractState.data;
  assert.equal(secpMap(state).member(secpKey), false);
  const [secpInsertResult, afterSecpInsert] = await run(
    'insertSecpPointToR1Base', state, secpKey, secpValue,
  );
  assert.equal(secpInsertResult, secpValue);
  state = afterSecpInsert;
  const [secpReadResult, afterSecpRead] = await run('readSecpPointToR1Base', state, secpKey);
  assert.equal(secpReadResult, secpValue);
  state = afterSecpRead;
  assert.equal(secpMap(state).member(secpKey), true);
  assert.equal(secpMap(state).member(secpSibling), false);

  assert.equal(c255Map(state).member(c255Key), false);
  const [c255InsertResult, afterC255Insert] = await run(
    'insertC255ScalarToC255Point', state, c255Key, c255Value,
  );
  assert.deepEqual(c255InsertResult, c255Value);
  state = afterC255Insert;
  const [c255ReadResult, afterC255Read] = await run('readC255ScalarToC255Point', state, c255Key);
  assert.deepEqual(c255ReadResult, c255Value);
  state = afterC255Read;
  assert.equal(c255Map(state).member(c255Key), true);
  assert.equal(c255Map(state).member(c255Sibling), false);

  const pointJson = point => Object.fromEntries(
    Object.entries(point).map(([name, value]) => [name, value.toString()]),
  );
  console.log(JSON.stringify({
    fixture: 'GenericForeignMap',
    compact: compilerVersion,
    runtime: runtimePackage.version,
    secp256k1PointToSecp256r1Base: {
      key: pointJson(secpKey),
      siblingKey: pointJson(secpSibling),
      value: secpValue.toString(),
      insertResult: secpInsertResult.toString(),
      readResult: secpReadResult.toString(),
      present: secpMap(state).member(secpKey),
      siblingPresent: secpMap(state).member(secpSibling),
    },
    curve25519ScalarToCurve25519Point: {
      key: c255Key.toString(),
      siblingKey: c255Sibling.toString(),
      value: pointJson(c255Value),
      insertReadMatched: true,
      present: c255Map(state).member(c255Key),
      siblingPresent: c255Map(state).member(c255Sibling),
    },
    wrongFamilyKeyRejected: true,
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
