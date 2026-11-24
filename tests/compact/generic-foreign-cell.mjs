import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import {
  mkdirSync,
  mkdtempSync,
  readFileSync,
  rmSync,
  symlinkSync,
  writeFileSync,
} from 'node:fs';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/generic-foreign-cell.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compilerVersion = execFileSync(compactc, ['--version', '--verbose'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^release:\s+0\.36\.1$/m);
assert.match(compilerVersion, /^commit-hash:\s+7fa3a117c5e7efe9d2c51da04263e5f0b3509144$/m);
const runtimeDirectory = resolve(runtimePath);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/GenericForeignCell.compact');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'generic-foreign-cell-'));

function compile(input, output) {
  return spawnSync(compactc, ['--skip-zk', input, output], { encoding: 'utf8' });
}

function normalize(value) {
  if (typeof value === 'bigint') return value.toString();
  if (ArrayBuffer.isView(value)) return Array.from(value, normalize);
  if (Array.isArray(value)) return value.map(normalize);
  if (value && typeof value === 'object') {
    return Object.fromEntries(Object.entries(value).map(([key, child]) => [key, normalize(child)]));
  }
  return value;
}

try {
  const generated = join(scratch, 'compact');
  const result = compile(source, generated);
  assert.equal(result.status, 0, `Compact compilation failed:\n${result.stderr || result.stdout}`);

  const manifestPath = join(generated, 'compiler/contract-info.json');
  const manifest = JSON.parse(readFileSync(manifestPath, 'utf8'));
  assert.equal(manifest['compiler-version'], '0.36.1');
  assert.equal(manifest['compiler-commit'], '7fa3a117c5e7efe9d2c51da04263e5f0b3509144');

  const types = [
    ['Secp256k1Base', 'secp256k1Base', 1n, 2n],
    ['Secp256k1Scalar', 'secp256k1Scalar', 37n, 41n],
    ['Secp256k1Point', 'secp256k1Point', null, null],
    ['Secp256r1Base', 'secp256r1Base', 3n, 5n],
    ['Secp256r1Scalar', 'secp256r1Scalar', 4n, 8n],
    ['Secp256r1Point', 'secp256r1Point', null, null],
    ['Curve25519Base', 'curve25519Base', 5n, 7n],
    ['Curve25519Scalar', 'curve25519Scalar', 6n, 9n],
    ['Curve25519Point', 'curve25519Point', null, null],
  ];
  const circuits = new Map(manifest.circuits.map(circuit => [circuit.name, circuit]));
  for (const [type, prefix] of types) {
    for (const [direction, args, result] of [
      ['read', 0, type],
      ['update', 1, type],
    ]) {
      const name = `${direction}${type}`;
      const circuit = circuits.get(name);
      assert.ok(circuit, `missing ${name} circuit`);
      assert.equal(circuit.arguments.length, args, `${name} argument count`);
      if (args === 1) {
        assert.equal(circuit.arguments[0].type['type-name'], type, `${name} argument type`);
      }
      assert.equal(circuit['result-type']['type-name'], result, `${name} result type`);
    }
    assert.ok(circuits.has(`update${type}`));
    assert.match(readFileSync(join(generated, 'contract/index.d.ts'), 'utf8'),
      new RegExp(`\\b(read|update)${type}\\(`));
  }

  const wrongFamily = join(scratch, 'wrong-family.compact');
  const wrongFamilyOutput = join(scratch, 'wrong-family-output');
  writeFileSync(wrongFamily, `${readFileSync(source, 'utf8')}\nexport circuit rejectWrongFamily(
  next: Secp256r1Point
): Secp256k1Point {
  return secp256k1Point_update(disclose(next));
}\n`);
  const wrongFamilyResult = compile(wrongFamily, wrongFamilyOutput);
  assert.notEqual(wrongFamilyResult.status, 0,
    'Compact accepted a Secp256r1Point value for a Secp256k1Point Cell');
  const wrongFamilyDiagnostic = `${wrongFamilyResult.stderr}\n${wrongFamilyResult.stdout}`;
  assert.match(wrongFamilyDiagnostic, /Secp256r1Point|Secp256k1Point|type mismatch/i,
    'wrong-family rejection did not identify the point types');

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');
  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  assert.equal(runtime.versionString, '0.21.0');
  const { Contract, ledger } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const values = [
    { initial: 1n, next: 2n },
    { initial: 37n, next: 41n },
    { initial: runtime.secp256k1MulGenerator(1n), next: runtime.secp256k1MulGenerator(2n) },
    { initial: 3n, next: 5n },
    { initial: 4n, next: 8n },
    { initial: runtime.secp256r1MulGenerator(1n), next: runtime.secp256r1MulGenerator(2n) },
    { initial: 5n, next: 7n },
    { initial: 6n, next: 9n },
    { initial: runtime.curve25519MulGenerator(1n), next: runtime.curve25519MulGenerator(2n) },
  ];
  const contract = new Contract({});
  const wallet = '00'.repeat(32);
  const initial = await contract.initialState(
    runtime.createConstructorContext(null, wallet),
    ...values.map(value => value.initial),
  );
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

  let state = initial.currentContractState.data;
  const outcomes = [];
  for (let index = 0; index < types.length; index++) {
    const [type, prefix] = types[index];
    const field = `${prefix}_value`;
    const stored = ledger(state)[field];
    assert.deepEqual(stored, values[index].initial, `${type} constructor value`);
    const [readValue] = await run(`read${type}`, state);
    assert.deepEqual(readValue, values[index].initial, `${type} initial read`);

    const [updatedValue, updatedState] = await run(`update${type}`, state, values[index].next);
    assert.deepEqual(updatedValue, values[index].next, `${type} update result`);
    assert.deepEqual(ledger(updatedState)[field], values[index].next, `${type} stored update`);
    const [readBack] = await run(`read${type}`, updatedState);
    assert.deepEqual(readBack, values[index].next, `${type} read after update`);
    state = updatedState;
    outcomes.push({
      type,
      initial: normalize(values[index].initial),
      update: normalize(values[index].next),
      readBack: normalize(readBack),
    });
  }

  console.log(JSON.stringify({
    fixture: 'GenericForeignCell',
    compiler: compilerVersion,
    runtime: runtimePackage.version,
    foreignCells: outcomes,
    wrongFamilyValueRejected: true,
  }));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
