import assert from 'node:assert/strict';
import {execFileSync, spawnSync} from 'node:child_process';
import {dirname, join, resolve} from 'node:path';
import {fileURLToPath, pathToFileURL} from 'node:url';
import {mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync} from 'node:fs';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/generic-foreign-curve-module.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version', '--verbose'], {encoding: 'utf8'}).trim();
assert.match(compilerVersion, /^release:\s+0\.36\.1$/m);
assert.match(compilerVersion, /^commit-hash:\s+7fa3a117c5e7efe9d2c51da04263e5f0b3509144$/m);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(root, 'tests/compact/GenericForeignCurveModule.compact');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, {recursive: true});
const scratch = mkdtempSync(join(experiments, '860-foreign-curve-module-'));
try {
  const generated = join(scratch, 'compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], {encoding: 'utf8'});
  assert.equal(compile.status, 0, compile.stderr || compile.stdout);

  const manifest = JSON.parse(readFileSync(
    join(generated, 'compiler/contract-info.json'), 'utf8'));
  assert.equal(manifest['compiler-version'], '0.36.1');
  assert.equal(manifest['compiler-commit'], '7fa3a117c5e7efe9d2c51da04263e5f0b3509144');
  const expectedTypes = [
    'Secp256k1Base', 'Secp256k1Scalar', 'Secp256k1Point',
    'Secp256r1Base', 'Secp256r1Scalar', 'Secp256r1Point',
    'Curve25519Base', 'Curve25519Scalar', 'Curve25519Point',
  ];
  assert.equal(manifest.circuits.length, expectedTypes.length);
  for (const type of expectedTypes) {
    const name = `${type[0].toLowerCase()}${type.slice(1)}Identity`;
    const circuit = manifest.circuits.find(entry => entry.name === name);
    assert.ok(circuit, `missing specialized circuit ${name}`);
    assert.equal(circuit.arguments.length, 1);
    assert.equal(circuit.arguments[0].name, 'value');
    assert.equal(circuit.arguments[0].type['type-name'], type);
    assert.equal(circuit['result-type']['type-name'], type);
  }

  const declarations = readFileSync(join(generated, 'contract/index.d.ts'), 'utf8');
  for (const type of expectedTypes) {
    const name = `${type[0].toLowerCase()}${type.slice(1)}Identity`;
    assert.match(declarations, new RegExp(`\\b${name}\\(`), `missing TypeScript export ${name}`);
  }

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), {recursive: true});
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');
  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  const {pureCircuits} = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const values = {
    secp256k1BaseIdentity: 1n,
    secp256k1ScalarIdentity: 37n,
    secp256k1PointIdentity: runtime.secp256k1MulGenerator(1n),
    secp256r1BaseIdentity: 3n,
    secp256r1ScalarIdentity: 4n,
    secp256r1PointIdentity: runtime.secp256r1MulGenerator(1n),
    curve25519BaseIdentity: 5n,
    curve25519ScalarIdentity: 6n,
    curve25519PointIdentity: runtime.curve25519MulGenerator(1n),
  };
  for (const [name, value] of Object.entries(values)) {
    assert.deepEqual(pureCircuits[name](value), value, `${name} changed its input`);
  }
  console.log(JSON.stringify({fixture: 'GenericForeignCurveModule', compilerVersion,
    runtime: runtimePackage.version,
    circuits: manifest.circuits.map(entry => `${entry.name}:${entry.arguments[0].type['type-name']}`)}));
} finally {
  rmSync(scratch, {recursive: true, force: true});
}
