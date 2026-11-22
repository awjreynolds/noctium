import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/maybe-bytes-curves.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compactVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compactVersion, /^0\.36\.1 \(7fa3a117c/, `unexpected Compact compiler: ${compactVersion}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/MaybeBytesCurves.compact');
const experiments = join(projectRoot, 'build/experiments/560');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'compact-maybe-bytes-curves-'));

try {
  const generated = join(scratch, 'compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  assert.equal(runtime.versionString, '0.21.0');
  const { pureCircuits } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);

  const bytes = Uint8Array.of(0, 145, 255);
  const jubjub = runtime.ecMulGenerator(1n);
  const secp256k1 = runtime.secp256k1MulGenerator(1n);
  const secpCompressed = `${(secp256k1.y & 1n) === 0n ? '02' : '03'}${
    secp256k1.x.toString(16).padStart(64, '0')
  }`;
  assert.equal(
    secpCompressed,
    '0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798',
  );

  const result = pureCircuits.inspect(bytes, jubjub, secp256k1);
  const jubjubIdentity = { x: 0n, y: 1n };
  const secp256k1Identity = { x: 0n, y: 0n, identity: true };
  const zeroBytes = new Uint8Array(3);
  const zeroBytes0 = new Uint8Array(0);
  assert.deepEqual(result, [
    { is_some: true, value: bytes },
    { is_some: false, value: zeroBytes },
    { is_some: true, value: jubjub },
    { is_some: false, value: jubjubIdentity },
    { is_some: true, value: secp256k1 },
    { is_some: false, value: secp256k1Identity },
    zeroBytes,
    jubjubIdentity,
    secp256k1Identity,
    { is_some: true, value: zeroBytes0 },
    { is_some: false, value: zeroBytes0 },
    zeroBytes0,
  ]);

  console.log(JSON.stringify({
    fixture: 'MaybeBytesCurves.inspect',
    compact: compactVersion,
    runtime: runtimePackage.version,
    someBytes3: { is_some: true, value: Array.from(bytes) },
    noneBytes3Default: Array.from(result[1].value),
    someJubjubGenerator: {
      is_some: true,
      value: { x: jubjub.x.toString(), y: jubjub.y.toString() },
    },
    noneJubjubIdentity: { is_some: false, value: { x: '0', y: '1' } },
    someSecp256k1Generator: {
      is_some: true,
      compressed: secpCompressed,
      value: { x: secp256k1.x.toString(), y: secp256k1.y.toString() },
    },
    noneSecp256k1Identity: {
      is_some: false,
      value: { x: '0', y: '0', identity: true },
    },
    someBytes0: { is_some: true, value: Array.from(result[9].value) },
    noneBytes0Default: Array.from(result[10].value),
  }));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
