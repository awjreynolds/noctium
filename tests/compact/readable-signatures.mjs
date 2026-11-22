import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/readable-signatures.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, '612-readable-signatures-compact-'));
try {
  const generated = join(scratch, 'compact');
  const source = join(root, 'tests/compact/ReadableSignatures.compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, compile.stderr || compile.stdout);
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(resolve(runtimeDirectory), runtimeLink, 'dir');

  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  const { pureCircuits } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const { ed25519 } = await import(pathToFileURL(resolve(
    runtimeDirectory,
    '../../@noble/curves/ed25519.js',
  )).href);

  const messages = [11n, 22n];
  const signingKey = 3n;
  const publicKey = runtime.jubjubSchnorrVerifyingKey(signingKey);
  const signature = runtime.jubjubSchnorrSign(
    new runtime.CompactTypeVector(2, runtime.CompactTypeField),
    messages,
    signingKey,
  );
  assert.equal(pureCircuits.verifySchnorr(messages, signature, publicKey), true,
    'Schnorr known message');
  assert.equal(pureCircuits.verifySchnorr([12n, 22n], signature, publicKey), false,
    'Schnorr changed message');

  const point = (hex) => ed25519.Point.fromHex(hex).toAffine();
  const littleEndianScalar = (hex) => {
    const bytes = Buffer.from(hex, 'hex');
    return BigInt(`0x${Buffer.from(bytes).reverse().toString('hex')}`);
  };
  const edSignature = {
    r: point('e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e06522490155'),
    s: littleEndianScalar('5fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b'),
  };
  const edKey = point('d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a');
  assert.equal(pureCircuits.verifyEd25519Empty(new Uint8Array(), edSignature, edKey), true,
    'Ed25519 empty-message vector');
  assert.equal(pureCircuits.verifyEd25519OneByte(new Uint8Array([0]), edSignature, edKey), false,
    'Ed25519 changed-message vector');

  console.log(JSON.stringify({
    compact: compilerVersion,
    runtime: runtimePackage.version,
    schnorr: { valid: true, changedMessage: false },
    ed25519: { emptyMessage: true, changedMessage: false },
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
