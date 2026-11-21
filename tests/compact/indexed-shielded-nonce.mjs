import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/indexed-shielded-nonce.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(root, 'tests/compact/IndexedShieldedNonce.compact');
const experiments = join(root, 'build/experiments/308');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'indexed-shielded-nonce-compact-'));
try {
  const generated = join(scratch, 'compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, compile.stderr || compile.stdout);
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');
  const { pureCircuits } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  assert.deepEqual(pureCircuits.burnRecipient(), [
    true, new Uint8Array(32), new Uint8Array(32),
  ]);

  const index = (1n << 128n) - 1n;
  const zeroIndex = 0n;
  const nonce = Uint8Array.from({ length: 32 }, (_, offset) => offset + 1);
  const nonceWithDifferentHighByte = nonce.slice();
  nonceWithDifferentHighByte[31] ^= 0xff;
  const evolvedAtZero = pureCircuits.indexedNonce(zeroIndex, nonce);
  const evolved = pureCircuits.indexedNonce(index, nonce);
  const evolvedWithDifferentHighByte = pureCircuits.indexedNonce(index, nonceWithDifferentHighByte);
  assert.notDeepEqual(evolvedAtZero, evolved);
  assert.deepEqual(evolvedWithDifferentHighByte, evolved);
  console.log(JSON.stringify({
    fixture: 'IndexedShieldedNonce',
    compact: compilerVersion,
    nonce: Buffer.from(nonce).toString('hex'),
    nonceWithDifferentHighByte: Buffer.from(nonceWithDifferentHighByte).toString('hex'),
    indexZero: {
      index: zeroIndex.toString(),
      evolvedNonce: Buffer.from(evolvedAtZero).toString('hex'),
    },
    indexMaximum: {
      index: index.toString(),
      evolvedNonce: Buffer.from(evolved).toString('hex'),
    },
    changedHighByte: {
      index: index.toString(),
      evolvedNonce: Buffer.from(evolvedWithDifferentHighByte).toString('hex'),
    },
  }));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
