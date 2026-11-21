import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/hash-domain-conversions.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.version, '0.21.0');
const runtime = await import(pathToFileURL(join(resolve(runtimeDirectory), 'dist/index.js')));
assert.equal(runtime.versionString, '0.21.0');

const modulus = 52435875175126190479447740508185965837690552500527637822603658699938581184513n;
const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(root, 'tests/compact/HashDomainConversions.compact');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'hash-domain-conversions-'));
try {
  const generated = join(scratch, 'compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, compile.stderr || compile.stdout);
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');
  const { pureCircuits } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);

  for (const [highByte, field] of [[0, 0n], [255, modulus - 1n]]) {
    const digest = new Uint8Array(32).fill(255);
    digest[31] = highByte;
    const degraded = runtime.degradeToTransient(digest);
    assert.equal(degraded, (1n << 248n) - 1n);
    assert.equal(pureCircuits.degrade(digest), degraded);

    const upgraded = Uint8Array.from({ length: 32 }, (_, index) =>
      index === 31 ? 0 : Number((field >> BigInt(8 * index)) & 255n));
    assert.deepEqual(runtime.upgradeFromTransient(field), upgraded);
    assert.deepEqual(pureCircuits.upgrade(field), upgraded);
  }

  assert.throws(() => runtime.upgradeFromTransient(modulus));
  assert.throws(() => pureCircuits.upgrade(modulus));
  const malformedDigest = new Uint8Array(31);
  assert.throws(() => runtime.degradeToTransient(malformedDigest));
  assert.throws(() => pureCircuits.degrade(malformedDigest));
  console.log(`Pinned Compact ${compilerVersion} conversion circuits match Compact runtime 0.21.0`);
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
