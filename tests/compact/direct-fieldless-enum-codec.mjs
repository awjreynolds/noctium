import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/direct-fieldless-enum-codec.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

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
const scratch = mkdtempSync(join(experiments, 'direct-fieldless-enum-codec-'));

try {
  const generated = join(scratch, 'compact');
  const source = join(projectRoot, 'tests/compact/DirectFieldlessEnumCodec.compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');
  const { versionString } = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  assert.equal(versionString, '0.21.0');
  const { pureCircuits } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);

  const [exactOrdinal, paddedOrdinal, decoded] = pureCircuits.serializeDone();
  assert.deepEqual(exactOrdinal, Uint8Array.of(1));
  assert.deepEqual(paddedOrdinal, Uint8Array.of(1, 0));
  assert.equal(decoded, 1);
  assert.equal(pureCircuits.deserializeStatus(exactOrdinal), 1);
  assert.throws(() => pureCircuits.deserializeStatus(Uint8Array.of(2)));
  assert.equal(pureCircuits.deserializePaddedStatus(paddedOrdinal), 1);
  assert.equal(pureCircuits.deserializePaddedStatus(Uint8Array.of(1, 9)), 1);

  console.log(JSON.stringify({
    fixture: 'DirectFieldlessEnumCodec',
    compact: compilerVersion,
    runtime: runtimePackage.version,
    enum: { name: 'Status', members: ['Pending', 'Done'] },
    doneOrdinal: 1,
    exactEncoding: Array.from(exactOrdinal),
    paddedEncoding: Array.from(paddedOrdinal),
    decodedDone: decoded,
    ignoresTrailingPadding: true,
    ordinalTwoRejected: true,
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
