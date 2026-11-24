import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/checked-enum-casts.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'checked-enum-casts-'));
try {
  const generated = join(scratch, 'compact');
  execFileSync(compactc, [
    '--skip-zk', join(root, 'tests/compact/CheckedEnumCasts.compact'), generated,
  ], { encoding: 'utf8' });
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  assert.equal(runtime.versionString, '0.21.0');
  const { pureCircuits } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);

  assert.equal(pureCircuits.defaultKind(), 0);
  assert.equal(pureCircuits.fromField(0n), 0);
  assert.equal(pureCircuits.fromField(2n), 2);
  assert.equal(pureCircuits.fromUint(0n), 0);
  assert.equal(pureCircuits.fromUint(2n), 2);
  assert.throws(() => pureCircuits.fromField(3n), /greater than maximum enum value 2/);
  assert.throws(() => pureCircuits.fromUint(3n), /greater than maximum enum value 2/);
  assert.equal(pureCircuits.identity(2), 2);

  assert.equal(pureCircuits.toField(2), 2n);
  assert.equal(pureCircuits.toUint(2), 2n);
  assert.equal(pureCircuits.narrowKind(1), 1n);
  assert.throws(() => pureCircuits.narrowKind(2), /greater than 1/);

  console.log(JSON.stringify({
    compiler: compilerVersion,
    runtime: runtimePackage.version,
    enum: { name: 'Status', members: ['Pending', 'Review', 'Done'] },
    default: 0,
    casts: {
      fieldToEnum: { accepted: [0, 2], rejected: [3] },
      uintToEnum: { accepted: [0, 2], rejected: [3] },
      enumToSameEnum: { input: 2, output: 2 },
      enumToField: { input: 2, output: '2' },
      enumToUint2: { input: 2, output: '2' },
      enumToUint1: { accepted: [1], rejected: [2] },
    },
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
