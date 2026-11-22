import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/nominal-record-equality.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const version = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(version, /^0\.36\.1 \(7fa3a117c/);
const runtime = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtime.version, '0.21.0');

const sourceDirectory = dirname(fileURLToPath(import.meta.url));
const experiments = resolve(sourceDirectory, '../../build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'nominal-record-equality-'));
try {
  const generated = join(scratch, 'compact');
  execFileSync(compactc, ['--skip-zk', join(sourceDirectory, 'NominalRecordEquality.compact'), generated]);
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');
  const { pureCircuits } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const left = { reading: 9n, count: 17n, active: true };
  assert.equal(pureCircuits.compare(left, left), true);
  for (const changed of [{ reading: 10n }, { count: 18n }, { active: false }]) {
    assert.equal(pureCircuits.compare(left, { ...left, ...changed }), false);
  }
  console.log(`Compact ${version} matched equal records and rejected each different field`);
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
