import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { mkdirSync, mkdtempSync, rmSync } from 'node:fs';

const [compactc] = process.argv.slice(2);
assert.ok(compactc, 'usage: node tests/compact/empty-range-purity.mjs <compactc-0.36.1>');

const version = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(version, /^0\.36\.1 \(7fa3a117c/, `unexpected Compact compiler: ${version}`);

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const fixtureDirectory = join(root, 'tests/compact');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'empty-range-purity-'));

function compile(sourceName, outputName) {
  return spawnSync(compactc, [
    '--skip-zk',
    join(fixtureDirectory, sourceName),
    join(scratch, outputName),
  ], { encoding: 'utf8' });
}

try {
  const ordinary = compile('EmptyRangeWitnessHelper.compact', 'ordinary');
  assert.equal(ordinary.status, 0,
    `ordinary helper should compile:\n${ordinary.stderr || ordinary.stdout}`);

  const pure = compile('EmptyRangePureWitnessHelper.compact', 'pure');
  assert.notEqual(pure.status, 0, 'pure helper with a witness call should be rejected');
  assert.match(pure.stderr || pure.stdout,
    /readSecretInEmptyRange is marked pure but is actually impure because it calls witness\s+secret/);
} finally {
  rmSync(scratch, { recursive: true, force: true });
}

console.log(`empty-range purity pair passed with Compact ${version}`);
