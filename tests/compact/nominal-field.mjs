import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/nominal-field.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const runtime = resolve(runtimePath);
const version = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(version, /^0\.36\.1 \(7fa3a117c/);
assert.equal(JSON.parse(readFileSync(join(runtime, 'package.json'), 'utf8')).version, '0.21.0');

const testDir = dirname(fileURLToPath(import.meta.url));
const experiments = resolve(testDir, '../../build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'nominal-field-'));
try {
  const generated = join(scratch, 'reference');
  execFileSync(compactc, ['--skip-zk', join(testDir, 'NominalField.compact'), generated]);

  const badSource = join(scratch, 'distinct-aliases.compact');
  const badOutput = join(scratch, 'bad');
  writeFileSync(badSource, [
    'pragma language_version 0.28;',
    'import CompactStandardLibrary;',
    'new type Amount = Field;',
    'new type Count = Field;',
    'export pure circuit invalid(x: Amount, y: Count): Amount { return x + y; }',
    '',
  ].join('\n'));
  const rejected = spawnSync(compactc, ['--skip-zk', badSource, badOutput], { encoding: 'utf8' });
  assert.notEqual(rejected.status, 0);
  assert.match(rejected.stderr + rejected.stdout,
    /incompatible combination of types Amount and Count/);

  const link = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(link), { recursive: true });
  symlinkSync(runtime, link, 'dir');
  const { pureCircuits } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const modulus = 52435875175126190479447740508185965837690552500527637822603658699938581184513n;
  assert.equal(pureCircuits.addAmount(modulus - 1n, 1n), 0n);
  assert.equal(pureCircuits.subAmount(0n, 1n), modulus - 1n);
  assert.equal(pureCircuits.mulAmount(modulus - 1n, 2n), modulus - 2n);
  assert.equal(pureCircuits.asField(7n), 7n);
  assert.equal(pureCircuits.asAmount(7n), 7n);
  console.log(`Compact ${version} matched nominal Field arithmetic, explicit casts, and distinct alias rejection`);
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
