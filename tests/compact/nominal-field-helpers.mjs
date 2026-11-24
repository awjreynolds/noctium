import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/nominal-field-helpers.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const runtime = resolve(runtimePath);
const version = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(version, /^0\.36\.1 \(7fa3a117c/);
assert.equal(JSON.parse(readFileSync(join(runtime, 'package.json'), 'utf8')).version, '0.21.0');

const testDir = dirname(fileURLToPath(import.meta.url));
const experiments = resolve(testDir, '../../build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'nominal-field-helpers-'));
try {
  const generated = join(scratch, 'reference');
  execFileSync(compactc, ['--skip-zk', join(testDir, 'NominalFieldHelpers.compact'), generated]);
  const link = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(link), { recursive: true });
  symlinkSync(runtime, link, 'dir');
  const { pureCircuits } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  assert.equal(pureCircuits.forwardAmount(19n), 19n);
  assert.equal(pureCircuits.castInput(19n), 19n);
  assert.equal(pureCircuits.castOutput(19n), 19n);

  const badSource = join(scratch, 'distinct-aliases.compact');
  const badOutput = join(scratch, 'bad');
  const source = readFileSync(join(testDir, 'NominalFieldHelpers.compact'), 'utf8')
    .replace('export pure circuit castOutput(raw: Field): Amount { return raw as Amount; }',
      'export pure circuit invalid(value: Count): Amount { return identityAmount(value); }');
  writeFileSync(badSource, source);
  const rejected = spawnSync(compactc, ['--skip-zk', badSource, badOutput], { encoding: 'utf8' });
  assert.notEqual(rejected.status, 0);
  assert.match(rejected.stderr + rejected.stdout, /incompatible|expected.*Amount|Count/);
  console.log(`Compact ${version} matched helper forwarding and explicit nominal Field casts`);
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
