import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/pure-helpers.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
assert.match(execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim(), /^0\.36\.1 \(7fa3a117c/);
const runtime = resolve(runtimePath);
const runtimePackage = JSON.parse(readFileSync(join(runtime, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'declared-pure-'));
const compile = (source, output) => spawnSync(compactc, ['--skip-zk', source, output], { encoding: 'utf8' });

try {
  const generated = join(scratch, 'pure');
  const result = compile(join(root, 'tests/compact/PureHelpers.compact'), generated);
  assert.equal(result.status, 0, result.stderr || result.stdout);
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtime, runtimeLink, 'dir');
  const { pureCircuits } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  assert.equal(pureCircuits.calculate(7n, 7n), 8n);
  assert.equal(pureCircuits.calculate(255n, 255n), 256n);
  assert.throws(() => pureCircuits.calculate(7n, 8n), /expected a matching value/);
  assert.throws(() => pureCircuits.calculate(256n, 256n));

  for (const [name, declaration, effect] of [
    ['witness', 'witness secret(): Field;', 'secret();'],
    ['ledger-read', 'ledger total: Counter;', 'total.read();'],
    ['ledger-write', 'ledger total: Counter;', 'total.increment(1);'],
    ['event', '', 'emit(Paused {});'],
  ]) {
    const source = join(scratch, name + '.compact');
    writeFileSync(source, `pragma language_version 0.28;
import CompactStandardLibrary;
${declaration}
circuit impure(): [] { ${effect} }
export pure circuit check(): [] {
  if (false) {
    impure();
  }
}
`);
    const result = compile(source, join(scratch, name));
    assert.ok(result.status !== null && result.status !== 0, name + ' unexpectedly compiled');
    assert.match(result.stderr, /is marked pure but is actually impure/, name);
  }
  console.log('Compact 0.36.1 matched pure calls and rejected each inactive transitive effect');
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
