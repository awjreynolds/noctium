import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/nominal-uint.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const runtime = resolve(runtimePath);
const version = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(version, /^0\.36\.1 \(7fa3a117c/);
assert.equal(JSON.parse(readFileSync(join(runtime, 'package.json'), 'utf8')).version, '0.21.0');

const testDir = dirname(fileURLToPath(import.meta.url));
const experiments = resolve(testDir, '../../build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'nominal-uint-'));
try {
  const generated = join(scratch, 'reference');
  execFileSync(compactc, ['--skip-zk', join(testDir, 'NominalUint.compact'), generated]);

  const rejectedCases = [
    ['mixed-types', 'new type Count = Uint<8>;',
      'pure circuit invalid(x: Amount, y: Count): Amount { return x + y; }',
      /incompatible combination of types Amount and Count/],
    ['implicit-unwrap', '',
      'pure circuit invalid(x: Amount): Uint<8> { return x; }',
      /mismatch between actual return type Amount and declared return type Uint<8>/],
    ['implicit-wrap', '',
      'pure circuit invalid(x: Uint<8>): Amount { return x; }',
      /mismatch between actual return type Uint<8> and declared return type Amount/],
    ['intermediate-width', 'new type Wide = Uint<248>;',
      'pure circuit invalid(x: Wide, y: Wide): Wide { return x + y; }',
      /resulting value might exceed largest representable Uint value/],
  ];
  for (const [name, extra, circuit, diagnostic] of rejectedCases) {
    const source = join(scratch, name + '.compact');
    writeFileSync(source, ['pragma language_version 0.28;', 'new type Amount = Uint<8>;',
      extra, 'export ' + circuit].join('\n') + '\n');
    const result = spawnSync(compactc, ['--skip-zk', source, join(scratch, name)], { encoding: 'utf8' });
    assert.notEqual(result.status, 0, name);
    assert.match(result.stderr + result.stdout, diagnostic, name);
  }

  const link = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(link), { recursive: true });
  symlinkSync(runtime, link, 'dir');
  const { pureCircuits } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  assert.equal(pureCircuits.addAmount(1n, 1n), 2n);
  assert.equal(pureCircuits.addAmount(255n, 0n), 255n);
  assert.throws(() => pureCircuits.addAmount(255n, 1n), /greater than 255/);
  assert.equal(pureCircuits.toUnderlying(9n), 9n);
  assert.equal(pureCircuits.toAmount(255n), 255n);
  assert.throws(() => pureCircuits.toAmount(256n), /greater than 255/);
  console.log(`Compact ${version} matched nominal UInt identity and checked narrowing cases`);
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
