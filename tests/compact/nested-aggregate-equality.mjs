import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/nested-aggregate-equality.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'nested-aggregate-equality-'));
try {
  const generated = join(scratch, 'compact');
  execFileSync(compactc, [
    '--skip-zk', join(root, 'tests/compact/NestedAggregateEquality.compact'), generated,
  ], { encoding: 'utf8' });
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const { pureCircuits } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const sample = {
    head: 11n,
    inner: { octets: Uint8Array.of(1, 2), enabled: true, amount: 5n },
    pair: [31n, [41n, 42n]],
    bytes: Uint8Array.of(9, 8),
    kind: 2,
  };
  const changes = {
    head: (value) => { value.head = 12n; },
    innerOctets: (value) => { value.inner.octets = Uint8Array.of(1, 3); },
    innerEnabled: (value) => { value.inner.enabled = false; },
    innerAmount: (value) => { value.inner.amount = 6n; },
    pairField: (value) => { value.pair[0] = 32n; },
    vectorFirst: (value) => { value.pair[1][0] = 40n; },
    vectorSecond: (value) => { value.pair[1][1] = 43n; },
    bytes: (value) => { value.bytes = Uint8Array.of(9, 7); },
    kind: (value) => { value.kind = 1; },
  };
  assert.equal(pureCircuits.equal(sample, structuredClone(sample)), true);
  const results = Object.fromEntries(Object.entries(changes).map(([name, change]) => {
    const changed = structuredClone(sample);
    change(changed);
    const equal = pureCircuits.equal(sample, changed);
    assert.equal(equal, false, `${name} change must make nested samples unequal`);
    return [name, equal];
  }));
  console.log(JSON.stringify({
    compiler: compilerVersion,
    runtime: runtimePackage.version,
    circuit: 'equal(left: Sample, right: Sample)',
    layout: ['head: Field', 'inner.octets: Bytes<2>', 'inner.enabled: Boolean',
      'inner.amount: Uint<8>', 'pair: [Field, Vector<2, Field>]', 'bytes: Bytes<2>', 'kind: Kind'],
    input: {
      head: '11',
      inner: { octets: [1, 2], enabled: true, amount: '5' },
      pair: ['31', ['41', '42']],
      bytes: [9, 8],
      kind: 2,
    },
    selfEquality: true,
    changedFieldResults: results,
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
