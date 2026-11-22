import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/nested-transient-hash.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'nested-transient-hash-'));
try {
  const generated = join(scratch, 'compact');
  execFileSync(compactc, [
    '--skip-zk', join(root, 'tests/compact/NestedTransientHash.compact'), generated,
  ], { encoding: 'utf8' });
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  const { pureCircuits } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  assert.equal(pureCircuits.hashEmpty([]), 0n);
  const value = {
    head: 11n,
    inner: { tag: Uint8Array.of(0x12, 0x34), enabled: true, amount: 513n },
    pair: [31n, [41n, 42n]],
    empty: [],
    tail: 99n,
  };
  const orderedValues = [
    ...runtime.CompactTypeField.toValue(value.head),
    ...new runtime.CompactTypeBytes(2).toValue(value.inner.tag),
    ...runtime.CompactTypeBoolean.toValue(value.inner.enabled),
    ...new runtime.CompactTypeUnsignedInteger(65535n, 16).toValue(value.inner.amount),
    ...runtime.CompactTypeField.toValue(value.pair[0]),
    ...new runtime.CompactTypeVector(2, runtime.CompactTypeField).toValue(value.pair[1]),
    ...runtime.CompactTypeField.toValue(value.tail),
  ];
  const bytes = orderedValues.map((part) => [...part]);
  assert.deepEqual(bytes, [[11], [0x12, 0x34], [1], [1, 2], [31], [41], [42], [99]]);
  const actual = pureCircuits.hashNested(value);
  assert.equal(actual, 15768837897521911811722696040654606308073209539648838630070805017733391969083n);

  const changedOrder = {
    ...value,
    pair: [31n, [42n, 41n]],
  };
  const changedOrderHash = pureCircuits.hashNested(changedOrder);
  assert.equal(changedOrderHash, 16758168218473546073028353208286085426324112504107359563775906790860030679182n);
  assert.notEqual(changedOrderHash, actual);
  assert.equal(runtime.versionString, '0.21.0');
  console.log(JSON.stringify({ compiler: compilerVersion, runtime: runtime.versionString,
    orderedLeaves: ['Field 11', 'Bytes<2> 0x1234', 'Boolean true', 'Uint<16> 513',
      'Field 31', 'Field 41', 'Field 42', 'Field 99'],
    orderedFabValues: bytes,
    emptyVectorLeaves: 0,
    emptyHash: pureCircuits.hashEmpty([]).toString(),
    hash: actual.toString(), changedOrderHash: changedOrderHash.toString() }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
