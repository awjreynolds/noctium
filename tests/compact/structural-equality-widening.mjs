import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/structural-equality-widening.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'structural-equality-widening-'));
try {
  const generated = join(scratch, 'compact');
  execFileSync(compactc, [
    '--skip-zk', join(root, 'tests/compact/StructuralEqualityWidening.compact'), generated,
  ], { encoding: 'utf8' });
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');
  const { pureCircuits } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);

  const vectors = {
    equal: pureCircuits.compareVectors([1n, 2n], [1n, 2n]),
    changedSecond: pureCircuits.compareVectors([1n, 2n], [1n, 3n]),
    widenedOutOfLeftRange: pureCircuits.compareVectors([1n, 2n], [1n, 256n]),
  };
  const tuples = {
    equal: pureCircuits.compareTuples([1n, 11n], [1n, 11n]),
    changedUInt: pureCircuits.compareTuples([1n, 11n], [2n, 11n]),
    changedField: pureCircuits.compareTuples([1n, 11n], [1n, 12n]),
  };
  assert.deepEqual(vectors, { equal: true, changedSecond: false, widenedOutOfLeftRange: false });
  assert.deepEqual(tuples, { equal: true, changedUInt: false, changedField: false });
  console.log(JSON.stringify({
    compiler: compilerVersion,
    runtime: runtimePackage.version,
    vectors: { left: 'Vector<2, Uint<8>>', right: 'Vector<2, Uint<16>>', results: vectors },
    tuples: { left: '[Uint<8>, Field]', right: '[Uint<16>, Field]', results: tuples },
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
