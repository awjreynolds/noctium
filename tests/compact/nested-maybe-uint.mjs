import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import {
  mkdirSync,
  mkdtempSync,
  readFileSync,
  readdirSync,
  rmSync,
  symlinkSync,
} from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/nested-maybe-uint.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compactVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compactVersion, /^0\.36\.1 \(7fa3a117c/,
  `expected pinned Compact 0.36.1 compiler, got ${compactVersion}`);
const runtimeDirectory = resolve(runtimePath);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0', 'expected pinned Compact runtime 0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/NestedMaybeUInt.compact');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'nested-maybe-uint-'));

const cases = [
  { outer: false, inner: true, value: 255, expected: { is_some: false, value: { is_some: false, value: 0n } } },
  { outer: true, inner: false, value: 255, expected: { is_some: true, value: { is_some: false, value: 0n } } },
  { outer: true, inner: true, value: 0, expected: { is_some: true, value: { is_some: true, value: 0n } } },
  { outer: true, inner: true, value: 255, expected: { is_some: true, value: { is_some: true, value: 255n } } },
];

try {
  const generated = join(scratch, 'compact');
  execFileSync(compactc, [source, generated], { encoding: 'utf8' });
  const info = JSON.parse(readFileSync(join(generated, 'compiler/contract-info.json'), 'utf8'));
  const { pure, proof } = info.circuits.find(circuit => circuit.name === 'inspect');
  const relationFiles = readdirSync(generated, { recursive: true })
    .filter(file => /\.(?:zkir|bzkir|pkey|prover|verifier)$/i.test(file));
  assert.deepEqual({ pure, proof, relationFiles }, { pure: true, proof: false, relationFiles: [] });

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');
  const { pureCircuits } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const results = [];
  for (const testCase of cases) {
    const result = pureCircuits.inspect(testCase.outer, testCase.inner, BigInt(testCase.value));
    assert.deepEqual(result, testCase.expected);
    results.push({
      outer: testCase.outer,
      inner: testCase.inner,
      value: testCase.value,
      result: {
        is_some: result.is_some,
        value: {
          is_some: result.value.is_some,
          value: Number(result.value.value),
        },
      },
    });
  }
  console.log(JSON.stringify({
    compactVersion,
    runtimeVersion: runtimePackage.version,
    pure,
    proof,
    relationFiles,
    cases: results,
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
