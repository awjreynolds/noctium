import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/nominal-uint-maybe.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/,
  `expected pinned Compact 0.36.1 compiler, got ${compilerVersion}`);
const runtimeDirectory = resolve(runtimePath);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0', 'expected pinned Compact runtime 0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'nominal-uint-maybe-'));

try {
  const generated = join(scratch, 'compact');
  const source = join(projectRoot, 'tests/compact/NominalUIntMaybe.compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const mismatchSource = join(scratch, 'NominalUIntMaybeMismatch.compact');
  writeFileSync(mismatchSource, `pragma language_version 0.28;
import CompactStandardLibrary;

new type Amount = Uint<8>;
new type Other = Uint<8>;

export pure circuit wrongSome(value: Amount): Maybe<Other> {
  return some<Other>(value);
}
`);
  const mismatch = spawnSync(compactc, ['--skip-zk', mismatchSource, join(scratch, 'mismatch')], {
    encoding: 'utf8',
  });
  const mismatchOutput = mismatch.stderr || mismatch.stdout;
  assert.notEqual(mismatch.status, 0, 'Compact accepted an Amount payload for Maybe<Other>');
  assert.match(mismatchOutput, /(?:Amount[\s\S]*Other|Other[\s\S]*Amount)/,
    `expected nominal Amount/Other mismatch diagnostic, got:\n${mismatchOutput}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');
  const { pureCircuits } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);

  const amountSome = pureCircuits.amountSome(37n);
  const amountNone = pureCircuits.amountNone();
  const otherSome = pureCircuits.otherSome(29n);
  const otherNone = pureCircuits.otherNone();
  assert.deepEqual(amountSome, { is_some: true, value: 37n });
  assert.deepEqual(pureCircuits.amountSome(0n), { is_some: true, value: 0n });
  assert.deepEqual(amountNone, { is_some: false, value: 0n });
  assert.deepEqual(otherSome, { is_some: true, value: 29n });
  assert.deepEqual(otherNone, { is_some: false, value: 0n });

  console.log(JSON.stringify({
    fixture: 'NominalUIntMaybe',
    compact: compilerVersion,
    runtime: runtimePackage.version,
    nominalTypes: { Amount: 'Uint<8>', Other: 'Uint<8>' },
    amountSome: { is_some: true, value: '37' },
    amountNone: { is_some: false, value: '0' },
    otherSome: { is_some: true, value: '29' },
    otherNone: { is_some: false, value: '0' },
    wrongNominalConstructorRejected: true,
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
