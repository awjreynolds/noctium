import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/nominal-scalar-serialization.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/);
const runtimeDirectory = resolve(runtimePath);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'nominal-scalar-serialization-'));
try {
  const source = join(root, 'tests/compact/NominalScalarSerialization.compact');
  const generated = join(scratch, 'compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');
  const { pureCircuits } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const [amountBytes, decodedAmount, smallBytes, decodedSmall] = pureCircuits.roundTrip(42n, 42n);
  const expectedAmountBytes = new Uint8Array(32);
  expectedAmountBytes[0] = 42;
  assert.deepEqual(amountBytes, expectedAmountBytes);
  assert.equal(decodedAmount, 42n);
  assert.deepEqual(smallBytes, Uint8Array.of(42));
  assert.equal(decodedSmall, 42n);
  assert.throws(() => pureCircuits.decodeSmall(Uint8Array.of(128)), /exceeds maximum value 127/);

  const validSource = readFileSync(source, 'utf8');
  const rejectedCases = [
    ['field-wrong-alias-result',
      'export pure circuit wrongAmountAlias(input: Bytes<32>): OtherAmount {\n' +
      '  return deserialize<Amount, 32>(input);\n}',
      /mismatch between actual return type Amount and declared return type OtherAmount/],
    ['field-raw-result',
      'export pure circuit rawAmountResult(input: Bytes<32>): Field {\n' +
      '  return deserialize<Amount, 32>(input);\n}',
      /mismatch between actual return type Amount and declared return type Field/],
    ['uint-wrong-alias-result',
      'export pure circuit wrongSmallAlias(input: Bytes<1>): OtherSmall {\n' +
      '  return deserialize<Small, 1>(input);\n}',
      /mismatch between actual return type Small and declared return type OtherSmall/],
    ['uint-raw-result',
      'export pure circuit rawSmallResult(input: Bytes<1>): Uint<7> {\n' +
      '  return deserialize<Small, 1>(input);\n}',
      /mismatch between actual return type Small and declared return type Uint<7>/],
  ];
  for (const [name, circuit, diagnostic] of rejectedCases) {
    const invalidSource = join(scratch, `${name}.compact`);
    writeFileSync(invalidSource, validSource + `\n${circuit}\n`);
    const rejected = spawnSync(compactc, ['--skip-zk', invalidSource, join(scratch, name)], {
      encoding: 'utf8',
    });
    assert.notEqual(rejected.status, 0, `${name} unexpectedly compiled`);
    assert.match(rejected.stderr + rejected.stdout, diagnostic, name);
  }

  console.log(JSON.stringify({
    fixture: 'NominalScalarSerialization', compact: compilerVersion, runtime: runtimePackage.version,
    aliases: { amount: 'Field', small: 'Uint<7>' },
    input: '42', amountBytesLE: Array.from(amountBytes), smallBytesLE: Array.from(smallBytes),
    decoded: { amount: decodedAmount.toString(), small: decodedSmall.toString() },
    small128Rejected: true, wrongAliasResultsRejected: true, rawResultsRejected: true,
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
