import assert from 'node:assert/strict';
import {execFileSync, spawnSync} from 'node:child_process';
import {mkdtempSync, mkdirSync, readFileSync, rmSync, symlinkSync, writeFileSync} from 'node:fs';
import {dirname, join, resolve} from 'node:path';
import {fileURLToPath, pathToFileURL} from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/field-arithmetic.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const version = execFileSync(compactc, ['--version'], {encoding: 'utf8'}).trim();
assert.match(version, /^0\.36\.1 \(7fa3a117c/, `expected pinned Compact 0.36.1 compiler, got ${version}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/FieldArithmetic.compact');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, {recursive: true});
const scratch = mkdtempSync(join(experiments, 'field-arithmetic-'));

function compile(sourcePath, target) {
  return spawnSync(compactc, ['--skip-zk', sourcePath, target], {encoding: 'utf8'});
}

function rejectsFieldOperation(name, expression, resultType, message) {
  const sourcePath = join(scratch, `${name}.compact`);
  const target = join(scratch, `${name}-output`);
  writeFileSync(sourcePath, `pragma language_version 0.28;\nimport CompactStandardLibrary;\n\nexport pure circuit probe(value: Field): ${resultType} {\n  return ${expression};\n}\n`);
  const result = compile(sourcePath, target);
  assert.notEqual(result.status, 0, `${name} unexpectedly compiled`);
  assert.match(result.stderr || result.stdout, message, `${name} did not fail at the expected boundary`);
}

const modulus = 52435875175126190479447740508185965837690552500527637822603658699938581184513n;
const vectors = [
  {
    name: 'add-sub-mul-wrap-and-subtract-from-zero',
    left: modulus - 1n,
    right: 1n,
    expected: [0n, modulus - 2n, modulus - 1n, 1n, false, true],
  },
  {
    name: 'equal-field-values',
    left: modulus - 1n,
    right: modulus - 1n,
    expected: [modulus - 2n, 0n, 1n, 1n, true, false],
  },
  {
    name: 'zero-and-one',
    left: 0n,
    right: 1n,
    expected: [1n, modulus - 1n, 0n, 0n, false, true],
  },
];

try {
  const generated = join(scratch, 'compiled');
  const result = compile(source, generated);
  assert.equal(result.status, 0, `Compact compilation failed:\n${result.stderr || result.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), {recursive: true});
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');
  const runtimeUrl = pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href;
  const contractUrl = pathToFileURL(join(generated, 'contract/index.js')).href;
  const {createCircuitContext, createConstructorContext, dummyContractAddress} = await import(runtimeUrl);
  const {Contract} = await import(contractUrl);
  const contract = new Contract({});
  const wallet = '00'.repeat(32);
  const {currentContractState} = await contract.initialState(createConstructorContext(null, wallet));
  const context = createCircuitContext({
    circuitId: 'arithmetic',
    contractAddress: dummyContractAddress(),
    coinPublicKeyOrZswapState: wallet,
    contractState: currentContractState.data,
    privateState: null,
  });

  for (const vector of vectors) {
    const actual = (await contract.circuits.arithmetic(context, vector.left, vector.right)).result;
    assert.deepEqual(actual, vector.expected, vector.name);
    assert.ok(actual.slice(0, 4).every(value => typeof value === 'bigint' && value >= 0n && value < modulus),
      `${vector.name}: arithmetic output was not canonical`);
  }

  rejectsFieldOperation('ordered-comparison', 'value < value', 'Boolean', /incompatible combination.*relational operator/i);
  rejectsFieldOperation('field-inverse', 'inv(value)', 'Field', /no compatible function named inv/i);
  rejectsFieldOperation('field-negation', 'neg(value)', 'Field', /no compatible function named neg/i);

  console.log(JSON.stringify({
    compactVersion: version,
    runtimeVersion: runtimePackage.version,
    vectors: vectors.map(({name, expected}) => ({
      name,
      output: expected.map(value => typeof value === 'bigint' ? value.toString() : value),
    })),
    rejected: ['ordered Field comparison', 'inv(Field)', 'neg(Field)'],
  }, null, 2));
} finally {
  rmSync(scratch, {recursive: true, force: true});
}
