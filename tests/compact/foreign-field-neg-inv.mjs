import assert from 'node:assert/strict';
import {execFileSync, spawnSync} from 'node:child_process';
import {mkdtempSync, mkdirSync, readFileSync, rmSync, symlinkSync} from 'node:fs';
import {dirname, join, resolve} from 'node:path';
import {fileURLToPath, pathToFileURL} from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/foreign-field-neg-inv.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const version = execFileSync(compactc, ['--version'], {encoding: 'utf8'}).trim();
assert.match(version, /^0\.36\.1 \(7fa3a117c/, `expected pinned Compact 0.36.1 compiler, got ${version}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/ForeignFieldNegInv.compact');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, {recursive: true});
const scratch = mkdtempSync(join(experiments, 'foreign-field-neg-inv-'));

function powMod(base, exponent, modulus) {
  let result = 1n;
  base %= modulus;
  while (exponent > 0n) {
    if ((exponent & 1n) !== 0n) result = result * base % modulus;
    base = base * base % modulus;
    exponent >>= 1n;
  }
  return result;
}

try {
  const generated = join(scratch, 'compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], {encoding: 'utf8'});
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

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
  const invoke = async (name, ...args) => {
    const {result} = await contract.circuits[name](createCircuitContext({
      circuitId: name,
      contractAddress: dummyContractAddress(),
      coinPublicKeyOrZswapState: wallet,
      contractState: currentContractState.data,
      privateState: null,
    }), ...args);
    return result;
  };

  const fields = [
    {label: 'secp256k1Base', inv: 'inverseZeroK1Base', modulus: 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2fn, value: 5n},
    {label: 'secp256k1Scalar', inv: 'inverseZeroK1Scalar', modulus: 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141n, value: 7n},
    {label: 'secp256r1Base', inv: 'inverseZeroR1Base', modulus: 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffffn, value: 11n},
    {label: 'secp256r1Scalar', inv: 'inverseZeroR1Scalar', modulus: 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551n, value: 13n},
    {label: 'curve25519Base', inv: 'inverseZeroC255Base', modulus: (1n << 255n) - 19n, value: 17n},
    {label: 'curve25519Scalar', inv: 'inverseZeroC255Scalar', modulus: (1n << 252n) + 27742317777372353535851937790883648493n, value: 19n},
  ];
  const boundary = fields.map(({modulus}) => modulus - 1n);
  const result = await invoke('arithmetic',
    ...fields.map(({value}) => value),
    ...fields.map(() => 0n),
    ...boundary);
  const expected = fields.flatMap(({modulus, value}) => [
    value === 0n ? 0n : modulus - value,
    powMod(value, modulus - 2n, modulus),
  ]).concat(fields.map(() => 0n), fields.flatMap(({modulus}) => [1n, modulus - 1n]));
  assert.deepEqual(result, expected);

  const zeroInverse = [];
  for (const {label, inv} of fields) {
    let failure;
    try {
      await invoke(inv, 0n);
    } catch (error) {
      failure = error;
    }
    assert.ok(failure, `${label} inverse of zero must reject`);
    assert.match(String(failure.message), /no inverse for 0/i);
    zeroInverse.push({field: label, result: 'rejected', message: failure.message});
  }

  console.log(JSON.stringify({
    fields: fields.map(({label}, index) => ({
      field: label,
      negative: result[index * 2].toString(),
      inverse: result[index * 2 + 1].toString(),
      negativeZero: result[12 + index].toString(),
      negativeBoundary: result[18 + index * 2].toString(),
      inverseBoundary: result[19 + index * 2].toString(),
    })),
    zeroInverse,
  }));
} finally {
  rmSync(scratch, {recursive: true, force: true});
}
