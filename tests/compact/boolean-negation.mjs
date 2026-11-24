import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/boolean-negation.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const version = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(version, /^0\.36\.1 \(7fa3a117c/);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'boolean-negation-'));
try {
  const generated = join(scratch, 'compact');
  const source = join(root, 'tests/compact/BooleanNegation.compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, compile.stderr || compile.stdout);
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');
  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  const { Contract } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const contract = new Contract({});
  const wallet = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(
    runtime.createConstructorContext(null, wallet),
  );
  const context = (circuitId) => runtime.createCircuitContext({
    circuitId, contractAddress: runtime.dummyContractAddress(),
    coinPublicKeyOrZswapState: wallet, contractState: currentContractState.data,
    privateState: null,
  });
  for (const [value, expected] of [[false, true], [true, false]]) {
    const { result } = await contract.circuits.negate(context('negate'), value);
    assert.equal(result, expected);
  }
  for (const left of [false, true]) {
    for (const right of [false, true]) {
      const { result } = await contract.circuits.truthTable(context('truthTable'), left, right);
      assert.deepEqual(result, [false, true, !left, left && right, left || right, left === right, left !== right]);
    }
  }
  const fieldMax = runtime.MAX_FIELD;
  for (const [flag, field, amount] of [[false, 0n, 0n], [false, fieldMax, 0n], [true, 0n, 255n], [true, fieldMax, 255n]]) {
    const { result } = await contract.circuits.convert(context('convert'), flag, field, amount);
    assert.deepEqual(result, [BigInt(flag), BigInt(flag), field !== 0n, amount !== 0n, false]);
  }
  assert.equal((await contract.circuits.narrow(context('narrow'), false)).result, 0n);
  await assert.rejects(async () => contract.circuits.narrow(context('narrow'), true));
  await assert.rejects(async () => contract.circuits.truthTable(context('truthTable'), 1n, false), /boolean/i);

  for (const [inputs, expected] of [
    [[false, true, false, false, 2n], [false, true, false]],
    [[false, true, true, true, 2n], [false, true, true]],
    [[true, false, true, false, 1n], [true, true, true]],
  ]) {
    const { result } = await contract.circuits.lazy(context('lazy'), ...inputs);
    assert.deepEqual(result, expected);
  }
  for (const inputs of [
    [true, true, false, false, 2n], [false, false, false, false, 2n], [false, true, true, false, 2n],
  ]) {
    await assert.rejects(async () => contract.circuits.lazy(context('lazy'), ...inputs));
  }
  const invalid = join(scratch, 'NonBooleanOperand.compact');
  writeFileSync(invalid, `pragma language_version 0.28;
export circuit wrong(left: Boolean, right: Field): Boolean {
  return left && right;
}
`);
  const rejected = spawnSync(compactc, ['--skip-zk', invalid, join(scratch, 'rejected')], { encoding: 'utf8' });
  assert.ok(rejected.status !== null && rejected.status !== 0, rejected.stderr || rejected.stdout);
  assert.match(rejected.stderr, /Boolean/);
  console.log(`Compact ${version} matched Boolean operators, conversions and short-circuit cases`);
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
