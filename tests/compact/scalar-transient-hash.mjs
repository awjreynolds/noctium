import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/scalar-transient-hash.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const version = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(version, /^0\.36\.1 \(7fa3a117c/, `expected pinned Compact 0.36.1 compiler, got ${version}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0', 'expected pinned Compact runtime 0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/ScalarTransientHash.compact');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'scalar-transient-hash-'));

try {
  const generated = join(scratch, 'compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  assert.equal(runtime.versionString, '0.21.0');
  const { createCircuitContext, createConstructorContext, dummyContractAddress } = runtime;
  const { Contract } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const contract = new Contract({});
  const wallet = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(createConstructorContext(null, wallet));
  const context = (circuitId) => createCircuitContext({
    circuitId,
    contractAddress: dummyContractAddress(),
    coinPublicKeyOrZswapState: wallet,
    contractState: currentContractState.data,
    privateState: null,
  });
  const hashField = async (value) => (await contract.circuits.hashField(context('hashField'), value)).result;
  const hashFlag = async (value) => (await contract.circuits.hashFlag(context('hashFlag'), value)).result;
  const hashByte = async (value) => (await contract.circuits.hashByte(context('hashByte'), value)).result;

  const field = await Promise.all([0n, 7n].map(hashField));
  const flag = await Promise.all([false, true].map(hashFlag));
  const byte = await Promise.all([0n, 7n, 255n].map(hashByte));
  const oneField = await hashField(1n);
  const oneByte = await hashByte(1n);
  const equivalents = {
    zero: field[0] === byte[0] && field[0] === flag[0],
    seven: field[1] === byte[1],
    one: oneField === oneByte && oneField === flag[1],
  };
  assert.deepEqual(field.map(String), [
    '9620025776880078320084866401708960911381310259544672466178048295274965038202',
    '38736647962766302285471997525105643408071412124637099941878267108985079060536',
  ]);
  assert.deepEqual(flag.map(String), [
    '9620025776880078320084866401708960911381310259544672466178048295274965038202',
    '17188582201390813395271572040516706359096240541392850241580803164279358646045',
  ]);
  assert.deepEqual(byte.map(String), [
    '9620025776880078320084866401708960911381310259544672466178048295274965038202',
    '38736647962766302285471997525105643408071412124637099941878267108985079060536',
    '24950185806055691809115319438305670656167725047316057740233702636209249196133',
  ]);
  assert.deepEqual(equivalents, {zero: true, seven: true, one: true});
  console.log(JSON.stringify({
    field: field.map(String),
    bool: flag.map(String),
    uint8: byte.map(String),
    equivalentFieldHashes: equivalents,
  }));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
