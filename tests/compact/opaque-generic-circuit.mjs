import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, rmdirSync, symlinkSync } from 'node:fs';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/opaque-generic-circuit.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/,
  `expected pinned Compact 0.36.1 compiler, got ${compilerVersion}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0', 'expected pinned Compact runtime 0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(root, 'tests/compact/OpaqueGenericCircuit.compact');
const experiments = join(root, 'build/experiments/873-opaque-generic-circuit');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'run-'));

try {
  const generated = join(scratch, 'compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

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
  const context = circuitId => runtime.createCircuitContext({
    circuitId,
    contractAddress: runtime.dummyContractAddress(),
    coinPublicKeyOrZswapState: wallet,
    contractState: currentContractState.data,
    privateState: null,
  });

  const text = 'A\0B';
  const textCall = await contract.circuits.string_identity(context('string_identity'), text);
  assert.equal(textCall.result, text);
  await assert.rejects(
    contract.circuits.string_identity(context('string_identity'), Uint8Array.of(0, 255, 0, 1)),
  );

  const bytes = Uint8Array.of(0, 255, 0, 1);
  const bytesCall = await contract.circuits.bytes_identity(context('bytes_identity'), bytes);
  assert.deepEqual([...bytesCall.result], [0, 255, 0, 1]);
  await assert.rejects(
    contract.circuits.bytes_identity(context('bytes_identity'), text),
  );

  console.log(JSON.stringify({
    fixture: 'OpaqueGenericCircuit',
    compact: compilerVersion,
    runtime: runtimePackage.version,
    string: [...new TextEncoder().encode(text)],
    bytes: [...bytesCall.result],
  }));
} finally {
  rmSync(scratch, { recursive: true, force: true });
  try {
    rmdirSync(experiments);
  } catch (error) {
    if (error.code !== 'ENOENT' && error.code !== 'ENOTEMPTY') throw error;
  }
}
