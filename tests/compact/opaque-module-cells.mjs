import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/opaque-module-cells.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/,
  `expected pinned Compact 0.36.1 compiler, got ${compilerVersion}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0', 'expected pinned Compact runtime 0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/OpaqueModuleCells.compact');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'opaque-module-cells-'));

try {
  const generated = join(scratch, 'compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], {
    cwd: projectRoot,
    encoding: 'utf8',
  });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  assert.equal(runtime.versionString, '0.21.0');
  const { Contract, ledger } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const contract = new Contract({});
  const wallet = '00'.repeat(32);
  const text = 'A\0B';
  const bytes = Uint8Array.of(0, 255, 0, 1);
  const { currentContractState } = await contract.initialState(
    runtime.createConstructorContext(null, wallet), text, bytes,
  );
  const initialState = currentContractState.data;
  const cells = ledger(initialState);
  assert.equal(cells.text_value, text);
  assert.deepEqual([...cells.bytes_value], [...bytes]);
  assert.equal(cells.directText, text);
  assert.deepEqual([...cells.directBytes], [...bytes]);

  const contextFor = circuitId => runtime.createCircuitContext({
    circuitId,
    contractAddress: runtime.dummyContractAddress(),
    coinPublicKeyOrZswapState: wallet,
    contractState: initialState,
    privateState: null,
  });
  const textRead = await contract.circuits.text_read(contextFor('text_read'));
  const bytesRead = await contract.circuits.bytes_read(contextFor('bytes_read'));
  assert.equal(textRead.result, text);
  assert.deepEqual([...bytesRead.result], [...bytes]);

  const [textHash, directTextHash] = await Promise.all([
    contract.circuits.text_hash(contextFor('text_hash')),
    contract.circuits.directTextHash(contextFor('directTextHash')),
  ]);
  const [bytesHash, directBytesHash] = await Promise.all([
    contract.circuits.bytes_hash(contextFor('bytes_hash')),
    contract.circuits.directBytesHash(contextFor('directBytesHash')),
  ]);
  assert.equal(textHash.result, directTextHash.result);
  assert.equal(bytesHash.result, directBytesHash.result);

  console.log(JSON.stringify({
    fixture: 'OpaqueModuleCells',
    compact: compilerVersion,
    runtime: runtimePackage.version,
    text,
    bytes: [...bytes],
    textHash: textHash.result.toString(),
    bytesHash: bytesHash.result.toString(),
  }));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
