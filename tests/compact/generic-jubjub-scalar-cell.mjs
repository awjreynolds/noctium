import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/generic-jubjub-scalar-cell.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

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
const scratch = mkdtempSync(join(experiments, 'generic-jubjub-scalar-cell-'));

try {
  const generated = join(scratch, 'compact');
  const source = join(projectRoot, 'tests/compact/GenericJubjubScalarCell.compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  assert.equal(runtime.versionString, '0.21.0');
  const { Contract, ledger } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const contract = new Contract({});
  const wallet = '00'.repeat(32);
  const constructor = runtime.createConstructorContext(null, wallet);
  const initial = await contract.initialState(constructor, 5n);
  const run = async (circuitId, state, ...args) => {
    const context = runtime.createCircuitContext({
      circuitId,
      contractAddress: runtime.dummyContractAddress(),
      coinPublicKeyOrZswapState: wallet,
      contractState: state,
      privateState: null,
    });
    const call = await contract.circuits[circuitId](context, ...args);
    return [call.result, call.context.callContext.currentQueryContext.state];
  };

  const initialState = initial.currentContractState.data;
  assert.equal(ledger(initialState).explicit_value, 5n);
  const initialRead = (await run('readExplicit', initialState))[0];
  assert.equal(initialRead, 5n);
  assert.equal(typeof initialRead, 'bigint');

  const [updateResult, updatedState] = await run('updateExplicit', initialState, 17n);
  assert.equal(updateResult, 17n);
  const storedValue = ledger(updatedState).explicit_value;
  assert.equal(storedValue, 17n);
  assert.equal(typeof storedValue, 'bigint');
  const updatedRead = (await run('readExplicit', updatedState))[0];
  assert.equal(updatedRead, 17n);
  assert.equal(typeof updatedRead, 'bigint');

  console.log(JSON.stringify({
    fixture: 'GenericJubjubScalarCell',
    compact: compilerVersion,
    runtime: runtimePackage.version,
    initial: {
      constructorInput: '5',
      stored: '5',
      readBack: initialRead.toString(),
      javascriptType: typeof initialRead,
    },
    update: {
      input: '17',
      result: updateResult.toString(),
      stored: storedValue.toString(),
      readBack: updatedRead.toString(),
      javascriptType: typeof updatedRead,
    },
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
