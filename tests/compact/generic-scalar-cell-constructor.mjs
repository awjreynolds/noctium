import assert from 'node:assert/strict';
import {execFileSync} from 'node:child_process';
import {dirname, join, resolve} from 'node:path';
import {fileURLToPath, pathToFileURL} from 'node:url';
import {mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync} from 'node:fs';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node generic-scalar-cell-constructor.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], {encoding: 'utf8'}).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/, `unexpected Compact compiler: ${compilerVersion}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(root, 'tests/compact/GenericScalarCellConstructor.compact');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, {recursive: true});
const scratch = mkdtempSync(join(experiments, 'generic-scalar-cell-constructor-'));

try {
  const generated = join(scratch, 'compiled');
  execFileSync(compactc, ['--skip-zk', source, generated], {encoding: 'utf8'});
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), {recursive: true});
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  assert.equal(runtime.versionString, '0.21.0');
  const {Contract, ledger} = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const contract = new Contract({});
  const walletKey = '00'.repeat(32);
  const initial = await contract.initialState(
    runtime.createConstructorContext(null, walletKey), 5n, true, 42n,
  );
  const state = initial.currentContractState.data;
  const initialized = ledger(state);
  assert.equal(initialized.fieldCell_value, 5n);
  assert.equal(initialized.flagCell_value, true);
  assert.equal(initialized.countCell_value, 42n);

  for (const [circuitId, expected] of [
    ['readField', 5n],
    ['readFlag', true],
    ['readCount', 42n],
  ]) {
    const result = await contract.circuits[circuitId](runtime.createCircuitContext({
      circuitId, contractAddress: runtime.dummyContractAddress(),
      coinPublicKeyOrZswapState: walletKey, contractState: state, privateState: null,
    }));
    assert.deepEqual(result.result, expected);
  }

  await assert.rejects(
    () => contract.initialState(runtime.createConstructorContext(null, walletKey), 5n, true, 65_536n),
  );
  console.log(`Compact ${compilerVersion} initialized specialized Field, Boolean and Uint<16> cells and rejected 65536`);
} finally {
  rmSync(scratch, {recursive: true, force: true});
}
