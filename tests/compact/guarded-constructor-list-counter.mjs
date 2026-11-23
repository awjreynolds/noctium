import assert from 'node:assert/strict';
import {execFileSync} from 'node:child_process';
import {dirname, join, resolve} from 'node:path';
import {fileURLToPath, pathToFileURL} from 'node:url';
import {mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync} from 'node:fs';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node guarded-constructor-list-counter.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], {encoding: 'utf8'}).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/, `unexpected Compact compiler: ${compilerVersion}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(root, 'tests/compact/GuardedConstructorListCounter.compact');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, {recursive: true});
const scratch = mkdtempSync(join(experiments, 'guarded-constructor-list-counter-'));

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

  for (const enabled of [false, true]) {
    const initial = await contract.initialState(
      runtime.createConstructorContext(null, walletKey), enabled, 1234n, 42n,
    );
    const state = initial.currentContractState.data;
    const expectedAmount = enabled ? 1234n : 0n;
    const expectedItems = enabled ? [42n] : [];
    assert.equal(ledger(state).total, expectedAmount);
    assert.deepEqual([...ledger(state).items], expectedItems);

    const readBack = await contract.circuits.readBack(runtime.createCircuitContext({
      circuitId: 'readBack', contractAddress: runtime.dummyContractAddress(),
      coinPublicKeyOrZswapState: walletKey, contractState: state, privateState: null,
    }));
    assert.deepEqual(readBack.result, [
      expectedAmount,
      enabled ? 1n : 0n,
      {is_some: enabled, value: enabled ? 42n : 0n},
    ]);
  }

  console.log(`Compact ${compilerVersion} guarded the sealed Counter and List constructor writes`);
} finally {
  rmSync(scratch, {recursive: true, force: true});
}
