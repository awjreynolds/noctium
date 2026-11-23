import assert from 'node:assert/strict';
import {execFileSync} from 'node:child_process';
import {dirname, join, resolve} from 'node:path';
import {fileURLToPath, pathToFileURL} from 'node:url';
import {mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync} from 'node:fs';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node ordered-constructor-counter-read.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], {encoding: 'utf8'}).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/, `unexpected Compact compiler: ${compilerVersion}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(root, 'tests/compact/OrderedConstructorCounterRead.compact');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, {recursive: true});
const scratch = mkdtempSync(join(experiments, 'ordered-constructor-counter-read-'));

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
  const cases = [
    {enabled: true, amount: 0n, expected: [0n, 0n, 0n]},
    {enabled: true, amount: 7n, expected: [0n, 7n, 7n]},
    {enabled: true, amount: 65_535n, expected: [0n, 65_535n, 65_535n]},
    {enabled: false, amount: 65_535n, expected: [0n, 0n, 0n]},
  ];

  for (const {enabled, amount, expected} of cases) {
    const initial = await contract.initialState(
      runtime.createConstructorContext(null, walletKey), enabled, amount,
    );
    const state = initial.currentContractState.data;
    const initialized = ledger(state);
    assert.equal(initialized.snapshotBefore, expected[0]);
    assert.equal(initialized.snapshotAfter, expected[1]);
    assert.equal(initialized.total, expected[2]);

    const readBack = await contract.circuits.readBack(runtime.createCircuitContext({
      circuitId: 'readBack', contractAddress: runtime.dummyContractAddress(),
      coinPublicKeyOrZswapState: walletKey, contractState: state, privateState: null,
    }));
    assert.deepEqual(readBack.result, expected);
  }

  console.log(`Compact ${compilerVersion} preserved Counter reads around a guarded constructor increment`);
} finally {
  rmSync(scratch, {recursive: true, force: true});
}
