import assert from 'node:assert/strict';
import {execFileSync} from 'node:child_process';
import {dirname, join, resolve} from 'node:path';
import {fileURLToPath, pathToFileURL} from 'node:url';
import {mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync} from 'node:fs';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node record-constructor.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const version = execFileSync(compactc, ['--version'], {encoding: 'utf8'}).trim();
assert.match(version, /^0\.36\.1 \(7fa3a117c/, `unexpected Compact compiler: ${version}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(root, 'tests/compact/RecordConstructor.compact');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, {recursive: true});
const scratch = mkdtempSync(join(experiments, 'record-constructor-'));
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
  const wallet = '00'.repeat(32);
  const owner = new Uint8Array(32).fill(19);
  const initialFor = enabled => contract.initialState(
    runtime.createConstructorContext(null, wallet), owner, 19n, 7n, true, enabled,
  );
  const inspect = (state, key = owner) => contract.circuits.inspect(runtime.createCircuitContext({
    circuitId: 'inspect', contractAddress: runtime.dummyContractAddress(),
    coinPublicKeyOrZswapState: wallet, contractState: state, privateState: null,
  }), key);

  for (const enabled of [false, true]) {
    const initial = await initialFor(enabled);
    const state = initial.currentContractState.data;
    const positions = ledger(state).positions;
    assert.equal(positions.size(), 1n);
    assert.equal(positions.member(owner), true);
    const expected = enabled
      ? {amount: 19n, count: 7n, active: true}
      : {amount: 0n, count: 7n, active: false};
    assert.deepEqual(positions.lookup(owner), expected);
    assert.deepEqual((await inspect(state)).result, expected);
  }
  console.log(`Compact ${version} guarded the Bytes<32>-keyed record Map constructor`);
} finally {
  rmSync(scratch, {recursive: true, force: true});
}
