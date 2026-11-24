import assert from 'node:assert/strict';
import {execFileSync} from 'node:child_process';
import {dirname, join, resolve} from 'node:path';
import {fileURLToPath, pathToFileURL} from 'node:url';
import {mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync} from 'node:fs';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node record-key-map-constructor.mjs <compactc> <compact-runtime>');
const version = execFileSync(compactc, ['--version'], {encoding: 'utf8'}).trim();
assert.match(version, /^0\.36\.1 \(7fa3a117c/, `unexpected Compact compiler: ${version}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(root, 'tests/compact/RecordKeyMapConstructor.compact');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, {recursive: true});
const scratch = mkdtempSync(join(experiments, 'record-key-map-constructor-'));
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
  const tag = new Uint8Array([7]);
  const id = Uint8Array.from({length: 33}, (_, index) => index * 5 + 2);
  const key = {tag, id};
  const initialFor = enabled => contract.initialState(
    runtime.createConstructorContext(null, wallet), tag, id, 513n, enabled,
  );
  const context = state => runtime.createCircuitContext({
    circuitId: 'inspect', contractAddress: runtime.dummyContractAddress(),
    coinPublicKeyOrZswapState: wallet, contractState: state, privateState: null,
  });

  for (const enabled of [false, true]) {
    const initial = await initialFor(enabled);
    const state = initial.currentContractState.data;
    const entries = ledger(state).entries;
    assert.equal(entries.size(), BigInt(Number(enabled)));
    assert.equal(entries.member(key), enabled);
    assert.equal((await contract.circuits.member(context(state), tag, id)).result, enabled);
    const neighboringId = id.slice();
    neighboringId[neighboringId.length - 1] += 1;
    assert.equal(
      (await contract.circuits.member(context(state), tag, neighboringId)).result,
      false,
    );
    if (enabled) {
      assert.equal(await entries.lookup(key), 513n);
      assert.equal((await contract.circuits.inspect(context(state), tag, id)).result, 513n);
    }
    else {
      let lookupFailed = false;
      try {
        await entries.lookup(key);
      } catch {
        lookupFailed = true;
      }
      assert.equal(lookupFailed, true);
    }
  }

  let wrongWidthRejected = false;
  try {
    await contract.initialState(
      runtime.createConstructorContext(null, wallet), tag, new Uint8Array(32), 513n, true,
    );
  } catch {
    wrongWidthRejected = true;
  }
  assert.equal(wrongWidthRejected, true);
  console.log(`Compact ${version} matched guarded record-key Map constructor initialization`);
} finally {
  rmSync(scratch, {recursive: true, force: true});
}
