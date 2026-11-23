import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/map-of-list.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const absoluteRuntimeDirectory = resolve(runtimeDirectory);

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/, `expected pinned Compact 0.36.1 compiler, got ${compilerVersion}`);
const runtimePackage = JSON.parse(readFileSync(join(absoluteRuntimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0', 'expected pinned Compact runtime 0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/MapOfList.compact');
const indirectSource = join(projectRoot, 'tests/compact/MapOfListIndirect.compact');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, '811-compact-map-of-list-'));

try {
  const generated = join(scratch, 'generated');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const rejected = spawnSync(compactc, ['--skip-zk', indirectSource, join(scratch, 'indirect')], { encoding: 'utf8' });
  assert.notEqual(rejected.status, 0, 'expected Compact to reject a local binding of a Map lookup returning a List');
  assert.match(rejected.stderr || rejected.stdout,
    /incomplete chain of ledger indirects: final result must be a regular type, but received ADT type\s+List<Field>/i,
    `expected the pinned indirect-ADT diagnostic, got:\n${rejected.stderr || rejected.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(absoluteRuntimeDirectory, runtimeLink, 'dir');

  const runtime = await import(pathToFileURL(join(absoluteRuntimeDirectory, 'dist/index.js')).href);
  const { Contract } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const contract = new Contract({});
  const walletKey = '00'.repeat(32);
  const ownerA = 1n;
  const ownerB = 2n;
  const { currentContractState } = await contract.initialState(runtime.createConstructorContext(null, walletKey));
  const invoke = async (name, state, ...args) => {
    const context = runtime.createCircuitContext({
      circuitId: name,
      contractAddress: runtime.dummyContractAddress(),
      coinPublicKeyOrZswapState: walletKey,
      contractState: state,
      privateState: null,
    });
    const call = await contract.circuits[name](context, ...args);
    return [call.result, call.context.callContext.currentQueryContext.state];
  };
  const expectList = async (state, owner, expected) => {
    const [result] = await invoke('inspect', state, owner);
    assert.deepEqual(result, [BigInt(expected.length), expected.length > 0, expected[0] ?? 0n]);
  };

  let state = currentContractState.data;
  [, state] = await invoke('push', state, ownerA, 5n);
  [, state] = await invoke('push', state, ownerB, 99n);
  [, state] = await invoke('push', state, ownerA, 11n);
  [, state] = await invoke('push', state, ownerA, 22n);
  await expectList(state, ownerA, [22n, 11n, 5n]);
  await expectList(state, ownerB, [99n]);

  [, state] = await invoke('pop', state, ownerA);
  await expectList(state, ownerA, [11n, 5n]);
  await expectList(state, ownerB, [99n]);

  console.log('Compact 0.36.1 Map<Field, List<Field>> pushFront, length, head, and popFront passed; local ADT binding was rejected');
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
