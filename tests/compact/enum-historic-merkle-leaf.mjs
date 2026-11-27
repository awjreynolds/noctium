import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';

const [compactc, runtimeArgument] = process.argv.slice(2);
assert.ok(compactc && runtimeArgument,
  'usage: node tests/compact/enum-historic-merkle-leaf.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/,
  `expected pinned Compact 0.36.1 compiler, got ${compilerVersion}`);
assert.equal(execFileSync(compactc, ['--language-version'], { encoding: 'utf8' }).trim(), '0.28.0');
assert.equal(execFileSync(compactc, ['--runtime-version'], { encoding: 'utf8' }).trim(), '0.21.0');

const runtimeDirectory = resolve(runtimeArgument);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0', 'expected pinned Compact runtime 0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'enum-historic-merkle-leaf-'));

try {
  const generated = join(scratch, 'compact');
  const source = join(projectRoot, 'tests/compact/EnumHistoricMerkleLeaf.compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');
  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  assert.equal(runtime.versionString, '0.21.0');
  const { Contract, ledger } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);

  const contract = new Contract({});
  const walletKey = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(runtime.createConstructorContext(null, walletKey));
  let state = currentContractState.data;

  const invoke = async (entrypoint, ...args) => {
    const context = runtime.createCircuitContext({
      circuitId: entrypoint,
      contractAddress: runtime.dummyContractAddress(),
      coinPublicKeyOrZswapState: walletKey,
      contractState: state,
      privateState: null,
    });
    const call = await contract.circuits[entrypoint](context, ...args);
    state = call.context.callContext.currentQueryContext.state;
    return call.result;
  };
  const snapshot = () => {
    const tree = ledger(state).history;
    return {
      root: tree.root().field.toString(),
      firstFree: tree.firstFree().toString(),
      history: [...tree.history()].map(({ field }) => field.toString()).sort(),
    };
  };
  const hasRoot = (root) => invoke('checkRoot', { field: BigInt(root) });

  const initial = snapshot();
  assert.deepEqual(initial, { root: '0', firstFree: '0', history: ['0'] });
  assert.equal(await hasRoot(initial.root), true);

  await invoke('appendLeaf', 0);
  const afterFirst = snapshot();
  assert.equal(afterFirst.firstFree, '1');
  assert.notEqual(afterFirst.root, initial.root);
  assert.deepEqual(afterFirst.history, ['0', afterFirst.root].sort());
  assert.equal(await hasRoot(initial.root), true);
  assert.equal(await hasRoot(afterFirst.root), true);

  await invoke('appendLeaf', 1);
  const afterSecond = snapshot();
  assert.equal(afterSecond.firstFree, '2');
  assert.notEqual(afterSecond.root, afterFirst.root);
  assert.deepEqual(afterSecond.history, ['0', afterFirst.root, afterSecond.root].sort());
  const initialRootAfterSecondAppend = await hasRoot(initial.root);
  const firstRootAfterSecondAppend = await hasRoot(afterFirst.root);
  const currentRootAfterSecondAppend = await hasRoot(afterSecond.root);
  assert.equal(initialRootAfterSecondAppend, true);
  assert.equal(firstRootAfterSecondAppend, true);
  assert.equal(currentRootAfterSecondAppend, true);

  const unrelatedRoot = '123456789';
  assert.equal(await hasRoot(unrelatedRoot), false);

  await assert.rejects(async () => invoke('appendLeaf', 2));
  assert.deepEqual(snapshot(), afterSecond);

  console.log(JSON.stringify({
    fixture: 'EnumHistoricMerkleLeaf',
    compact: compilerVersion,
    runtime: runtimePackage.version,
    enum: { name: 'Leaf', members: ['First', 'Second'], ordinals: [0, 1] },
    initial,
    afterFirst,
    afterSecond,
    membership: {
      initialRootAfterSecondAppend,
      firstRootAfterSecondAppend,
      currentRootAfterSecondAppend,
      unrelatedRoot: { root: unrelatedRoot, present: false },
    },
    rejectedOrdinal: 2,
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
