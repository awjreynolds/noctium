import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/native-map-remove.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const version = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(version, /^0\.36\.1 \(7fa3a117c/, `expected pinned Compact 0.36.1 compiler, got ${version}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0', 'expected pinned Compact runtime 0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/NativeMapRemove.compact');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'native-map-remove-'));

try {
  const generated = join(scratch, 'compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtimeUrl = pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href;
  const contractUrl = pathToFileURL(join(generated, 'contract/index.js')).href;
  const { createCircuitContext, createConstructorContext, dummyContractAddress } = await import(runtimeUrl);
  const { Contract, ledger } = await import(contractUrl);
  const contract = new Contract({});
  const walletKey = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(createConstructorContext(null, walletKey));
  const invoke = async (state, owner, spender, enabled) => {
    const context = createCircuitContext({
      circuitId: 'remove',
      contractAddress: dummyContractAddress(),
      coinPublicKeyOrZswapState: walletKey,
      contractState: state,
      privateState: null,
    });
    const result = await contract.circuits.remove(context, owner, spender, enabled);
    return result.context.callContext.currentQueryContext.state;
  };
  const invokeOwner = async (state, owner, enabled) => {
    const context = createCircuitContext({
      circuitId: 'removeOwner',
      contractAddress: dummyContractAddress(),
      coinPublicKeyOrZswapState: walletKey,
      contractState: state,
      privateState: null,
    });
    const result = await contract.circuits.removeOwner(context, owner, enabled);
    return result.context.callContext.currentQueryContext.state;
  };
  const seed = async (state, owner, spender, x, y) => {
    const context = createCircuitContext({
      circuitId: 'seed',
      contractAddress: dummyContractAddress(),
      coinPublicKeyOrZswapState: walletKey,
      contractState: state,
      privateState: null,
    });
    const result = await contract.circuits.seed(context, owner, spender, x, y);
    return result.context.callContext.currentQueryContext.state;
  };
  const ownerA = new Uint8Array(32).fill(0);
  const ownerB = new Uint8Array(32).fill(3);
  const missingOwner = new Uint8Array(32).fill(9);
  const target = new Uint8Array(32).fill(1);
  const sibling = new Uint8Array(32).fill(2);

  let state = currentContractState.data;
  state = await seed(state, ownerA, target, 10n, 11n);
  state = await seed(state, ownerA, sibling, 20n, 21n);
  state = await seed(state, ownerB, target, 30n, 31n);
  const before = ledger(state).escrow;
  assert.deepEqual(before.lookup(ownerA).lookup(target), { x: 10n, y: 11n });
  assert.deepEqual(before.lookup(ownerA).lookup(sibling), { x: 20n, y: 21n });
  assert.deepEqual(before.lookup(ownerB).lookup(target), { x: 30n, y: 31n });

  state = await invoke(state, ownerA, target, true);
  let escrow = ledger(state).escrow;
  assert.equal(escrow.lookup(ownerA).member(target), false, 'remove deletes the selected child');
  assert.equal(escrow.lookup(ownerA).member(sibling), true, 'remove preserves a sibling child');
  assert.deepEqual(escrow.lookup(ownerA).lookup(sibling), { x: 20n, y: 21n });
  assert.equal(escrow.lookup(ownerB).member(target), true, 'remove preserves the same child under another parent');

  const afterFirstRemove = state;
  state = await invoke(state, ownerA, target, true);
  assert.equal(ledger(state).escrow.lookup(ownerA).member(target), false,
    'removing an absent child is a no-op');
  assert.deepEqual([...ledger(state).escrow.lookup(ownerA)], [...ledger(afterFirstRemove).escrow.lookup(ownerA)]);

  await assert.rejects(() => invoke(state, missingOwner, target, true),
    'active lookup of an absent parent rejects');
  const inactiveState = await invoke(state, missingOwner, target, false);
  escrow = ledger(inactiveState).escrow;
  assert.equal(escrow.size(), ledger(state).escrow.size(), 'inactive removal leaves parent count unchanged');
  assert.equal(escrow.member(ownerA), true);
  assert.equal(escrow.member(ownerB), true);
  assert.equal(escrow.member(missingOwner), false, 'inactive removal does not create a missing parent');
  assert.equal(escrow.lookup(ownerA).member(sibling), true);
  assert.equal(escrow.lookup(ownerB).member(target), true);

  state = await invokeOwner(state, ownerA, true);
  escrow = ledger(state).escrow;
  assert.equal(escrow.member(ownerA), false, 'removeOwner deletes the selected parent entry');
  assert.equal(escrow.member(ownerB), true, 'removeOwner preserves the other parent entry');
  assert.deepEqual(escrow.lookup(ownerB).lookup(target), { x: 30n, y: 31n },
    'removeOwner preserves the other parent record');

  const afterOwnerRemove = state;
  state = await invokeOwner(state, ownerA, true);
  assert.equal(ledger(state).escrow.member(ownerA), false,
    'removing an absent parent is a no-op');
  assert.deepEqual([...ledger(state).escrow.lookup(ownerB)], [...ledger(afterOwnerRemove).escrow.lookup(ownerB)]);

  const inactiveOwnerState = await invokeOwner(state, ownerB, false);
  const inactiveOwnerEscrow = ledger(inactiveOwnerState).escrow;
  assert.equal(inactiveOwnerEscrow.member(ownerB), true, 'inactive removal preserves an existing parent');
  assert.deepEqual(inactiveOwnerEscrow.lookup(ownerB).lookup(target), { x: 30n, y: 31n });
  assert.equal(inactiveOwnerEscrow.member(missingOwner), false,
    'inactive removal does not create or remove a missing parent');

  console.log('Compact 0.36.1 matched nested Map.remove: child and parent removal, repeat no-op, sibling and other-parent preservation, active missing-parent rejection, and inactive no-op');
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
