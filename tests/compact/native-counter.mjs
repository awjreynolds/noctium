import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/native-counter.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(root, 'tests/compact/NativeCounter.compact');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'native-counter-'));

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
  const owner = new Uint8Array(32).fill(4);
  const spender = new Uint8Array(32).fill(7);
  const absentOwner = new Uint8Array(32).fill(8);
  const absentSpender = new Uint8Array(32).fill(9);
  const { currentContractState } = await contract.initialState(createConstructorContext(null, walletKey));
  const invoke = async (name, state, ...args) => {
    const context = createCircuitContext({
      circuitId: name,
      contractAddress: dummyContractAddress(),
      coinPublicKeyOrZswapState: walletKey,
      contractState: state,
      privateState: null,
    });
    const call = await contract.circuits[name](context, ...args);
    return [call.result, call.context.callContext.currentQueryContext.state];
  };

  const initial = currentContractState.data;
  assert.equal(ledger(initial).total, 0n);
  assert.equal(ledger(initial).epochs.size(), 0n);
  const [initialTotalRead] = await invoke('readTotal', initial);
  assert.equal(initialTotalRead, 0n, 'standalone Counter.read starts at zero');
  const [, inactive] = await invoke('guarded', initial, owner, spender, false);
  assert.equal(ledger(inactive).total, 0n);
  assert.equal(ledger(inactive).epochs.member(owner), false);

  let state = initial;
  for (const [name, args, expected] of [
    ['bump', [owner, spender], [3n, 1n]],
    ['bump', [owner, spender], [6n, 2n]],
    ['reduce', [owner, spender], [4n, 1n]],
    ['resetCounters', [owner, spender], [0n, 0n]],
  ]) {
    const [result, next] = await invoke(name, state, ...args);
    assert.deepEqual(result, expected, `${name} return values`);
    state = next;
    assert.equal(ledger(state).total, expected[0]);
    assert.equal(ledger(state).epochs.lookup(owner).lookup(spender).read(), expected[1]);
  }
  const [readBack] = await invoke('readCounters', state, owner, spender);
  assert.deepEqual(readBack, [0n, 0n], 'read returns reset standalone and nested counters');
  const [resetTotalRead] = await invoke('readTotal', state);
  assert.equal(resetTotalRead, 0n);

  const [, parentOnly] = await invoke('ensureOwner', state, absentOwner);
  assert.equal(ledger(parentOnly).epochs.member(absentOwner), true);
  assert.equal(ledger(parentOnly).epochs.lookup(absentOwner).member(absentSpender), false);
  await assert.rejects(
    invoke('readCounters', parentOnly, absentOwner, absentSpender),
    /expected a cell, received null/,
  );
  const [missingLeafReset, afterMissingLeafReset] = await invoke(
    'resetCounters', parentOnly, absentOwner, absentSpender,
  );
  assert.deepEqual(missingLeafReset, [0n, 0n]);
  assert.equal(ledger(afterMissingLeafReset).epochs.lookup(absentOwner).member(absentSpender), true,
    'resetToDefault inserts an absent leaf below an existing map parent');
  const [readMissingLeaf] = await invoke(
    'readCounters', afterMissingLeafReset, absentOwner, absentSpender,
  );
  assert.deepEqual(readMissingLeaf, [0n, 0n]);

  await assert.rejects(
    invoke('resetCounters', state, new Uint8Array(32).fill(10), absentSpender),
    /invalid operation for type: attempted to ins, only array, map, and bmt are supported/,
    'resetToDefault rejects a missing intermediate map parent',
  );
  assert.equal(ledger(state).epochs.member(new Uint8Array(32).fill(10)), false,
    'failed missing-parent reset leaves the input state unchanged');

  console.log(`Compact ${compilerVersion} passed NativeCounter transitions, reads, reset, absent-leaf insertion, and missing-parent rejection`);
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
