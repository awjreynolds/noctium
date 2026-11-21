import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/counter-compare.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/,
  `expected pinned Compact compiler, got ${compilerVersion}`);

const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(root, 'tests/compact/CounterCompare.compact');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'counter-compare-'));

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
  const owner = new Uint8Array(32).fill(1);
  const spender = new Uint8Array(32).fill(2);
  const { currentContractState } = await contract.initialState(createConstructorContext(null, walletKey));
  const initial = currentContractState.data;
  const run = async (name, state, ...args) => {
    const result = await contract.circuits[name](createCircuitContext({
      circuitId: name,
      contractAddress: dummyContractAddress(),
      coinPublicKeyOrZswapState: walletKey,
      contractState: state,
      privateState: null,
    }), ...args);
    return [result.result, result.context.callContext.currentQueryContext.state];
  };

  const thresholds = [[301n, true], [300n, false], [299n, false], [(1n << 64n) - 1n, true]];
  for (const [threshold, expected] of thresholds) {
    const [result, state] = await run('inspect', initial, threshold);
    assert.deepEqual(result, [300n, expected]);
    assert.equal(ledger(state).total, 300n);
  }

  const [, seeded] = await run('seedNested', initial, owner, spender);
  assert.equal(ledger(seeded).epochs.member(owner), true);
  for (const [threshold, expected] of thresholds) {
    const [result] = await run('inspectNested', seeded, owner, spender, threshold, true);
    assert.deepEqual(result, [expected]);
  }

  const [inactive, unchanged] = await run('inspectNested', initial, owner, spender, 301n, false);
  assert.deepEqual(inactive, [false]);
  assert.equal(ledger(unchanged).epochs.member(owner), false);
  await assert.rejects(() => run('inspectNested', initial, owner, spender, 301n, true));
  console.log(JSON.stringify({
    fixture: 'CounterCompare', compact: compilerVersion,
    thresholds: thresholds.map(([threshold, expected]) => ({ threshold: threshold.toString(), expected })),
    standaloneReadAfterIncrement: 300,
    nestedReadAfterSeed: 300,
    inactiveMissingPath: false,
    activeMissingPathRejected: true,
  }));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
