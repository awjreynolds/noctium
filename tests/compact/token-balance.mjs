import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/token-balance.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/, `unexpected Compact compiler: ${compilerVersion}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(root, 'tests/compact/TokenBalance.compact');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'token-balance-'));

try {
  const generated = join(scratch, 'compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  assert.equal(runtime.versionString, '0.21.0');
  const { Contract } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const contract = new Contract({});
  const wallet = '00'.repeat(32);
  const color = Uint8Array.from({ length: 32 }, (_, index) => index + 1);
  const raw = Buffer.from(color).toString('hex');
  const max128 = (1n << 128n) - 1n;
  const max64 = (1n << 64n) - 1n;
  const { currentContractState } = await contract.initialState(
    runtime.createConstructorContext(null, wallet),
  );

  function contextWithBalance(circuitId, unshielded, shielded) {
    const context = runtime.createCircuitContext({
      circuitId,
      contractAddress: runtime.dummyContractAddress(),
      coinPublicKeyOrZswapState: wallet,
      contractState: currentContractState.data,
      privateState: null,
    });
    const vm = context.callContext.currentQueryContext;
    const balance = new Map();
    if (unshielded !== null) balance.set({ tag: 'unshielded', raw }, unshielded);
    if (shielded !== null) balance.set({ tag: 'shielded', raw }, shielded);
    vm.block = { ...vm.block, balance };
    return context;
  }

  async function inspect(unshielded, shielded, tag, limit, enabled, exact) {
    return contract.circuits.inspect(
      contextWithBalance('inspect', unshielded, shielded), color, tag, limit, enabled, exact,
    );
  }

  for (const [shielded, tag, limit, enabled, exact, amount] of [
    [23n, true, 20n, true, true, 17n],
    [23n, false, 20n, true, true, 23n],
    [23n, false, 23n, true, true, 23n],
    [null, false, 20n, true, true, 0n],
    [max128, false, max128, false, true, max128],
    [max128, false, max128, false, false, max128],
  ]) {
    const { result } = await inspect(17n, shielded, tag, limit, enabled, exact);
    assert.deepEqual(result, [
      exact ? amount : 0n,
      enabled && amount < limit,
      enabled && amount > limit,
    ]);
  }
  for (const [amount, limit] of [[max128, 0n], [23n, max128]]) {
    await assert.rejects(
      () => inspect(17n, amount, false, limit, true, false),
      /decode for built-in type u64/,
    );
  }

  const helperCases = [
    [17n, 20n, true, [17n, true, false, false, true]],
    [20n, 20n, true, [20n, false, true, false, true]],
    [23n, 20n, true, [23n, false, true, true, false]],
    [null, 20n, true, [0n, true, false, false, true]],
    [max128, max128, false, [max128, false, false, false, false]],
    [max64, max64, true, [max64, false, true, false, true]],
  ];
  for (const [amount, limit, enabled, expected] of helperCases) {
    const context = contextWithBalance('unshielded', amount, 11n);
    const { result } = await contract.circuits.unshielded(context, color, limit, enabled);
    assert.deepEqual(result, expected);
  }
  await assert.rejects(async () => contract.circuits.unshielded(
    contextWithBalance('unshielded', max128, 11n), color, 20n, true,
  ), /decode for built-in type u64/);
  await assert.rejects(async () => contract.circuits.unshielded(
    contextWithBalance('unshielded', 8n, 11n), color, max128, true,
  ), /decode for built-in type u64/);
  console.log('Compact 0.36.1 matched six seeded unshielded helper comparisons, absent and inactive behavior, active u64 maximum, and wide balance/limit rejection');
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
