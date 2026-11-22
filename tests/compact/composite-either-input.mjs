import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { existsSync, mkdirSync, readFileSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/composite-either-input.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const version = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(version, /^0\.36\.1 \(7fa3a117c/,
  `expected pinned Compact 0.36.1 compiler, got ${version}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0', 'expected pinned Compact runtime 0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/CompositeEitherInput.compact');
const generated = join(projectRoot, 'build/experiments/either-input/compact/generated');
mkdirSync(dirname(generated), { recursive: true });
const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
mkdirSync(dirname(runtimeLink), { recursive: true });
if (!existsSync(runtimeLink)) symlinkSync(runtimeDirectory, runtimeLink, 'dir');

const runtimeUrl = pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href;
const contractUrl = pathToFileURL(join(generated, 'contract/index.js')).href;
const { createCircuitContext, createConstructorContext, dummyContractAddress } = await import(runtimeUrl);
const { Contract, ledger } = await import(contractUrl);

const contract = new Contract({});
const wallet = '00'.repeat(32);
const limits = { count: 17n, enabled: true, memo: Uint8Array.from([0, 1, 2, 255]) };
const vector = [true, true];
const initialState = async () => (await contract.initialState(createConstructorContext(null, wallet))).currentContractState.data;
const invoke = async (contractState, value) => {
  const context = createCircuitContext({
    circuitId: 'echo',
    contractAddress: dummyContractAddress(),
    coinPublicKeyOrZswapState: wallet,
    contractState,
    privateState: null,
  });
  return contract.circuits.echo(context, value);
};

for (const value of [
  { is_left: true, left: limits, right: vector },
  { is_left: false, left: limits, right: vector },
]) {
  const { result, context } = await invoke(await initialState(), value);
  assert.deepEqual(result, value);
  assert.equal(ledger(context.callContext.currentQueryContext.state).seen, value.is_left);
}

const freshState = await initialState();
await assert.rejects(invoke(freshState, { is_left: 'true', left: limits, right: vector }));
await assert.rejects(invoke(freshState, {
  is_left: true,
  left: { ...limits, memo: Uint8Array.from([0, 1, 2]) },
  right: vector,
}));
await assert.rejects(invoke(freshState, { is_left: false, left: limits, right: [true] }));

console.log('Compact 0.36.1 echoed both Either tags and both payload arms');
