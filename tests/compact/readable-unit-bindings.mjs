import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/readable-unit-bindings.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const runtimeDirectory = resolve(runtimePath);
const version = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(version, /^0\.36\.1 \(7fa3a117c/,
  `expected pinned Compact 0.36.1 compiler, got ${version}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const generated = mkdtempSync(join(experiments, '435-unit-compact-'));

try {
  execFileSync(compactc, ['--skip-zk', join(projectRoot, 'tests/compact/ReadableUnitBindings.compact'), generated]);
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtimeUrl = pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href;
  const contractUrl = pathToFileURL(join(generated, 'contract/index.js')).href;
  const { createCircuitContext, createConstructorContext, dummyContractAddress } = await import(runtimeUrl);
  const { Contract } = await import(contractUrl);
  const contract = new Contract({
    unitObserve: ({ privateState }, value) => [[...privateState, value.toString()], []],
    unitFinish: ({ privateState }, value) => [[...privateState, value.toString()], value + 1n],
  });
  const walletKey = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(createConstructorContext([], walletKey));
  const result = await contract.circuits.update(createCircuitContext({
    circuitId: 'update',
    contractAddress: dummyContractAddress(),
    coinPublicKeyOrZswapState: walletKey,
    contractState: currentContractState.data,
    privateState: [],
  }), 7n);

  const callbackOrder = result.context.callContext.currentPrivateState;
  const [value, present, absent] = result.result;
  assert.equal(value, 10n);
  assert.deepEqual(present, { is_some: true, value: [] });
  assert.deepEqual(absent, { is_some: false, value: [] });
  assert.deepEqual(callbackOrder, ['7', '8', '9', '10']);
  console.log(JSON.stringify({ value: value.toString(), present, absent, callbackOrder }));
} finally {
  rmSync(generated, { recursive: true, force: true });
}
