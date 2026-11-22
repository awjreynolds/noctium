import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { existsSync, mkdirSync, readFileSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/record-list-head-maybe.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const version = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(version, /^0\.36\.1 \(7fa3a117c/,
  `expected pinned Compact 0.36.1 compiler, got ${version}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0', 'expected pinned Compact runtime 0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/RecordListHeadMaybe.compact');
const generated = join(projectRoot, 'build/experiments/record-list-head-maybe/compact/generated');
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
const { currentContractState } = await contract.initialState(createConstructorContext(null, wallet));
const invoke = async (name, state) => {
  const context = createCircuitContext({
    circuitId: name,
    contractAddress: dummyContractAddress(),
    coinPublicKeyOrZswapState: wallet,
    contractState: state,
    privateState: null,
  });
  const call = await contract.circuits[name](context);
  return [call.result, call.context.callContext.currentQueryContext.state];
};

const [empty] = await invoke('peek', currentContractState.data);
assert.deepEqual(Object.keys(empty), ['is_some', 'value']);
assert.deepEqual(empty, { is_some: false, value: { first: 0n, second: 0n } });

const [, seededState] = await invoke('seed', currentContractState.data);
const seededMemo = { first: 17n, second: 23n };
assert.deepEqual([...ledger(seededState).inbox], [seededMemo]);
const [present] = await invoke('peek', seededState);
assert.deepEqual(Object.keys(present), ['is_some', 'value']);
assert.deepEqual(present, { is_some: true, value: seededMemo });

const render = ({ is_some, value }) => ({
  is_some,
  value: { first: value.first.toString(), second: value.second.toString() },
});
console.log(JSON.stringify({ empty: render(empty), present: render(present) }));
