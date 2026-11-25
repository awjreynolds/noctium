import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/map-is-empty-parity.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/, `expected pinned Compact 0.36.1 compiler, got ${compilerVersion}`);
assert.equal(execFileSync(compactc, ['--language-version'], { encoding: 'utf8' }).trim(), '0.28.0');
assert.equal(execFileSync(compactc, ['--runtime-version'], { encoding: 'utf8' }).trim(), '0.21.0');

const runtimeDirectory = resolve(runtimePath);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0', 'expected pinned Compact runtime 0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'map-is-empty-parity-'));

try {
  const generated = join(scratch, 'compact');
  const source = join(projectRoot, 'tests/compact/MapIsEmptyParity.compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], {
    cwd: projectRoot,
    encoding: 'utf8',
  });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  const { Contract, ledger } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  assert.equal(runtime.versionString, '0.21.0');

  const contract = new Contract({});
  const walletKey = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(
    runtime.createConstructorContext(null, walletKey),
  );
  const context = (circuitId, contractState) => runtime.createCircuitContext({
    circuitId,
    contractAddress: runtime.dummyContractAddress(),
    coinPublicKeyOrZswapState: walletKey,
    contractState,
    privateState: null,
  });
  const invoke = async (name, state, ...args) => {
    const call = await contract.circuits[name](context(name, state), ...args);
    return [call.result, call.context.callContext.currentQueryContext.state];
  };
  const observe = async (stage, state) => {
    const [isEmpty] = await invoke('read', state);
    const size = ledger(state).flags.size();
    assert.equal(isEmpty, size === 0n, `${stage}: circuit isEmpty must match generated Map size`);
    return { stage, size: size.toString(), isEmpty };
  };

  const observations = [];
  let state = currentContractState.data;
  observations.push(await observe('empty', state));

  [, state] = await invoke('put', state, 2n, true);
  observations.push(await observe('insert', state));

  [, state] = await invoke('put', state, 2n, false);
  assert.equal(ledger(state).flags.member(2n), true, 'overwrite keeps the key in the Map');
  assert.equal(ledger(state).flags.lookup(2n), false, 'overwrite stores false as the value');
  observations.push(await observe('overwrite', state));

  [, state] = await invoke('remove', state, 2n);
  observations.push(await observe('remove', state));

  assert.deepEqual(observations, [
    { stage: 'empty', size: '0', isEmpty: true },
    { stage: 'insert', size: '1', isEmpty: false },
    { stage: 'overwrite', size: '1', isEmpty: false },
    { stage: 'remove', size: '0', isEmpty: true },
  ]);
  console.log(JSON.stringify({
    compact: compilerVersion,
    runtime: runtimePackage.version,
    observations,
  }));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
