import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, rmdirSync, symlinkSync } from 'node:fs';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/mixed-record-cell-reset.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/,
  `expected pinned Compact 0.36.1 compiler, got ${compilerVersion}`);
const runtimeDirectory = resolve(runtimePath);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0', 'expected pinned Compact runtime 0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(root, 'build/experiments/mixed-record-cell-reset');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'run-'));

try {
  const generated = join(scratch, 'compact');
  const source = join(root, 'tests/compact/MixedRecordCellReset.compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], {
    cwd: root,
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
  const wallet = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(
    runtime.createConstructorContext(null, wallet),
  );
  const initialState = currentContractState.data;
  const initial = {
    typedMemo: { active: true, amount: 513n },
    fixedBytesMemo: { active: true, payload: Uint8Array.from([115, 101, 101, 100]), amount: 1027n },
  };
  const defaults = {
    typedMemo: { active: false, amount: 0n },
    fixedBytesMemo: { active: false, payload: new Uint8Array(4), amount: 0n },
  };
  const read = state => {
    const view = ledger(state);
    return {
      typedMemo: view.typedMemo,
      fixedBytesMemo: view.fixedBytesMemo,
    };
  };
  const context = state => runtime.createCircuitContext({
    circuitId: 'clearMemos',
    contractAddress: runtime.dummyContractAddress(),
    coinPublicKeyOrZswapState: wallet,
    contractState: state,
    privateState: null,
  });

  assert.deepEqual(read(initialState), initial);
  for (const enabled of [false, true]) {
    const call = await contract.circuits.clearMemos(context(initialState), enabled);
    const afterState = call.context.callContext.currentQueryContext.state;
    const expectedState = enabled ? defaults : initial;
    assert.deepEqual(read(afterState), expectedState);
    assert.deepEqual(
      [...call.result.slice(0, 3), [...call.result[3]], call.result[4]],
      enabled
        ? [false, 0n, false, [0, 0, 0, 0], 0n]
        : [true, 513n, true, [115, 101, 101, 100], 1027n],
    );
  }

  console.log(JSON.stringify({
    fixture: 'MixedRecordCellReset',
    compiler: compilerVersion,
    runtime: runtimePackage.version,
    seeded: { typedMemo: { active: true, amount: '513' },
      fixedBytesMemo: { active: true, payload: [115, 101, 101, 100], amount: '1027' } },
    disabledPreserved: true,
    enabledResetBothToDefaults: true,
    typedReturnsChecked: true,
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
  try {
    rmdirSync(experiments);
  } catch (error) {
    if (error.code !== 'ENOENT' && error.code !== 'ENOTEMPTY') throw error;
  }
}
