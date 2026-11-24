import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/either-branch-construction.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/,
  `expected pinned Compact 0.36.1 compiler, got ${compilerVersion}`);
const runtimeDirectory = resolve(runtimePath);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0', 'expected pinned Compact runtime 0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'either-branch-construction-'));

try {
  const generated = join(scratch, 'compact');
  const source = join(projectRoot, 'tests/compact/EitherBranchConstruction.compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  assert.equal(runtime.versionString, '0.21.0');
  const { Contract } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const calls = [];
  const limits = { count: 17n, enabled: true, memo: Uint8Array.of(0, 1, 2, 255) };
  const vector = [true, false];
  const contract = new Contract({
    loadLimits: ({ privateState }) => {
      calls.push('loadLimits');
      return [privateState, limits];
    },
    loadFlags: ({ privateState }) => {
      calls.push('loadFlags');
      return [privateState, vector];
    },
  });
  const wallet = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(
    runtime.createConstructorContext(null, wallet),
  );
  const context = (circuitId) => runtime.createCircuitContext({
    circuitId,
    contractAddress: runtime.dummyContractAddress(),
    coinPublicKeyOrZswapState: wallet,
    contractState: currentContractState.data,
    privateState: null,
  });

  const leftResult = await contract.circuits.makeLeft(context('makeLeft'));
  assert.deepEqual(leftResult.result, {
    is_left: true,
    left: limits,
    right: [false, false],
  });
  assert.deepEqual(calls, ['loadLimits']);
  const makeLeftWitnessCalls = calls.length;

  calls.length = 0;
  const rightResult = await contract.circuits.makeRight(context('makeRight'));
  assert.deepEqual(rightResult.result, {
    is_left: false,
    left: { count: 0n, enabled: false, memo: new Uint8Array(4) },
    right: vector,
  });
  assert.deepEqual(calls, ['loadFlags']);
  const makeRightWitnessCalls = calls.length;

  console.log(JSON.stringify({
    fixture: 'EitherBranchConstruction',
    compact: compilerVersion,
    runtime: runtimePackage.version,
    left: {
      is_left: true,
      payload: { count: '17', enabled: true, memo: [0, 1, 2, 255] },
      inactive: [false, false],
    },
    right: {
      is_left: false,
      inactive: { count: '0', enabled: false, memo: [0, 0, 0, 0] },
      payload: vector,
    },
    activeWitnessCalls: { makeLeft: makeLeftWitnessCalls, makeRight: makeRightWitnessCalls },
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
