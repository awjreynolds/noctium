import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/readable-bind-patterns.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const version = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(version, /^0\.36\.1 \(7fa3a117c/, `expected pinned Compact 0.36.1 compiler, got ${version}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0', 'expected pinned Compact runtime 0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/ReadableBindPatterns.compact');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'readable-bind-patterns-'));

try {
  const generated = join(scratch, 'compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  assert.equal(runtime.versionString, '0.21.0');
  const { createCircuitContext, createConstructorContext, dummyContractAddress } = runtime;
  const { Contract } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const calls = [];
  const contract = new Contract({
    load: ({ privateState }, seed) => {
      calls.push(seed);
      return [privateState, {
        reading: { count: 17n, active: true },
        measures: [9n, false],
        omitted: 5n,
      }];
    },
  });
  const wallet = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(createConstructorContext(null, wallet));
  const { result } = await contract.circuits.unpack(createCircuitContext({
    circuitId: 'unpack',
    contractAddress: dummyContractAddress(),
    coinPublicKeyOrZswapState: wallet,
    contractState: currentContractState.data,
    privateState: null,
  }), 7n);

  assert.equal(result, 26n);
  assert.deepEqual(calls, [7n]);
  console.log(JSON.stringify({ result: result.toString(), calls: calls.map(String) }));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
