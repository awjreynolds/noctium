import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, rmdirSync, symlinkSync, writeFileSync } from 'node:fs';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/readable-generic-range.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/,
  `expected pinned Compact 0.36.1 compiler, got ${compilerVersion}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0', 'expected pinned Compact runtime 0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/ReadableGenericRange.compact');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'readable-generic-range-'));
process.on('exit', () => {
  rmSync(scratch, { recursive: true, force: true });
  try {
    rmdirSync(experiments);
  } catch (error) {
    if (error.code !== 'ENOENT' && error.code !== 'ENOTEMPTY') throw error;
  }
});

const generated = join(scratch, 'compact');
const compile = spawnSync(compactc, ['--skip-zk', source, generated], {
  cwd: projectRoot,
  encoding: 'utf8',
});
assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

const runtimeBoundSource = join(scratch, 'runtime-bound.compact');
writeFileSync(runtimeBoundSource, `${readFileSync(source, 'utf8')}\nexport circuit runtimeBound(start: Uint<8>): Field {
  return applyRange<start, 3>();
}\n`);
const runtimeBound = spawnSync(compactc,
  ['--skip-zk', runtimeBoundSource, join(scratch, 'runtime-bound')], {
    cwd: projectRoot,
    encoding: 'utf8',
  });
assert.notEqual(runtimeBound.status, 0, 'Compact should reject a runtime-derived generic range bound');
assert.match(`${runtimeBound.stderr}\n${runtimeBound.stdout}`,
  /invalid context for reference to variable name start/);

const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
mkdirSync(dirname(runtimeLink), { recursive: true });
symlinkSync(runtimeDirectory, runtimeLink, 'dir');
const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
const { Contract, ledger } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
assert.equal(runtime.versionString, '0.21.0');

const calls = [];
const contract = new Contract({
  visit: ({ privateState }, index) => {
    calls.push(Number(index));
    return [[...privateState, Number(index)], BigInt(index)];
  },
});
const wallet = '00'.repeat(32);
const { currentContractState } = await contract.initialState(
  runtime.createConstructorContext({ total: 0n }, wallet));
const contextFor = (circuitId) => runtime.createCircuitContext({
  circuitId,
  contractAddress: runtime.dummyContractAddress(),
  coinPublicKeyOrZswapState: wallet,
  contractState: currentContractState.data,
  privateState: [],
});

const nonEmpty = await contract.circuits.nonEmptyRange(contextFor('nonEmptyRange'));
assert.equal(nonEmpty.result, 3n);
assert.equal(ledger(nonEmpty.context.callContext.currentQueryContext.state).total, 3n);
assert.deepEqual(calls, [1, 2]);
assert.deepEqual(nonEmpty.context.callContext.currentPrivateState, [1, 2]);
const nonEmptyCalls = [...calls];

calls.length = 0;
const empty = await contract.circuits.emptyRange(contextFor('emptyRange'));
assert.equal(empty.result, 0n);
assert.equal(ledger(empty.context.callContext.currentQueryContext.state).total, 0n);
assert.deepEqual(calls, [], 'equal static bounds should execute zero iterations');
assert.deepEqual(empty.context.callContext.currentPrivateState, []);

console.log(JSON.stringify({
  nonEmpty: { result: nonEmpty.result.toString(), calls: nonEmptyCalls },
  empty: { result: empty.result.toString(), calls },
  runtimeBound: 'rejected',
}));
