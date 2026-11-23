import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/generic-jubjub-module.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(root, 'tests/compact/GenericJubjubModule.compact');
const experiments = join(root, 'build/experiments/847');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'generic-jubjub-module-'));
try {
  const generated = join(scratch, 'compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, compile.stderr || compile.stdout);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');
  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  const { Contract } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const contract = new Contract({});
  const wallet = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(
    runtime.createConstructorContext(null, wallet),
  );
  const context = circuitId => runtime.createCircuitContext({
    circuitId,
    contractAddress: runtime.dummyContractAddress(),
    coinPublicKeyOrZswapState: wallet,
    contractState: currentContractState.data,
    privateState: null,
  });

  const scalar = 37n;
  const scalarCall = await contract.circuits.scalar_identity(context('scalar_identity'), scalar);
  assert.equal(scalarCall.result, scalar);

  const point = runtime.ecMulGenerator(1n);
  const pointCall = await contract.circuits.point_identity(context('point_identity'), point);
  assert.deepEqual(pointCall.result, point);
  console.log(JSON.stringify({
    fixture: 'GenericJubjubModule',
    compact: compilerVersion,
    runtime: runtimePackage.version,
    scalar: scalarCall.result.toString(),
    point: { x: pointCall.result.x.toString(), y: pointCall.result.y.toString() },
  }));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
