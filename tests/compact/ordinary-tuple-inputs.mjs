import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/ordinary-tuple-inputs.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/, `unexpected Compact compiler: ${compilerVersion}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, '1506-ordinary-tuple-inputs-'));

try {
  const generated = join(scratch, 'compact');
  const source = join(projectRoot, 'tests/compact/OrdinaryTupleInputs.compact');
  execFileSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });

  const interfaceInfo = JSON.parse(readFileSync(join(generated, 'compiler/contract-info.json'), 'utf8'));
  assert.equal(interfaceInfo['compiler-commit'], '7fa3a117c5e7efe9d2c51da04263e5f0b3509144');
  const projection = interfaceInfo.circuits.find((circuit) => circuit.name === 'tupleProjection');
  assert.deepEqual(projection.arguments, [{
    name: 'pair',
    type: {
      'type-name': 'Tuple',
      types: [{ 'type-name': 'Uint', maxval: 255 }, { 'type-name': 'Boolean' }],
    },
  }]);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  assert.equal(runtime.versionString, '0.21.0');
  const { Contract } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const contract = new Contract({});
  const walletKey = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(
    runtime.createConstructorContext(null, walletKey),
  );
  const context = runtime.createCircuitContext({
    circuitId: 'tupleProjection',
    contractAddress: runtime.dummyContractAddress(),
    coinPublicKeyOrZswapState: walletKey,
    contractState: currentContractState.data,
    privateState: null,
  });

  const projected = await contract.circuits.tupleProjection(context, [173n, true]);
  assert.deepEqual(projected.result, [173n, true]);
  await assert.rejects(
    async () => contract.circuits.tupleProjection(context, [256n, true]),
    'out-of-range Uint<8> tuple leaf should fail runtime validation',
  );
  await assert.rejects(
    async () => contract.circuits.tupleProjection(context, [173n]),
    'short tuple should fail runtime validation',
  );

  console.log(JSON.stringify({
    compiler: compilerVersion,
    runtime: runtime.versionString,
    circuit: 'tupleProjection',
    accepted: [173, true],
    rejected: ['Uint<8> leaf 256', 'tuple with one leaf'],
  }));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
