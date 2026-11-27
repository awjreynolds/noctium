import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/mixed-fab-hash-to-curve.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/, `unexpected Compact compiler: ${compilerVersion}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, '306-mixed-fab-hash-to-curve-'));

try {
  const generated = join(scratch, 'compact');
  const source = join(projectRoot, 'tests/compact/MixedFabHashToCurve.compact');
  execFileSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  assert.equal(runtime.versionString, '0.21.0');
  const { Contract } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const octets = Uint8Array.from({ length: 32 }, (_, index) => index + 1);
  const payload = (counter) => ({ octets, flag: true, counter, marker: 0, anchor: 42n });
  const calls = [];
  const contract = new Contract({
    loadPayload(context, counter) {
      calls.push(counter);
      return [context.privateState, payload(counter === 0n ? 65536n : counter)];
    },
  });
  const walletKey = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(
    runtime.createConstructorContext(null, walletKey),
  );

  const points = [];
  const context = (circuitId) => runtime.createCircuitContext({
    circuitId,
    contractAddress: runtime.dummyContractAddress(),
    coinPublicKeyOrZswapState: walletKey,
    contractState: currentContractState.data,
    privateState: null,
  });
  async function hash(counter) {
    const call = await contract.circuits.hashToCurveFab(context('hashToCurveFab'), payload(counter));
    const witnessed = await contract.circuits.hashWitnessPayload(context('hashWitnessPayload'), counter);
    assert.ok(Array.isArray(call.result) && call.result.length === 1,
      'expected one hash-to-curve output');
    assert.deepEqual(witnessed.result, call.result);
    points.push({ x: call.result[0].x.toString(), y: call.result[0].y.toString() });
  }

  await hash(257n);
  await hash(258n);
  await assert.rejects(async () =>
    contract.circuits.hashWitnessPayload(context('hashWitnessPayload'), 0n));
  assert.deepEqual(calls, [257n, 258n, 0n]);
  assert.deepEqual(points, [
    {
      x: '28795585433567012869963935944812663991492396026676757706215428925031281335525',
      y: '22332899933082389804809036260506171817896244000051913394706757537977492146276',
    },
    {
      x: '29703381369117037955354524975024459739721474734473359661960630795432392269544',
      y: '27301738739419332019240484823733146733474981258073086105370655572681570990521',
    },
  ]);

  console.log(JSON.stringify({
    compiler: compilerVersion,
    runtime: runtime.versionString,
    circuit: 'hashToCurveFab',
    fields: ['Bytes<32>', 'Boolean', 'Uint<16>', 'LeafMarker', 'Field'],
    points,
  }));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
