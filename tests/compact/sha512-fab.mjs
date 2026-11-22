import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/sha512-fab.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/, `unexpected Compact compiler: ${compilerVersion}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, '298-sha512-fab-'));

try {
  const generated = join(scratch, 'compact');
  const source = join(projectRoot, 'tests/compact/Sha512Fab.compact');
  execFileSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });

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

  const octets = Uint8Array.from({ length: 32 }, (_, index) => index + 1);
  const digests = [];
  const keccakDigests = [];
  async function sha512Payload(counter) {
    const context = runtime.createCircuitContext({
      circuitId: 'sha512Fab',
      contractAddress: runtime.dummyContractAddress(),
      coinPublicKeyOrZswapState: walletKey,
      contractState: currentContractState.data,
      privateState: null,
    });
    const call = await contract.circuits.sha512Fab(context, {
      octets,
      flag: true,
      counter,
      anchor: 42n,
    });
    assert.ok(Array.isArray(call.result) && call.result.length === 2, 'expected two digest outputs');
    digests.push(Buffer.from(call.result[0]).toString('hex'));
    keccakDigests.push(Buffer.from(call.result[1]).toString('hex'));
  }

  await sha512Payload(257n);
  await sha512Payload(258n);

  assert.deepEqual(digests, [
    '6f2b8bc408127949730a24dd6a4b5562a8ec69a7d895a79329c13976447a1c948c4a84e6d070af7e02ea37d89408d1a0679dee79fd6c3cb40e548e4438b7bfae',
    'd65da98a4c62937f9f0aa99c4b68dd81d171a73be6f09f03a85d251ea58d1b6d54d55002038ad3ef43a53c8e43ef808eda8beb48679b092434bffc063bd519aa',
  ]);
  assert.deepEqual(keccakDigests, [
    '0a3cf3d2108f7463f9ef5896ebfd31c7fcdde34ac2171cc6b3c48f28d03e8683',
    'eb28a2f9796f720f03aea8e43e7e6ec85e202d85258bd36da513f50f32acf5ee',
  ]);

  console.log(JSON.stringify({
    compiler: compilerVersion,
    runtime: runtime.versionString,
    circuit: 'sha512Fab',
    fields: ['Bytes<32>', 'Boolean', 'Uint<16>', 'Field'],
    digests,
    keccakDigests,
  }));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
