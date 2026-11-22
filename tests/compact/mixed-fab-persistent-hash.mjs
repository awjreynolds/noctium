import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/mixed-fab-persistent-hash.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/, `unexpected Compact compiler: ${compilerVersion}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, '275-mixed-fab-commitments-'));

try {
  const generated = join(scratch, 'compact');
  const source = join(projectRoot, 'tests/compact/MerklePathRootNoLeafHash.compact');
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
  const payloads = [257n, 258n].map((counter) => ({
    octets,
    flag: true,
    counter,
    marker: 0,
    anchor: 42n,
  }));
  const opening = new Uint8Array(32).fill(9);
  const nonce = 77n;
  const persistentHashes = [];
  const persistentCommitments = [];
  const transientCommitments = [];
  const transientHashes = [];
  async function fabHashes(payload, persistentOpening, transientOpening) {
    const context = runtime.createCircuitContext({
      circuitId: 'fabHashes',
      contractAddress: runtime.dummyContractAddress(),
      coinPublicKeyOrZswapState: walletKey,
      contractState: currentContractState.data,
      privateState: null,
    });
    const call = await contract.circuits.fabHashes(
      context, payload, persistentOpening, transientOpening,
    );
    assert.ok(Array.isArray(call.result) && call.result.length === 4, 'expected four FAB hash outputs');
    return call.result;
  }

  for (const payload of payloads) {
    const result = await fabHashes(payload, opening, nonce);
    persistentHashes.push(Buffer.from(result[0]).toString('hex'));
    persistentCommitments.push(Buffer.from(result[1]).toString('hex'));
    transientHashes.push(result[2].toString());
    transientCommitments.push(result[3].toString());
  }

  assert.deepEqual(persistentHashes, [
    '05743c725c44c8d77bf1b9601385ef901ec4040ecb770014a535ddcb5e2840d9',
    '4376a00dd2129c85219a8aecd9a8209cad4fdc8d333ed7e127f71220697490c2',
  ]);
  assert.notEqual(persistentHashes[0], persistentHashes[1],
    'persistentHash must bind the changed UInt16 field');

  assert.deepEqual(persistentCommitments, [
    'cff69459a493e86a1276354b70bcb77aaac2edaaac6802fda770a68723f3d68d',
    'c24011e4183df55510160926607b3dc3bcae795f70b69db0e370e9bf9669ccdc',
  ]);
  assert.deepEqual(transientCommitments, [
    '26379122738253202444518886441389591496658820157546698964272146379194073575416',
    '52175680914820761057797808711717819206214043408631344658262904895711887709638',
  ]);
  assert.deepEqual(transientHashes, [
    '31450192802498090922990245422064529103765978660401260400662966898300129689545',
    '45341827361802937545085556155854399066079167850897885488099005759856344686712',
  ]);
  assert.notEqual(transientHashes[0], transientHashes[1],
    'transientHash must bind the changed UInt16 field');

  const changedPersistentOpening = await fabHashes(
    payloads[0], new Uint8Array(32).fill(10), nonce,
  );
  assert.equal(Buffer.from(changedPersistentOpening[0]).toString('hex'), persistentHashes[0]);
  assert.equal(changedPersistentOpening[2].toString(), transientHashes[0]);
  assert.equal(
    Buffer.from(changedPersistentOpening[1]).toString('hex'),
    '34f5becb77595f7a8e7eda241d9c187f87e97e5c4af68a14577b668c519030fe',
  );
  assert.equal(changedPersistentOpening[3].toString(), transientCommitments[0]);

  const changedTransientOpening = await fabHashes(
    payloads[0], opening, 78n,
  );
  assert.equal(Buffer.from(changedTransientOpening[0]).toString('hex'), persistentHashes[0]);
  assert.equal(Buffer.from(changedTransientOpening[1]).toString('hex'), persistentCommitments[0]);
  assert.equal(changedTransientOpening[2].toString(), transientHashes[0]);
  assert.equal(
    changedTransientOpening[3].toString(),
    '1245246646047273088008560749436502138436832274864845859888856457488273394968',
  );

  console.log(JSON.stringify({
    compiler: compilerVersion,
    runtime: runtime.versionString,
    circuit: 'fabHashes',
    layout: ['Bytes<32>', 'Boolean', 'Uint<16>', 'LeafMarker', 'Field'],
    inputs: payloads.map(({ counter }) => ({ counter: counter.toString() })),
    persistentHashes,
    persistentCommitments,
    transientHashes,
    transientCommitments,
  }));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
