import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/wide-public-bytes.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
assert.match(execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim(),
  /^0\.36\.1 \(7fa3a117c/);
const runtimeDirectory = resolve(runtimePath);
const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
assert.equal(runtime.versionString, '0.21.0');

const fixtures = dirname(fileURLToPath(import.meta.url));
const experiments = resolve(fixtures, '../../build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'wide-public-bytes-'));
try {
  const generated = join(scratch, 'compact');
  execFileSync(compactc, ['--skip-zk', join(fixtures, 'WidePublicBytes.compact'), generated]);
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const { Contract } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const wallet = '00'.repeat(32);
  const contract = new Contract({});
  const { currentContractState } = await contract.initialState(
    runtime.createConstructorContext(null, wallet));
  const context = (circuitId) => runtime.createCircuitContext({
    circuitId,
    contractAddress: runtime.dummyContractAddress(),
    coinPublicKeyOrZswapState: wallet,
    contractState: currentContractState.data,
    privateState: null,
  });
  for (const [circuitId, length] of [
    ['roundTrip', 1025],
    ['roundTrip1055', 1055],
    ['roundTrip4096', 4096],
  ]) {
    const payload = Uint8Array.from({ length }, (_, index) => index % 251);
    payload.set([0xa5, 0x5a], length - 2);
    assert.deepEqual(
      (await contract.circuits[circuitId](context(circuitId), payload)).result,
      payload,
    );
    await assert.rejects(async () =>
      contract.circuits[circuitId](context(circuitId), payload.slice(0, -1)));
  }
  console.log('1025, 1055, and 4096 bytes round-tripped with tail a55a. Short inputs rejected.');
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
