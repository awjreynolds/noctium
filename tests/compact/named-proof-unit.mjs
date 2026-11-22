import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/named-proof-unit.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const runtimeDirectory = resolve(runtimePath);
const version = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(version, /^0\.36\.1 \(7fa3a117c/,
  `expected pinned Compact 0.36.1 compiler, got ${version}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const generated = mkdtempSync(join(experiments, '437-named-proof-unit-'));

try {
  execFileSync(compactc, [
    '--skip-zk', join(projectRoot, 'tests/compact/NamedProofUnit.compact'), generated,
  ]);
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtimeUrl = pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href;
  const contractUrl = pathToFileURL(join(generated, 'contract/index.js')).href;
  const { createCircuitContext, createConstructorContext, dummyContractAddress } = await import(runtimeUrl);
  const { Contract } = await import(contractUrl);
  const contract = new Contract({});
  const walletKey = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(createConstructorContext(null, walletKey));
  const context = () => createCircuitContext({
    circuitId: 'checkGate',
    contractAddress: dummyContractAddress(),
    coinPublicKeyOrZswapState: walletKey,
    contractState: currentContractState.data,
    privateState: null,
  });

  const success = await contract.circuits.checkGate(context(), true);
  assert.deepEqual(success.result, []);
  let failureMessage;
  await assert.rejects(async () => contract.circuits.checkGate(context(), false), (error) => {
    failureMessage = error.message;
    assert.match(failureMessage, /gate denied/);
    return true;
  });
  console.log(JSON.stringify({ success: success.result, failure: failureMessage }));
} finally {
  rmSync(generated, { recursive: true, force: true });
}
