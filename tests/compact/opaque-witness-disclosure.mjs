import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/opaque-witness-disclosure.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const version = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(version, /^0\.36\.1 \(7fa3a117c/, `expected pinned Compact 0.36.1 compiler, got ${version}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0', 'expected pinned Compact runtime 0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/OpaqueWitnessDisclosure.compact');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, '1224-opaque-witness-disclosure-'));

try {
  const generated = join(scratch, 'compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtimeUrl = pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href;
  const contractUrl = pathToFileURL(join(generated, 'contract/index.js')).href;
  const runtime = await import(runtimeUrl);
  const { Contract, ledger } = await import(contractUrl);
  const label = 'A\0夜\0B';
  const contract = new Contract({
    readPrivateLabel: ({ privateState }) => [privateState, label],
  });
  const wallet = '00'.repeat(32);
  const initial = await contract.initialState(runtime.createConstructorContext(null, wallet));
  const contextFor = (circuitId, contractState, privateState = null) => runtime.createCircuitContext({
    circuitId,
    contractAddress: runtime.dummyContractAddress(),
    coinPublicKeyOrZswapState: wallet,
    contractState,
    privateState,
  });
  const published = await contract.circuits.publish(
    contextFor('publish', initial.currentContractState.data),
  );
  const state = published.context.callContext.currentQueryContext.state;
  assert.equal(ledger(state).label, label);
  const trace = published.context.callProofDataTrace.at(-1);
  const encoded = new TextEncoder().encode(label);
  const compress = [{ tag: 'atom', value: { tag: 'compress' } }];
  assert.deepEqual([...trace.privateTranscriptOutputs[0].value[0]], [...encoded]);
  assert.deepEqual(trace.privateTranscriptOutputs[0].alignment, compress);
  const storedCell = trace.publicTranscript.find(operation => operation.push?.storage);
  assert.deepEqual([...storedCell.push.value.content.value[0]], [...encoded]);
  assert.deepEqual(storedCell.push.value.content.alignment, compress);

  const read = await contract.circuits.readLabel(contextFor('readLabel', state));
  assert.equal(read.result, label);

  const wrongType = new Contract({
    readPrivateLabel: ({ privateState }) => [privateState, new Uint8Array([1])],
  });
  await assert.rejects(
    () => wrongType.circuits.publish(contextFor('publish', state)),
    /readPrivateLabel.*return value/s,
  );
  await assert.rejects(
    () => new Contract({
      readPrivateLabel: ({ privateState }) => [privateState, 'trailing\0'],
    }).circuits.publish(contextFor('publish', state)),
    /aligned value is not in normal form \(has trailing zero bytes\)/,
  );

  console.log('Compact 0.36.1 disclosed a private OpaqueString witness into a public root Cell and preserved interior NULs');
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
