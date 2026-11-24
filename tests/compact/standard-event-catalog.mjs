import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeArgument, output] = process.argv.slice(2);
assert.ok(compactc && runtimeArgument,
  'usage: node tests/compact/standard-event-catalog.mjs <compactc-0.36.1> <compact-runtime-0.21.0> [reference-output]');

const compiler = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compiler, /^0\.36\.1 \(7fa3a117c/);
const runtimeDirectory = resolve(runtimeArgument);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const sourceDirectory = dirname(fileURLToPath(import.meta.url));
const projectRoot = resolve(sourceDirectory, '../..');
const source = join(sourceDirectory, 'StandardEventCatalog.compact');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'standard-event-catalog-'));
const eventTypes = [
  'shielded-spend', 'shielded-receive', 'shielded-mint', 'shielded-burn',
  'unshielded-spend', 'unshielded-receive', 'unshielded-mint', 'unshielded-burn',
  'paused', 'unpaused', 'misc',
];
const widths = [32, 578, 81, 49, 145, 145, 80, 113, 0, 0, 288];
const bytes = (length, start) => Uint8Array.from({ length }, (_, index) => (start + index) % 256);

try {
  const generated = join(scratch, 'compiled');
  execFileSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  const { Contract } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  assert.equal(runtime.versionString, '0.21.0');
  const contract = new Contract({});
  const coinPublicKey = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(
    runtime.createConstructorContext(null, coinPublicKey),
  );
  const runCatalog = async (memo, quantity) => contract.circuits.logCatalog(
    runtime.createCircuitContext({
      circuitId: 'logCatalog',
      contractAddress: runtime.dummyContractAddress(),
      coinPublicKeyOrZswapState: coinPublicKey,
      contractState: currentContractState.data,
      privateState: null,
    }),
    bytes(32, 1), bytes(32, 225), bytes(512, 1), memo, quantity,
  );
  const quantity = (1n << 127n) + 0x10203n;
  const memo = bytes(256, 2);
  const call = await runCatalog(memo, quantity);
  assert.equal(call.context.events.length, eventTypes.length);

  const events = call.context.events.map(({ version, eventType, data }, tag) => {
    assert.equal(version, 1);
    assert.equal(eventType, eventTypes[tag]);
    assert.equal(data.tag, 'cell');
    const { alignment, value } = data.content;
    const payloadLength = widths[tag];
    assert.deepEqual(alignment, [{ tag: 'atom', value: { tag: 'bytes', length: payloadLength } }]);
    assert.equal(value.length, 1);
    assert.ok(value[0] instanceof Uint8Array);
    assert.ok(value[0].length <= payloadLength);
    // FAB byte atoms omit trailing zeros. Hash the aligned event payload.
    const payload = new Uint8Array(payloadLength);
    payload.set(value[0]);
    const payloadSha256 = createHash('sha256').update(payload).digest('hex');
    return { version, tag, payloadLength, payloadSha256 };
  });
  const reference = { compiler, runtime: runtime.versionString, events };
  if (output) {
    writeFileSync(output, JSON.stringify(reference, null, 2) + '\n');
  } else {
    const retained = join(projectRoot, 'tests/standard-event-catalog-compact.json');
    assert.deepEqual(reference, JSON.parse(readFileSync(retained, 'utf8')));
  }
  await assert.rejects(() => runCatalog(bytes(255, 2), quantity), /256/);
  await assert.rejects(() => runCatalog(memo, 1n << 128n), /expected value of type Uint.*received 340282366920938463463374607431768211456n/);
  console.log(`Compact ${compiler} matched all ${events.length} layouts and rejected invalid memo width and amount`);
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
