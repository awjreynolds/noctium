import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeArgument] = process.argv.slice(2);
assert.ok(compactc && runtimeArgument,
  'usage: node tests/compact/standard-helper-events.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/);
const runtimeDirectory = resolve(runtimeArgument);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.version, '0.21.0');

const sourceDirectory = dirname(fileURLToPath(import.meta.url));
const projectRoot = resolve(sourceDirectory, '../..');
const source = join(sourceDirectory, 'StandardHelperEvents.compact');
const reference = JSON.parse(readFileSync(
  join(projectRoot, 'tests/standard-helper-event-localnet-evidence.json'), 'utf8',
));
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'standard-helper-events-'));

const eventTypeByTag = new Map([
  [0, 'shielded-spend'],
  [8, 'paused'],
  [9, 'unpaused'],
]);

const checkEvents = (events, expected) => {
  assert.equal(events.length, expected.length);
  for (const [event, receipt] of events.map((event, index) => [event, expected[index]])) {
    assert.equal(event.version, receipt.version);
    assert.equal(event.eventType, eventTypeByTag.get(receipt.tag));
    assert.equal(event.data.tag, 'cell');

    const { value, alignment } = event.data.content;
    assert.equal(alignment.length, 1);
    assert.equal(alignment[0].tag, 'atom');
    assert.deepEqual(alignment[0].value, { tag: 'bytes', length: receipt.payloadLength });
    assert.equal(value.length, 1);
    assert.ok(value[0] instanceof Uint8Array);
    assert.equal(value[0].length, receipt.payloadLength);
    assert.equal(createHash('sha256').update(value[0]).digest('hex'), receipt.payloadSha256);
  }
};

try {
  const generated = join(scratch, 'compiled');
  execFileSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  const { Contract } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const contract = new Contract({});
  const coinPublicKey = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(
    runtime.createConstructorContext(null, coinPublicKey),
  );
  const nullifier = Uint8Array.from({ length: 32 }, (_, index) => index + 1);
  const invoke = async (circuitId, ...arguments_) => {
    const context = runtime.createCircuitContext({
      circuitId,
      contractAddress: runtime.dummyContractAddress(),
      coinPublicKeyOrZswapState: coinPublicKey,
      contractState: currentContractState.data,
      privateState: null,
    });
    const call = await contract.circuits[circuitId](context, ...arguments_);
    return call.context.events;
  };

  checkEvents(await invoke('logHelperSpend', true, nullifier), reference.receipts.active.events);
  checkEvents(await invoke('logHelperSpend', false, nullifier), reference.receipts.inactive.events);
  for (const width of [31, 33]) {
    const invalidNullifier = new Uint8Array(width).fill(1);
    await assert.rejects(() => invoke('logHelperSpend', true, invalidNullifier), /Bytes<32>/);
  }
  checkEvents(await invoke('logGuardedPause', true), reference.receipts.inactive.events);
  checkEvents(await invoke('logGuardedPause', false), []);
  for (const event of ['Paused', 'Unpaused']) {
    const invalid = join(scratch, `Invalid${event}.compact`);
    writeFileSync(invalid, `pragma language_version 0.28;
import CompactStandardLibrary;
export circuit invalid(): [] { emit(${event} { reason: true }); }
`);
    assert.throws(
      () => execFileSync(compactc, ['--skip-zk', invalid, join(scratch, `invalid-${event}`)], {
        stdio: 'pipe',
      }),
      /reason/,
    );
  }
  console.log(`Compact ${compilerVersion} matched the finalized helper logs and guarded pause events`);
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
