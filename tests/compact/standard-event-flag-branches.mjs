import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeArgument, output] = process.argv.slice(2);
assert.ok(compactc && runtimeArgument,
  'usage: node standard-event-flag-branches.mjs <compactc-0.36.1> <compact-runtime-0.21.0> [reference-output]');
const compiler = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compiler, /^0\.36\.1 \(7fa3a117c/);
const runtimeDirectory = resolve(runtimeArgument);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const sourceDirectory = dirname(fileURLToPath(import.meta.url));
const projectRoot = resolve(sourceDirectory, '../..');
const source = join(sourceDirectory, 'StandardEventFlagBranches.compact');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'standard-event-flag-branches-'));
const eventTypes = [
  'shielded-receive', 'shielded-mint', 'shielded-burn',
  'unshielded-spend', 'unshielded-receive', 'unshielded-burn',
];
const eventTags = [1, 2, 3, 4, 5, 7];
const widths = [578, 81, 49, 145, 145, 113];
const bytes = (length, seed) => Uint8Array.from({ length }, (_, index) => (seed + index * 17) % 251 + 1);
const pairs = [[false, false], [false, true], [true, false], [true, true]];
const fixedInputs = {
  receiveCommitment: bytes(32, 3), receiveCiphertext: bytes(512, 19), receiveContract: bytes(32, 37),
  mintCommitment: bytes(32, 53), mintDomain: bytes(32, 71), mintAmount: (1n << 111n) + 0x12345n,
  burnNullifier: bytes(32, 89), burnAmount: (1n << 109n) + 0x34567n,
  spendUserKey: bytes(32, 107), spendContract: bytes(32, 127), spendDomain: bytes(32, 149),
  spendToken: bytes(32, 167), spendAmount: (1n << 107n) + 0x56789n,
  receiveUserKey: bytes(32, 181), receiveAddress: bytes(32, 199), receiveDomain: bytes(32, 211),
  receiveToken: bytes(32, 229), receiveAmount: (1n << 105n) + 0x789abn,
  unshieldedBurnUserKey: bytes(32, 23), unshieldedBurnContract: bytes(32, 41),
  unshieldedBurnToken: bytes(32, 59), unshieldedBurnAmount: (1n << 103n) + 0x9abcdn,
};
const nativeInputs = Object.fromEntries(Object.entries(fixedInputs).map(([name, value]) => [
  name,
  value instanceof Uint8Array ? { kind: 'bytes', values: [...value] } : value.toString(),
]));

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
  const run = async (present, route) => contract.circuits.emitFlagBranches(
    runtime.createCircuitContext({
      circuitId: 'emitFlagBranches',
      contractAddress: runtime.dummyContractAddress(),
      coinPublicKeyOrZswapState: coinPublicKey,
      contractState: currentContractState.data,
      privateState: null,
    }),
    present, route,
    fixedInputs.receiveCommitment, fixedInputs.receiveCiphertext, fixedInputs.receiveContract,
    fixedInputs.mintCommitment, fixedInputs.mintDomain, fixedInputs.mintAmount,
    fixedInputs.burnNullifier, fixedInputs.burnAmount,
    fixedInputs.spendUserKey, fixedInputs.spendContract, fixedInputs.spendDomain,
    fixedInputs.spendToken, fixedInputs.spendAmount,
    fixedInputs.receiveUserKey, fixedInputs.receiveAddress, fixedInputs.receiveDomain,
    fixedInputs.receiveToken, fixedInputs.receiveAmount,
    fixedInputs.unshieldedBurnUserKey, fixedInputs.unshieldedBurnContract,
    fixedInputs.unshieldedBurnToken, fixedInputs.unshieldedBurnAmount,
  );

  const cases = [];
  for (const [present, route] of pairs) {
    const call = await run(present, route);
    assert.equal(call.context.events.length, eventTypes.length);
    const events = call.context.events.map(({ version, eventType, data }, order) => {
      assert.equal(version, 1);
      assert.equal(eventType, eventTypes[order]);
      assert.equal(data.tag, 'cell');
      const { alignment, value } = data.content;
      const payloadLength = widths[order];
      assert.deepEqual(alignment, [{ tag: 'atom', value: { tag: 'bytes', length: payloadLength } }]);
      assert.equal(value.length, 1);
      assert.ok(value[0] instanceof Uint8Array);
      assert.ok(value[0].length <= payloadLength);
      const padded = new Uint8Array(payloadLength);
      padded.set(value[0]);
      return {
        version, tag: eventTags[order], order, eventType, payloadLength,
        payloadSha256: createHash('sha256').update(padded).digest('hex'),
      };
    });
    cases.push({ present, route, events });
  }
  const reference = { compiler, runtime: runtime.versionString, nativeInputs, cases };
  if (output) {
    writeFileSync(output, JSON.stringify(reference, null, 2) + '\n');
  } else {
    const retained = join(projectRoot, 'tests/standard-event-flag-branches-compact.json');
    assert.deepEqual(reference, JSON.parse(readFileSync(retained, 'utf8')));
  }
  console.log(`Compact ${compiler} matched ${cases.length} flag pairs across ${eventTypes.length} event layouts`);
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
