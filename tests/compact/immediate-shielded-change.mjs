import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/immediate-shielded-change.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const version = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(version, /^0\.36\.1 \(7fa3a117c/, `expected pinned Compact 0.36.1 compiler, got ${version}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0', 'expected pinned Compact runtime 0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/ImmediateShieldedChange.compact');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'immediate-shielded-change-'));

try {
  const generated = join(scratch, 'compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], {
    cwd: projectRoot,
    encoding: 'utf8',
  });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtimeUrl = pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href;
  const contractUrl = pathToFileURL(join(generated, 'contract/index.js')).href;
  const { createCircuitContext, createConstructorContext, dummyContractAddress } = await import(runtimeUrl);
  const { Contract } = await import(contractUrl);
  const contract = new Contract({});
  const coinPublicKey = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(
    createConstructorContext(null, coinPublicKey),
  );
  const contextFor = (circuitId = 'splitImmediateShielded') => createCircuitContext({
    circuitId,
    contractAddress: dummyContractAddress(),
    coinPublicKeyOrZswapState: coinPublicKey,
    contractState: currentContractState.data,
    privateState: null,
  });
  const input = {
    color: new Uint8Array(32).fill(1),
    nonce: new Uint8Array(32).fill(2),
    value: 5n,
  };
  const recipient = { bytes: new Uint8Array(32).fill(3) };
  const toHex = (bytes) => Buffer.from(bytes).toString('hex');
  const repeatedByte = (byte) => byte.toString(16).padStart(2, '0').repeat(32);

  const { result, context } = await contract.circuits.splitImmediateShielded(
    contextFor(), input, recipient, 2n,
  );
  const changeNonce = '0283a70d7732a940d63ebf3957495f2549236d165e604aa67a59d7eb746f4b00';
  const sentNonce = '92411b27a7fe195f0f94f46bab957487031cb2702b4e6015adebe924fe246500';
  const color = repeatedByte(1);
  const self = repeatedByte(0);
  const target = repeatedByte(3);

  assert.equal(result.change.is_some, true);
  assert.deepEqual({
    nonce: toHex(result.sent.nonce),
    color: toHex(result.sent.color),
    value: result.sent.value,
  }, { nonce: sentNonce, color, value: 2n });
  assert.deepEqual({
    nonce: toHex(result.change.value.nonce),
    color: toHex(result.change.value.color),
    value: result.change.value.value,
  }, { nonce: changeNonce, color, value: 3n });

  const query = context.callContext.currentQueryContext;
  const offer = context.callContext.currentZswapLocalState;
  assert.equal(offer.currentIndex, 3n);
  assert.equal(offer.inputs.length, 1);
  assert.deepEqual({
    nonce: toHex(offer.inputs[0].nonce),
    color: toHex(offer.inputs[0].color),
    value: offer.inputs[0].value,
    mt_index: offer.inputs[0].mt_index,
  }, { nonce: repeatedByte(2), color, value: 5n, mt_index: 0n });
  assert.equal(offer.outputs.length, 3);
  const [received, sent, change] = offer.outputs;
  assert.deepEqual(offer.outputs.map(({ coinInfo }) => ({
    nonce: toHex(coinInfo.nonce),
    color: toHex(coinInfo.color),
    value: coinInfo.value,
  })), [
    { nonce: repeatedByte(2), color, value: 5n },
    { nonce: sentNonce, color, value: 2n },
    { nonce: changeNonce, color, value: 3n },
  ]);
  assert.equal(received.recipient.is_left, false);
  assert.equal(toHex(received.recipient.right.bytes), self);
  assert.equal(sent.recipient.is_left, true);
  assert.equal(toHex(sent.recipient.left.bytes), target);
  assert.equal(change.recipient.is_left, false);
  assert.equal(toHex(change.recipient.right.bytes), self);

  assert.deepEqual(query.effects.claimedNullifiers, [
    'd119520f9cd70fb3b835e7421773629b1991e38d642ff9b6b69eb9ed1bf86c24',
  ]);
  assert.deepEqual(query.effects.claimedShieldedSpends, [
    'ed1aadafa7d1883bc63e45853fc4b51f21fb99c6ae68c8de9a256cbc3ac299c7',
    'ac1f3bb1ec93068af7810556a541cd2fbd3eb3e8e1c4336a7e5a72ee403405c2',
  ]);
  assert.deepEqual(query.effects.claimedShieldedReceives, [
    '84a93c4d7971bb71252e9b01a8cc75f4daffdcac90c25c3d3ea484a1b6eae3a0',
    'ac1f3bb1ec93068af7810556a541cd2fbd3eb3e8e1c4336a7e5a72ee403405c2',
  ]);

  const rejectedContext = contextFor();
  await assert.rejects(
    contract.circuits.splitImmediateShielded(rejectedContext, input, recipient, 6n),
    /result of subtraction would be negative/,
  );
  assert.equal(rejectedContext.callContext.currentZswapLocalState.currentIndex, 0n);
  assert.deepEqual(rejectedContext.callContext.currentZswapLocalState.inputs, []);
  assert.deepEqual(rejectedContext.callContext.currentZswapLocalState.outputs, []);
  assert.deepEqual(rejectedContext.callContext.currentQueryContext.effects.claimedNullifiers, []);
  assert.deepEqual(rejectedContext.callContext.currentQueryContext.effects.claimedShieldedSpends, []);
  assert.deepEqual(rejectedContext.callContext.currentQueryContext.effects.claimedShieldedReceives, []);

  console.log('Immediate shielded split: exact 5 -> 2 + 3 values, offer metadata and claims; overspend rejected');
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
