import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/private-record-stage.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const runtime = resolve(runtimePath);
const version = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(version, /^0\.36\.1 \(7fa3a117c/);
const metadata = JSON.parse(readFileSync(join(runtime, 'package.json')));
assert.equal(metadata.name, '@midnight-ntwrk/compact-runtime');
assert.equal(metadata.version, '0.21.0');

const source = fileURLToPath(new URL('./PrivateRecordStage.compact', import.meta.url));
const experiments = fileURLToPath(new URL('../../build/experiments', import.meta.url));
mkdirSync(experiments, { recursive: true });
const out = mkdtempSync(join(experiments, '575-compact-'));
try {
  execFileSync(compactc, ['--skip-zk', source, out]);
  const runtimeLink = join(out, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtime, runtimeLink, 'dir');
  const { createCircuitContext, createConstructorContext, dummyContractAddress } =
    await import(pathToFileURL(join(runtime, 'dist/index.js')).href);
  const { Contract } = await import(pathToFileURL(join(out, 'contract/index.js')).href);
  const oldReceipt = { amount: 2n, okay: true };
  const newReceipt = { amount: 3n, okay: false };
  const walletKey = '00'.repeat(32);
  async function run(readReceipt) {
    const contract = new Contract({
      readReceipt: ({ privateState }) => [privateState, readReceipt(privateState)],
      stageReceipt: (_, value) => [value, []],
    });
    const { currentContractState } = await contract.initialState(createConstructorContext(oldReceipt, walletKey));
    return contract.circuits.advance(createCircuitContext({
      circuitId: 'advance', contractAddress: dummyContractAddress(),
      coinPublicKeyOrZswapState: walletKey, contractState: currentContractState.data,
      privateState: oldReceipt,
    }), 2n);
  }
  const result = await run(receipt => receipt);
  assert.deepEqual(result.result, [true, 2n]);
  assert.deepEqual(result.context.callContext.currentPrivateState, newReceipt);
  await assert.rejects(() => run(() => oldReceipt), /stale receipt/);
  console.log('Compact reference matched the tentative receipt, public result, and stale read rejection');
} finally {
  rmSync(out, { recursive: true, force: true });
}
