import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/unshielded-mint-recipient.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/, `unexpected Compact compiler: ${compilerVersion}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(root, 'tests/compact/UnshieldedMintRecipient.compact');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'unshielded-mint-recipient-'));

try {
  const generated = join(scratch, 'compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  const { Contract } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const contract = new Contract({});
  const wallet = '00'.repeat(32);
  const own = '09'.repeat(32);
  const domain = Uint8Array.from({ length: 32 }, (_, index) => index + 1);
  const amount = 7n;
  const { currentContractState } = await contract.initialState(
    runtime.createConstructorContext(null, wallet),
  );

  let derivedColor;
  for (const [enabled, isContract, recipientByte, credited] of [
    [true, true, 9, true], [true, true, 23, false], [true, false, 9, false],
    [false, true, 9, false],
  ]) {
    const recipient = new Uint8Array(32).fill(recipientByte);
    const context = runtime.createCircuitContext({
      circuitId: 'mint', contractAddress: own, coinPublicKeyOrZswapState: wallet,
      contractState: currentContractState.data, privateState: null,
    });
    const { result, context: after } = await contract.circuits.mint(
      context, domain, amount, isContract, recipient, enabled,
    );
    const effects = after.callContext.currentQueryContext.effects;
    const color = Buffer.from(result).toString('hex');
    if (!enabled) {
      assert.equal(color, '00'.repeat(32));
      assert.deepEqual([...effects.unshieldedMints], []);
      assert.deepEqual([...effects.unshieldedInputs], []);
      assert.deepEqual([...effects.unshieldedOutputs], []);
      assert.deepEqual([...effects.claimedUnshieldedSpends], []);
      continue;
    }
    derivedColor ??= color;
    assert.equal(color, derivedColor, 'recipient selection does not change the token color');
    const token = { tag: 'unshielded', raw: color };
    const address = Buffer.from(recipient).toString('hex');
    const target = { tag: isContract ? 'contract' : 'user', address };

    assert.deepEqual([...effects.unshieldedMints], [[Buffer.from(domain).toString('hex'), amount]]);
    assert.deepEqual([...effects.unshieldedInputs], credited ? [[token, amount]] : []);
    assert.deepEqual([...effects.unshieldedOutputs], []);
    assert.deepEqual([...effects.claimedUnshieldedSpends], [[[token, target], amount]]);
  }
  console.log(JSON.stringify({
    fixture: 'unshielded-mint-recipient', derivedColor,
    cases: ['contract-self', 'contract-other', 'user-same-bytes', 'inactive'],
    exactMintSpend: true, selfOnlyCredit: true, outputs: 0,
  }));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
