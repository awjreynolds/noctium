import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/bounded-uint-arithmetic.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const runtimeDirectory = resolve(runtimePath);
const version = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(version, /^0\.36\.1 \(7fa3a117c/);
assert.equal(JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8')).version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'uint-arithmetic-'));
try {
  const generated = join(scratch, 'compact');
  const source = join(root, 'tests/compact/BoundedUintArithmetic.compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, compile.stderr || compile.stdout);

  const sourceText = readFileSync(source, 'utf8');
  for (const [operation, acceptedBound, rejectedBound] of [['sum', 511, 510], ['product', 65026, 65025]]) {
    const type = `Uint<0..${acceptedBound}>`;
    assert.ok(sourceText.includes(type));
    const narrowerSource = join(scratch, `${operation}.compact`);
    writeFileSync(narrowerSource, sourceText.replace(type, `Uint<0..${rejectedBound}>`));
    const rejected = spawnSync(compactc, ['--skip-zk', narrowerSource, join(scratch, operation)],
      { encoding: 'utf8' });
    assert.notEqual(rejected.status, 0, `Uint<0..${rejectedBound}> must reject the Uint<8> ${operation}`);
    assert.ok((rejected.stderr + rejected.stdout).includes(`actual return type ${type}`),
      rejected.stderr || rejected.stdout);
  }

  for (const [fixture, diagnostic] of [
    ['BoundedUintDeclaredZeroTooNarrow.compact', /actual return type Uint<0\.\.511>.*declared return type Uint<8>/s],
    ['BoundedUintMaxAddBitRejected.compact', /resulting value might exceed largest representable Uint value/],
  ]) {
    const rejected = spawnSync(compactc, ['--skip-zk', join(root, 'tests/compact', fixture),
      join(scratch, fixture.replace(/\.compact$/, ''))], { encoding: 'utf8' });
    assert.notEqual(rejected.status, 0, `${fixture} must be rejected`);
    assert.match(rejected.stderr + rejected.stdout, diagnostic);
  }

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');
  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  const { Contract } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const contract = new Contract({});
  const wallet = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(
    runtime.createConstructorContext(null, wallet),
  );
  const context = (circuitId) => runtime.createCircuitContext({
    circuitId, contractAddress: runtime.dummyContractAddress(),
    coinPublicKeyOrZswapState: wallet, contractState: currentContractState.data,
    privateState: null,
  });

  assert.equal((await contract.circuits.add8(context('add8'), 255n, 255n)).result, 510n);
  assert.equal((await contract.circuits.multiply8(context('multiply8'), 255n, 255n)).result, 65_025n);
  assert.equal((await contract.circuits.subtract8(context('subtract8'), 255n, 1n)).result, 254n);
  assert.equal((await contract.circuits.subtract8(context('subtract8'), 255n, 0n)).result, 255n);
  await assert.rejects(contract.circuits.subtract8(context('subtract8'), 0n, 1n));

  assert.equal((await contract.circuits.addZeroLiteral(context('addZeroLiteral'), 255n)).result, 255n);
  assert.equal((await contract.circuits.addZeroRange(context('addZeroRange'), 255n, 0n)).result, 255n);
  const uint248Max = (1n << 248n) - 1n;
  assert.equal((await contract.circuits.multiplyMaxByBit(context('multiplyMaxByBit'), uint248Max, 1n)).result,
    uint248Max);
  assert.equal((await contract.circuits.addMaxToZero(context('addMaxToZero'), uint248Max, 0n)).result,
    uint248Max);
  assert.equal((await contract.circuits.addSmall(context('addSmall'), 255n, 255n)).result, 510n);
  console.log(`Compact ${version} matched ordinary Uint bounds, zero, max-width, alias, and rejection cases`);
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
