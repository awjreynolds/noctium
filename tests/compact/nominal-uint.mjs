import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/nominal-uint.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const runtime = resolve(runtimePath);
const version = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(version, /^0\.36\.1 \(7fa3a117c/);
assert.equal(JSON.parse(readFileSync(join(runtime, 'package.json'), 'utf8')).version, '0.21.0');

const testDir = dirname(fileURLToPath(import.meta.url));
const experiments = resolve(testDir, '../../build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'nominal-uint-'));
try {
  const generated = join(scratch, 'reference');
  execFileSync(compactc, ['--skip-zk', join(testDir, 'NominalUint.compact'), generated]);

  const rejectedCases = [
    ['mixed-types', 'new type Count = Uint<8>;',
      'pure circuit invalid(x: Amount, y: Count): Amount { return x + y; }',
      /incompatible combination of types Amount and Count/],
    ['implicit-unwrap', '',
      'pure circuit invalid(x: Amount): Uint<8> { return x; }',
      /mismatch between actual return type Amount and declared return type Uint<8>/],
    ['implicit-wrap', '',
      'pure circuit invalid(x: Uint<8>): Amount { return x; }',
      /mismatch between actual return type Uint<8> and declared return type Amount/],
    ['intermediate-width', 'new type Wide = Uint<248>;',
      'pure circuit invalid(x: Wide, y: Wide): Wide { return x + y; }',
      /resulting value might exceed largest representable Uint value/],
    ['mixed-ledger-write',
      'new type Count = Uint<8>; ledger balance: Amount; constructor(x: Amount) { balance = disclose(x); }',
      'circuit invalid(x: Count): [] { balance = disclose(x); return []; }',
      /expected right-hand side of = to have type Amount but received Count/],
    ['implicit-ledger-wrap',
      'ledger balance: Amount; constructor(x: Amount) { balance = disclose(x); }',
      'circuit invalid(x: Uint<8>): [] { balance = disclose(x); return []; }',
      /expected right-hand side of = to have type Amount but received Uint<8>/],
  ];
  for (const [name, extra, circuit, diagnostic] of rejectedCases) {
    const source = join(scratch, name + '.compact');
    writeFileSync(source, ['pragma language_version 0.28;', 'new type Amount = Uint<8>;',
      extra, 'export ' + circuit].join('\n') + '\n');
    const result = spawnSync(compactc, ['--skip-zk', source, join(scratch, name)], { encoding: 'utf8' });
    assert.notEqual(result.status, 0, name);
    assert.match(result.stderr + result.stdout, diagnostic, name);
  }

  const link = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(link), { recursive: true });
  symlinkSync(runtime, link, 'dir');
  const { Contract, pureCircuits } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  assert.equal(pureCircuits.addAmount(1n, 1n), 2n);
  assert.equal(pureCircuits.addAmount(255n, 0n), 255n);
  assert.throws(() => pureCircuits.addAmount(255n, 1n), /greater than 255/);
  assert.equal(pureCircuits.toUnderlying(9n), 9n);
  assert.equal(pureCircuits.toAmount(255n), 255n);
  assert.throws(() => pureCircuits.toAmount(256n), /greater than 255/);
  const compactRuntime = await import(pathToFileURL(join(runtime, 'dist/index.js')).href);
  const contract = new Contract({});
  const wallet = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(
    compactRuntime.createConstructorContext(null, wallet), 19n,
  );
  function invoke(name, state, ...args) {
    const context = compactRuntime.createCircuitContext({
      circuitId: name, contractAddress: compactRuntime.dummyContractAddress(),
      coinPublicKeyOrZswapState: wallet, contractState: state, privateState: null,
    });
    return contract.circuits[name](context, ...args);
  }
  const initial = currentContractState.data;
  assert.equal((await invoke('get', initial)).result, 19n);
  const written = await invoke('setAmount', initial, 41n);
  const afterWrite = written.context.callContext.currentQueryContext.state;
  assert.equal((await invoke('get', afterWrite)).result, 41n);
  const cast = await invoke('setRaw', afterWrite, 255n);
  assert.equal((await invoke('get', cast.context.callContext.currentQueryContext.state)).result, 255n);
  console.log(`Compact ${version} matched nominal UInt arithmetic, narrowing and ledger state cases`);
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
