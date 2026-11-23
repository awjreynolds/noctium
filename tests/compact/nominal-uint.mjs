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
    ['list-wrong-nominal-insert', 'new type Count = Uint<8>; ledger amounts: List<Amount>;',
      'circuit invalid(x: Count): [] { amounts.pushFront(disclose(x)); return []; }',
      /expected first argument of pushFront to have type Amount but received Count/],
    ['list-implicit-raw-insert', 'ledger amounts: List<Amount>;',
      'circuit invalid(x: Uint<8>): [] { amounts.pushFront(disclose(x)); return []; }',
      /expected first argument of pushFront to have type Amount but received Uint<8>/],
    ['map-wrong-nominal-key',
      'new type Count = Uint<8>; new type OtherCount = Uint<8>; ledger balances: Map<Count, Amount>;',
      'circuit invalid(key: OtherCount): [] { balances.insert(disclose(key), disclose(0 as Amount)); return []; }',
      /expected first argument of insert to have type Count but received OtherCount/],
    ['map-implicit-raw-key',
      'new type Count = Uint<8>; ledger balances: Map<Count, Amount>;',
      'circuit invalid(key: Uint<8>): [] { balances.insert(disclose(key), disclose(0 as Amount)); return []; }',
      /expected first argument of insert to have type Count but received Uint<8>/],
    ['map-wrong-nominal-value',
      'new type Count = Uint<8>; new type OtherAmount = Uint<8>; ledger balances: Map<Count, Amount>;',
      'circuit invalid(value: OtherAmount): [] { balances.insert(disclose(0 as Count), disclose(value)); return []; }',
      /expected second argument of insert to have type Amount but received OtherAmount/],
    ['map-implicit-raw-value',
      'new type Count = Uint<8>; ledger balances: Map<Count, Amount>;',
      'circuit invalid(value: Uint<8>): [] { balances.insert(disclose(0 as Count), disclose(value)); return []; }',
      /expected second argument of insert to have type Amount but received Uint<8>/],
    ['set-map-wrong-nominal-key',
      'new type Count = Uint<8>; new type OtherCount = Uint<8>; ledger amountSets: Map<Count, Set<Amount>>;',
      'circuit invalid(key: OtherCount): [] { amountSets.insertDefault(disclose(key)); return []; }',
      /expected first argument of insertDefault to have type Count but received OtherCount/],
    ['set-map-implicit-raw-key',
      'new type Count = Uint<8>; ledger amountSets: Map<Count, Set<Amount>>;',
      'circuit invalid(key: Uint<8>): [] { amountSets.insertDefault(disclose(key)); return []; }',
      /expected first argument of insertDefault to have type Count but received Uint<8>/],
    ['nested-set-wrong-nominal-element',
      'new type Count = Uint<8>; new type OtherAmount = Uint<8>; ledger amountSets: Map<Count, Set<Amount>>;',
      'circuit invalid(value: OtherAmount): [] { amountSets.insertDefault(disclose(0 as Count)); amountSets.lookup(disclose(0 as Count)).insert(disclose(value)); return []; }',
      /expected first argument of insert to have type Amount but received OtherAmount/],
    ['nested-set-implicit-raw-element',
      'new type Count = Uint<8>; ledger amountSets: Map<Count, Set<Amount>>;',
      'circuit invalid(value: Uint<8>): [] { amountSets.insertDefault(disclose(0 as Count)); amountSets.lookup(disclose(0 as Count)).insert(disclose(value)); return []; }',
      /expected first argument of insert to have type Amount but received Uint<8>/],
    ['position-amount-wrong-nominal',
      'new type Count = Uint<8>; struct Position { amount: Amount; count: Count; active: Boolean; } ledger position: Position; constructor() { position = Position { amount: 0 as Amount, count: 0 as Count, active: true }; }',
      'circuit invalid(value: Count): [] { position = Position { amount: disclose(value), count: 0 as Count, active: true }; return []; }',
      /mismatch between actual type Count and declared type Amount for field amount of struct/],
    ['position-amount-implicit-raw',
      'new type Count = Uint<8>; struct Position { amount: Amount; count: Count; active: Boolean; } ledger position: Position; constructor() { position = Position { amount: 0 as Amount, count: 0 as Count, active: true }; }',
      'circuit invalid(value: Uint<8>): [] { position = Position { amount: disclose(value), count: 0 as Count, active: true }; return []; }',
      /mismatch between actual type Uint<8> and declared type Amount for field amount of struct/],
    ['position-constructor-wrong-nominal',
      'new type Count = Uint<8>; struct Position { amount: Amount; count: Count; active: Boolean; } ledger position: Position;',
      'constructor(value: Count) { position = Position { amount: disclose(value), count: disclose(value), active: true }; }',
      /mismatch between actual type Count and declared type Amount for field amount of struct/, ''],
    ['position-constructor-implicit-raw',
      'new type Count = Uint<8>; struct Position { amount: Amount; count: Count; active: Boolean; } ledger position: Position;',
      'constructor(value: Uint<8>) { position = Position { amount: disclose(value), count: 0 as Count, active: true }; }',
      /mismatch between actual type Uint<8> and declared type Amount for field amount of struct/, ''],
  ];
  for (const [name, extra, circuit, diagnostic, prefix = 'export '] of rejectedCases) {
    const source = join(scratch, name + '.compact');
    writeFileSync(source, ['pragma language_version 0.28;', 'import CompactStandardLibrary;', 'new type Amount = Uint<8>;',
      extra, prefix + circuit].join('\n') + '\n');
    const result = spawnSync(compactc, ['--skip-zk', source, join(scratch, name)], { encoding: 'utf8' });
    assert.notEqual(result.status, 0, name);
    assert.match(result.stderr + result.stdout, diagnostic, name);
  }

  const link = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(link), { recursive: true });
  symlinkSync(runtime, link, 'dir');
  const { Contract, ledger, pureCircuits } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  assert.equal(pureCircuits.addAmount(1n, 1n), 2n);
  assert.equal(pureCircuits.addAmount(255n, 0n), 255n);
  assert.throws(() => pureCircuits.addAmount(255n, 1n), /greater than 255/);
  assert.equal(pureCircuits.toUnderlying(9n), 9n);
  assert.equal(pureCircuits.toAmount(255n), 255n);
  assert.throws(() => pureCircuits.toAmount(256n), /greater than 255/);
  const compactRuntime = await import(pathToFileURL(join(runtime, 'dist/index.js')).href);
  const contract = new Contract({});
  const wallet = '00'.repeat(32);
  const positionKey = new Uint8Array(32).fill(23);
  const { currentContractState } = await contract.initialState(
    compactRuntime.createConstructorContext(null, wallet), 2n, 19n, positionKey,
  );
  function invoke(name, state, ...args) {
    const context = compactRuntime.createCircuitContext({
      circuitId: name, contractAddress: compactRuntime.dummyContractAddress(),
      coinPublicKeyOrZswapState: wallet, contractState: state, privateState: null,
    });
    return contract.circuits[name](context, ...args);
  }
  const recordKey = new Uint8Array(32).fill(1);
  const { currentContractState: recordState } = await contract.initialState(
    compactRuntime.createConstructorContext(null, wallet), 7n, 19n, recordKey,
  );
  const initializedRecord = { amount: 19n, count: 7n, active: true };
  assert.deepEqual(ledger(recordState.data).position, initializedRecord);
  assert.deepEqual(ledger(recordState.data).positions.lookup(recordKey), initializedRecord);

  const initial = currentContractState.data;
  assert.equal((await invoke('get', initial)).result, 19n);
  assert.equal(ledger(initial).balances.member(2n), true);
  assert.equal(ledger(initial).balances.lookup(2n), 19n);
  assert.deepEqual(ledger(initial).position, { amount: 19n, count: 2n, active: true });
  assert.deepEqual(ledger(initial).positions.lookup(positionKey), { amount: 19n, count: 2n, active: true });
  assert.equal((await invoke('positionAmount', initial)).result, 19n);
  assert.equal((await invoke('mappedPositionAmount', initial, positionKey)).result, 19n);
  const initialListHead = (await invoke('amountHead', initial)).result;
  assert.deepEqual(Object.keys(initialListHead), ['is_some', 'value']);
  assert.equal(initialListHead.is_some, true);
  assert.equal(initialListHead.value, 19n);
  const written = await invoke('setAmount', initial, 41n);
  const afterWrite = written.context.callContext.currentQueryContext.state;
  assert.equal((await invoke('get', afterWrite)).result, 41n);
  const pushedListHead = (await invoke('amountHead', afterWrite)).result;
  assert.equal(pushedListHead.is_some, true);
  assert.equal(pushedListHead.value, 41n);

  const positionWrite = await invoke('writePositionAmount', initial, positionKey, 41n);
  const afterPositionWrite = positionWrite.context.callContext.currentQueryContext.state;
  assert.deepEqual(ledger(afterPositionWrite).position, { amount: 41n, count: 2n, active: true });
  assert.deepEqual(ledger(afterPositionWrite).positions.lookup(positionKey), { amount: 41n, count: 2n, active: true });
  assert.equal((await invoke('positionAmount', afterPositionWrite)).result, 41n);
  assert.equal((await invoke('mappedPositionAmount', afterPositionWrite, positionKey)).result, 41n);

  const positionCast = await invoke('writePositionRaw', afterPositionWrite, positionKey, 255n);
  const afterPositionCast = positionCast.context.callContext.currentQueryContext.state;
  assert.deepEqual(ledger(afterPositionCast).position, { amount: 255n, count: 2n, active: true });
  assert.deepEqual(ledger(afterPositionCast).positions.lookup(positionKey), { amount: 255n, count: 2n, active: true });
  assert.equal((await invoke('positionAmount', afterPositionCast)).result, 255n);
  assert.equal((await invoke('mappedPositionAmount', afterPositionCast, positionKey)).result, 255n);

  const mapWrite = await invoke('writeBalance', initial, 2n, 41n);
  const afterMapWrite = mapWrite.context.callContext.currentQueryContext.state;
  assert.equal((await invoke('balanceMember', afterMapWrite, 2n)).result, true);
  assert.equal((await invoke('balanceLookup', afterMapWrite, 2n)).result, 41n);
  assert.equal(ledger(initial).balances.lookup(2n), 19n);

  const rawMapWrite = await invoke('writeRawBalance', afterMapWrite, 255n, 255n);
  const afterRawMapWrite = rawMapWrite.context.callContext.currentQueryContext.state;
  assert.equal((await invoke('balanceMember', afterRawMapWrite, 255n)).result, true);
  assert.equal((await invoke('balanceLookup', afterRawMapWrite, 255n)).result, 255n);

  const nestedWrite = await invoke('writeNestedBalance', afterRawMapWrite, 2n, 3n, 73n);
  const afterNestedWrite = nestedWrite.context.callContext.currentQueryContext.state;
  assert.equal(ledger(afterNestedWrite).nestedBalances.lookup(2n).member(3n), true);
  assert.equal(ledger(afterNestedWrite).nestedBalances.lookup(2n).lookup(3n), 73n);
  const nestedSibling = await invoke('writeNestedBalance', afterNestedWrite, 2n, 4n, 74n);
  const nestedBalances = ledger(nestedSibling.context.callContext.currentQueryContext.state).nestedBalances;
  assert.equal(nestedBalances.lookup(2n).lookup(3n), 73n);
  assert.equal(nestedBalances.lookup(2n).lookup(4n), 74n);

  const removed = await invoke('removeBalance', afterRawMapWrite, 2n);
  const afterRemove = removed.context.callContext.currentQueryContext.state;
  assert.equal((await invoke('balanceMember', afterRemove, 2n)).result, false);
  assert.equal((await invoke('balanceMember', afterRemove, 255n)).result, true);

  const addedToSets = await invoke('add', initial, 19n, 7n);
  assert.deepEqual(addedToSets.result, [true, true]);
  const removedFromSets = await invoke('remove', addedToSets.context.callContext.currentQueryContext.state, 19n, 7n);
  assert.deepEqual(removedFromSets.result, [false, false]);

  const cast = await invoke('setRaw', afterWrite, 255n);
  const afterCast = cast.context.callContext.currentQueryContext.state;
  assert.equal((await invoke('get', afterCast)).result, 255n);
  const castListHead = (await invoke('amountHead', afterCast)).result;
  assert.equal(castListHead.is_some, true);
  assert.equal(castListHead.value, 255n);
  console.log(`Compact ${version} matched nominal UInt arithmetic, narrowing, ledger state, Position records, List<Amount>, Map<Count, Amount> and Set<Amount> cases`);
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
