import assert from 'node:assert/strict';
import {execFileSync} from 'node:child_process';
import {dirname, join, resolve} from 'node:path';
import {fileURLToPath, pathToFileURL} from 'node:url';
import {mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync} from 'node:fs';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node generic-scalar-cell-constructor.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], {encoding: 'utf8'}).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/, `unexpected Compact compiler: ${compilerVersion}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(root, 'tests/compact/GenericScalarCellConstructor.compact');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, {recursive: true});
const scratch = mkdtempSync(join(experiments, 'generic-scalar-cell-constructor-'));

try {
  const generated = join(scratch, 'compiled');
  execFileSync(compactc, ['--skip-zk', source, generated], {encoding: 'utf8'});
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), {recursive: true});
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  assert.equal(runtime.versionString, '0.21.0');
  const {Contract, ledger} = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const contract = new Contract({});
  const walletKey = '00'.repeat(32);
  const initial = await contract.initialState(
    runtime.createConstructorContext(null, walletKey), 5n, true, 42n,
  );
  const state = initial.currentContractState.data;
  const expectedState = (field, flag, count) => ({
    fieldCell_value: BigInt(field),
    flagCell_value: flag,
    countCell_value: BigInt(count),
  });
  const readLedger = state => {
    const current = ledger(state);
    return {
      fieldCell_value: current.fieldCell_value,
      flagCell_value: current.flagCell_value,
      countCell_value: current.countCell_value,
    };
  };
  assert.deepEqual(readLedger(state), expectedState(5, true, 42));

  for (const [circuitId, expected] of [
    ['readField', 5n],
    ['readFlag', true],
    ['readCount', 42n],
  ]) {
    const result = await contract.circuits[circuitId](runtime.createCircuitContext({
      circuitId, contractAddress: runtime.dummyContractAddress(),
      coinPublicKeyOrZswapState: walletKey, contractState: state, privateState: null,
    }));
    assert.deepEqual(result.result, expected);
  }

  const run = async (circuitId, state, ...args) => {
    const result = await contract.circuits[circuitId](runtime.createCircuitContext({
      circuitId, contractAddress: runtime.dummyContractAddress(),
      coinPublicKeyOrZswapState: walletKey, contractState: state, privateState: null,
    }), ...args);
    return [result.result, result.context.callContext.currentQueryContext.state];
  };

  let currentState = state;
  for (const [circuitId, next, expected] of [
    ['updateField', 8n, 5n],
    ['updateFlag', false, true],
    ['updateCount', 65_535n, 42n],
  ]) {
    const [result, after] = await run(circuitId, currentState, false, next);
    assert.equal(result, expected);
    assert.deepEqual(readLedger(after), expectedState(5, true, 42));
    currentState = after;
  }

  for (const [circuitId, next, expected, expectedStateAfter] of [
    ['updateField', 8n, 8n, expectedState(8, true, 42)],
    ['updateFlag', false, false, expectedState(8, false, 42)],
    ['updateCount', 65_535n, 65_535n, expectedState(8, false, 65_535)],
  ]) {
    const [result, after] = await run(circuitId, currentState, true, next);
    assert.equal(result, expected);
    assert.deepEqual(readLedger(after), expectedStateAfter);
    currentState = after;
  }

  await assert.rejects(
    () => run('updateCount', currentState, true, 65_536n),
  );
  for (const [circuitId, expected] of [
    ['readField', 8n],
    ['readFlag', false],
    ['readCount', 65_535n],
  ]) {
    const result = await contract.circuits[circuitId](runtime.createCircuitContext({
      circuitId, contractAddress: runtime.dummyContractAddress(),
      coinPublicKeyOrZswapState: walletKey,
      contractState: currentState,
      privateState: null,
    }));
    assert.deepEqual(result.result, expected);
  }

  console.log(`Compact ${compilerVersion} initialized and updated specialized Field, Boolean and Uint<16> cells; inactive writes preserved values and 65536 was rejected`);
} finally {
  rmSync(scratch, {recursive: true, force: true});
}
