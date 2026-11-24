import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/nominal-field-records.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/);
const runtimeDirectory = resolve(runtimePath);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'nominal-field-records-'));
try {
  const generated = join(scratch, 'compact');
  const source = join(root, 'tests/compact/NominalFieldRecords.compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');
  const { createCircuitContext, createConstructorContext, dummyContractAddress } = await import(
    pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href,
  );
  const { Contract, ledger } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const contract = new Contract({});
  const wallet = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(createConstructorContext(null, wallet));

  const invoke = async (name, args, state) => {
    const context = createCircuitContext({
      circuitId: name,
      contractAddress: dummyContractAddress(),
      coinPublicKeyOrZswapState: wallet,
      contractState: state,
      privateState: null,
    });
    const call = await contract.circuits[name](context, ...args);
    return [call.result, call.context.callContext.currentQueryContext.state];
  };

  let state = currentContractState.data;
  assert.deepEqual(ledger(state).memo, { amount: 0n });
  assert.equal(ledger(state).memos.size(), 0n);
  assert.deepEqual([...ledger(state).records], []);

  [, state] = await invoke('writeCell', [17n], state);
  const [cellAmount] = await invoke('readCell', [], state);
  assert.equal(cellAmount, 17n);
  assert.deepEqual(ledger(state).memo, { amount: 17n });

  [, state] = await invoke('writeMap', [9n, 42n], state);
  const [mapAmount] = await invoke('readMap', [9n], state);
  assert.equal(mapAmount, 42n);
  assert.deepEqual(ledger(state).memos.lookup(9n), { amount: 42n });

  [, state] = await invoke('pushList', [51n], state);
  const [listAmount] = await invoke('readList', [], state);
  assert.equal(listAmount, 51n);
  assert.deepEqual([...ledger(state).records], [{ amount: 51n }]);

  const validSource = readFileSync(source, 'utf8');
  const rejectedCases = [
    ['wrong-cell-alias',
      'export circuit invalidCell(amount: Count): [] {\n  const exposed = disclose(amount);\n  memo = disclose(Memo { amount: exposed });\n}'],
    ['wrong-map-value-alias',
      'export circuit invalidMapValue(key: Field, amount: Count): [] {\n  const exposed = disclose(amount);\n  memos.insert(disclose(key), disclose(Memo { amount: exposed }));\n}'],
    ['wrong-list-alias',
      'export circuit invalidList(amount: Count): [] {\n  const exposed = disclose(amount);\n  records.pushFront(disclose(Memo { amount: exposed }));\n}'],
  ];
  for (const [name, circuit] of rejectedCases) {
    const wrongSource = join(scratch, `${name}.compact`);
    writeFileSync(wrongSource, `${validSource}\n${circuit}\n`);
    const rejected = spawnSync(compactc, ['--skip-zk', wrongSource, join(scratch, name)], { encoding: 'utf8' });
    assert.notEqual(rejected.status, 0, `${name} unexpectedly compiled`);
    assert.match(rejected.stderr + rejected.stdout, /actual type Count and declared type Amount/, name);
  }

  console.log(JSON.stringify({
    fixture: 'NominalFieldRecords', compact: compilerVersion, runtime: runtimePackage.version,
    cell: { amount: cellAmount.toString() },
    map: { key: '9', amount: mapAmount.toString() },
    list: { head: listAmount.toString() },
    wrongAliasesRejected: ['cell', 'map-value', 'list'],
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
