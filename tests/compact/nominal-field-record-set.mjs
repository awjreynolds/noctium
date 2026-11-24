import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/nominal-field-record-set.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/);
const runtimeDirectory = resolve(runtimePath);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'nominal-field-record-set-'));
try {
  const generated = join(scratch, 'compact');
  const source = join(root, 'tests/compact/NominalFieldRecordSet.compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');
  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  const { Contract, ledger } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);

  const contract = new Contract({});
  const wallet = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(
    runtime.createConstructorContext(null, wallet),
  );
  const invoke = (state, amount, adding, removing) => contract.circuits.update(
    runtime.createCircuitContext({
      circuitId: 'update',
      contractAddress: runtime.dummyContractAddress(),
      coinPublicKeyOrZswapState: wallet,
      contractState: state,
      privateState: null,
    }), amount, adding, removing,
  );

  const initial = currentContractState.data;
  assert.equal(ledger(initial).members.size(), 0n);
  const first = await invoke(initial, 17n, true, false);
  assert.deepEqual(first.result, [false, true, true]);
  const afterInsert = first.context.callContext.currentQueryContext.state;
  const inserted = ledger(afterInsert).members;
  const key = { amount: 17n };
  assert.equal(inserted.size(), 1n);
  assert.equal(inserted.member(key), true);

  const second = await invoke(afterInsert, 17n, false, true);
  assert.deepEqual(second.result, [true, true, false]);
  const afterRemove = second.context.callContext.currentQueryContext.state;
  assert.equal(ledger(afterRemove).members.size(), 0n);
  assert.equal(ledger(afterRemove).members.member(key), false);

  const validSource = readFileSync(source, 'utf8');
  const wrongSource = join(scratch, 'wrong-key-alias.compact');
  writeFileSync(wrongSource, `${validSource}\nexport circuit wrongKeyAlias(keyAmount: Count): [] {\n  const key = Key { amount: disclose(keyAmount) };\n  members.insert(key);\n  return [];\n}\n`);
  const rejected = spawnSync(compactc, ['--skip-zk', wrongSource, join(scratch, 'wrong-key-alias')], {
    encoding: 'utf8',
  });
  assert.notEqual(rejected.status, 0, 'wrong record Set alias unexpectedly compiled');
  assert.match(rejected.stderr + rejected.stdout, /actual type Count and declared type Amount/);

  console.log(JSON.stringify({
    fixture: 'NominalFieldRecordSet',
    compact: compilerVersion,
    runtime: runtimePackage.version,
    logicalKey: { amount: '17' },
    calls: [[false, true, true], [true, true, false]],
    sizes: ['1', '0'],
    wrongKeyAliasRejected: true,
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
