import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/nominal-field-record-map.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/);
const runtimeDirectory = resolve(runtimePath);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'nominal-field-record-map-'));
try {
  const generated = join(scratch, 'compact');
  const source = join(root, 'tests/compact/NominalFieldRecordMap.compact');
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
  const { result, context } = await contract.circuits.roundTrip(createCircuitContext({
    circuitId: 'roundTrip', contractAddress: dummyContractAddress(),
    coinPublicKeyOrZswapState: wallet, contractState: currentContractState.data, privateState: null,
  }), 17n, 42n);
  assert.deepEqual(result, [true, 42n]);
  const records = ledger(context.callContext.currentQueryContext.state).records;
  assert.equal(records.size(), 1n);
  assert.equal(records.member({ amount: 17n }), true);
  assert.deepEqual(records.lookup({ amount: 17n }), { amount: 42n });

  const validSource = readFileSync(source, 'utf8');
  const rejectedCases = [
    ['wrong-key-alias', 'const key = Key { amount: disclose(keyAmount) };',
      'export circuit invalidKey(keyAmount: Count): [] {\n  const key = Key { amount: disclose(keyAmount) };\n  return [];\n}',
      /actual type Count and declared type Amount/],
    ['wrong-value-alias', 'const memo = Memo { amount: disclose(memoAmount) };',
      'export circuit invalidMemo(memoAmount: Count): [] {\n  const memo = Memo { amount: disclose(memoAmount) };\n  return [];\n}',
      /actual type Count and declared type Amount/],
  ];
  for (const [name, marker, circuit, diagnostic] of rejectedCases) {
    const wrongSource = join(scratch, `${name}.compact`);
    assert.ok(validSource.includes(marker), `fixture marker missing: ${marker}`);
    writeFileSync(wrongSource, validSource + `\n${circuit}\n`);
    const rejected = spawnSync(compactc, ['--skip-zk', wrongSource, join(scratch, name)], { encoding: 'utf8' });
    assert.notEqual(rejected.status, 0, `${name} unexpectedly compiled`);
    assert.match(rejected.stderr + rejected.stdout, diagnostic, name);
  }

  console.log(JSON.stringify({
    fixture: 'NominalFieldRecordMap', compact: compilerVersion, runtime: runtimePackage.version,
    outputs: { found: result[0], amount: result[1].toString() },
    remainingEntries: records.size().toString(),
    matching: { member: true, storedAmount: '42' }, wrongKeyAliasRejected: true,
    wrongRecordValueAliasRejected: true,
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
