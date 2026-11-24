import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/nested-nominal-field-scalar-map-values.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/);
const runtimeDirectory = resolve(runtimePath);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'nested-nominal-field-scalar-map-values-'));
try {
  const generated = join(scratch, 'compact');
  const source = join(root, 'tests/compact/NestedNominalFieldScalarMapValues.compact');
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
  assert.equal(ledger(currentContractState.data).holdings.size(), 0n);

  const { result, context } = await contract.circuits.writeHolding(createCircuitContext({
    circuitId: 'writeHolding', contractAddress: dummyContractAddress(),
    coinPublicKeyOrZswapState: wallet, contractState: currentContractState.data, privateState: null,
  }), true, 11n, 29n, 73n);
  assert.deepEqual(result, [73n, true]);
  const holdings = ledger(context.callContext.currentQueryContext.state).holdings;
  assert.equal(holdings.size(), 1n);
  assert.equal(holdings.member(11n), true);
  assert.equal(holdings.lookup(11n).size(), 0n);
  assert.equal(holdings.lookup(11n).member(29n), false);

  const validSource = readFileSync(source, 'utf8');
  const rejectedCases = [
    ['wrong-nominal-value-alias',
      'export circuit invalidValue(owner: OwnerId, asset: AssetId, amount: Count): [] {\n' +
      '  holdings.lookup(disclose(owner)).insert(disclose(asset), disclose(amount));\n' +
      '  return [];\n}',
      /expected second argument of insert to have type Amount but received Count/],
    ['raw-field-value',
      'export circuit invalidValue(owner: OwnerId, asset: AssetId, amount: Field): [] {\n' +
      '  holdings.lookup(disclose(owner)).insert(disclose(asset), disclose(amount));\n' +
      '  return [];\n}',
      /expected second argument of insert to have type Amount but received Field/],
  ];
  for (const [name, circuit, diagnostic] of rejectedCases) {
    const wrongSource = join(scratch, `${name}.compact`);
    writeFileSync(wrongSource, validSource + `\n${circuit}\n`);
    const rejected = spawnSync(compactc, ['--skip-zk', wrongSource, join(scratch, name)], { encoding: 'utf8' });
    assert.notEqual(rejected.status, 0, `${name} unexpectedly compiled`);
    assert.match(rejected.stderr + rejected.stdout, diagnostic, name);
  }

  console.log(JSON.stringify({
    fixture: 'NestedNominalFieldScalarMapValues', compact: compilerVersion, runtime: runtimePackage.version,
    inputs: { owner: '11', asset: '29', amount: '73', enabled: true },
    outputs: { stored: result[0].toString(), exists: result[1] },
    retainedOwners: holdings.size().toString(), innerEntries: holdings.lookup(11n).size().toString(),
    wrongNominalValueAliasRejected: true, rawFieldValueRejected: true,
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
