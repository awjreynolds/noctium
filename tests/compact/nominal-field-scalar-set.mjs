import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/nominal-field-scalar-set.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/);
const runtimeDirectory = resolve(runtimePath);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'nominal-field-scalar-set-'));
try {
  const source = join(root, 'tests/compact/NominalFieldScalarSet.compact');
  const generated = join(scratch, 'compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');
  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  const { Contract, ledger } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const contract = new Contract({});
  const wallet = '00'.repeat(32);
  const initial = await contract.initialState(
    runtime.createConstructorContext(null, wallet), 17n, 19n, true,
  );
  const constructorState = ledger(initial.currentContractState.data).constructorMembers;
  assert.equal(constructorState.size(), 2n);
  assert.equal(constructorState.member(17n), true);
  assert.equal(constructorState.member(19n), true);

  const invoke = (state, adding, removing) => contract.circuits.update(
    runtime.createCircuitContext({
      circuitId: 'update',
      contractAddress: runtime.dummyContractAddress(),
      coinPublicKeyOrZswapState: wallet,
      contractState: state,
      privateState: null,
    }), 17n, 19n, adding, removing,
  );
  const first = await invoke(initial.currentContractState.data, true, false);
  assert.deepEqual(first.result, [false, true, false, false, true, true, true, true]);
  const afterInsert = first.context.callContext.currentQueryContext.state;
  const inserted = ledger(afterInsert).members;
  assert.equal(inserted.size(), 2n);
  assert.equal(inserted.member(17n), true);
  assert.equal(inserted.member(19n), true);
  assert.equal(ledger(afterInsert).plain.size(), 0n);

  const second = await invoke(afterInsert, false, true);
  assert.deepEqual(second.result, [false, true, false, true, true, true, false, false]);
  const afterRemove = second.context.callContext.currentQueryContext.state;
  assert.equal(ledger(afterRemove).members.size(), 0n);
  assert.equal(ledger(afterRemove).plain.size(), 0n);

  const validSource = readFileSync(source, 'utf8');
  const compileRejected = (name, body, pattern) => {
    const invalidSource = join(scratch, `${name}.compact`);
    const invalidOutput = join(scratch, name);
    writeFileSync(invalidSource, body);
    const result = spawnSync(compactc, ['--skip-zk', invalidSource, invalidOutput], {
      encoding: 'utf8',
    });
    assert.notEqual(result.status, 0, `${name} unexpectedly compiled`);
    assert.match(result.stderr + result.stdout, pattern);
  };
  compileRejected('wrong-update-alias', `${validSource}\nexport circuit wrongAlias(key: Count): [] {\n  members.insert(disclose(key));\n  return [];\n}\n`,
    /expected first argument of insert to have type Amount but received Count/);
  compileRejected('wrong-constructor-alias',
    validSource.replace('constructor(seed: Amount, raw: Field', 'constructor(seed: Count, raw: Field'),
    /expected first argument of insert to have type Amount but received Count/);
  compileRejected('raw-guarded-constructor-key',
    validSource.replace('constructorMembers.insert(disclose(raw as Amount));',
      'constructorMembers.insert(disclose(raw));'),
    /expected first argument of insert to have type Amount but received Field/);

  console.log(JSON.stringify({
    fixture: 'NominalFieldScalarSet',
    compact: compilerVersion,
    runtime: runtimePackage.version,
    firstOutputs: first.result,
    keysAfterInsert: ['17', '19'],
    secondOutputs: second.result,
    keysAfterRemove: '0',
    wrongUpdateAliasRejected: true,
    wrongConstructorAliasRejected: true,
    rawGuardedConstructorKeyRejected: true,
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
