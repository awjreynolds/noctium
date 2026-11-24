import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/nested-nominal-field-record-set.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/);
const runtimeDirectory = resolve(runtimePath);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'nested-nominal-field-record-set-'));
try {
  const generated = join(scratch, 'compact');
  const source = join(root, 'tests/compact/NestedNominalFieldRecordSet.compact');
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
  const owner = new Uint8Array(32).fill(7);
  const missedOwner = new Uint8Array(32).fill(9);
  const amount = 17n;
  const { currentContractState } = await contract.initialState(
    createConstructorContext(null, wallet),
  );
  const emptyState = currentContractState.data;
  const { result: initResult, context: initContext } = await contract.circuits.initBucket(
    createCircuitContext({
      circuitId: 'initBucket', contractAddress: dummyContractAddress(),
      coinPublicKeyOrZswapState: wallet, contractState: emptyState, privateState: null,
    }), owner,
  );
  assert.deepEqual(initResult, []);
  const initial = initContext.callContext.currentQueryContext.state;
  const run = async (state, adding, removing, selectedOwner = owner) => {
    const { result, context } = await contract.circuits.update(createCircuitContext({
      circuitId: 'update', contractAddress: dummyContractAddress(),
      coinPublicKeyOrZswapState: wallet, contractState: state, privateState: null,
    }), selectedOwner, amount, adding, removing);
    return [result, context.callContext.currentQueryContext.state];
  };

  assert.equal(ledger(initial).buckets.lookup(owner).size(), 0n);
  const [added, afterAdd] = await run(initial, true, false);
  assert.deepEqual(added, [false, true, true]);
  assert.equal(ledger(afterAdd).buckets.lookup(owner).member({ amount }), true);
  assert.equal(ledger(afterAdd).buckets.lookup(owner).size(), 1n);

  const [removed, afterRemove] = await run(afterAdd, false, true);
  assert.deepEqual(removed, [true, true, false]);
  assert.equal(ledger(afterRemove).buckets.lookup(owner).member({ amount }), false);
  assert.equal(ledger(afterRemove).buckets.lookup(owner).size(), 0n);

  await assert.rejects(async () => {
    await run(initial, false, false, missedOwner);
  });

  const invalidSource = join(scratch, 'wrong-alias.compact');
  writeFileSync(invalidSource, readFileSync(source, 'utf8') + `
export circuit wrongAlias(owner: Bytes<32>, value: Count): Boolean {
  const key = Key { amount: disclose(value) };
  return buckets.lookup(disclose(owner)).member(key);
}
`);
  const rejected = spawnSync(compactc, ['--skip-zk', invalidSource, join(scratch, 'wrong-alias')],
    { encoding: 'utf8' });
  assert.notEqual(rejected.status, 0, 'wrong nominal record key alias unexpectedly compiled');
  assert.match(rejected.stderr + rejected.stdout, /actual type Count and declared type Amount/);

  console.log(JSON.stringify({
    fixture: 'NestedNominalFieldRecordSet', compact: compilerVersion, runtime: runtimePackage.version,
    initializedOwner: ledger(initial).buckets.lookup(owner).size() === 0n,
    outputs: { add: added, remove: removed },
    sizes: { afterAdd: ledger(afterAdd).buckets.lookup(owner).size().toString(),
      afterRemove: ledger(afterRemove).buckets.lookup(owner).size().toString() },
    missedOwnerRejected: true,
    wrongAliasRejected: true,
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
