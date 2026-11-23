import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectoryArgument] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectoryArgument,
  'usage: node tests/compact/five-parent-qualified-coin-set.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/,
  `expected pinned Compact 0.36.1 compiler, got ${compilerVersion}`);
const runtimeDirectory = resolve(runtimeDirectoryArgument);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/DeepQualifiedCoinSet.compact');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'five-parent-qualified-coin-set-'));

try {
  const generated = join(scratch, 'compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], {
    encoding: 'utf8',
    timeout: 180_000,
  });
  assert.equal(compile.error, undefined,
    `pinned Compact compilation failed to start or exceeded 180 seconds: ${compile.error}`);
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');
  const runtimeUrl = pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href;
  const contractUrl = pathToFileURL(join(generated, 'contract/index.js')).href;
  const { createCircuitContext, createConstructorContext } = await import(runtimeUrl);
  const { Contract, ledger } = await import(contractUrl);

  const contract = new Contract({});
  const wallet = '00'.repeat(32);
  const own = '09'.repeat(32);
  const wrongContract = '0a'.repeat(32);
  const domain = new Uint8Array(32).fill(8);
  const paddingNonce = new Uint8Array(32).fill(0xfe);
  const selected = [1, 2, 3, 4, 5].map(byte => new Uint8Array(32).fill(byte));
  const siblings = [
    [1, 2, 3, 4, 6],
    [1, 2, 3, 7, 5],
    [1, 2, 8, 4, 5],
    [1, 9, 3, 4, 5],
    [10, 2, 3, 4, 5],
  ].map(path => path.map(byte => new Uint8Array(32).fill(byte)));
  const absentPath = [1, 2, 3, 4, 11].map(byte => new Uint8Array(32).fill(byte));
  const paths = [selected, ...siblings];
  const initial = (await contract.initialState(createConstructorContext(null, wallet)))
    .currentContractState.data;
  const contextFor = (entry, contractState) => createCircuitContext({
    circuitId: entry,
    contractAddress: own,
    coinPublicKeyOrZswapState: wallet,
    contractState,
    privateState: null,
  });
  const setAt = (state, path) => {
    const [first, second, third, fourth, fifth] = path;
    return ledger(state).deepSets.lookup(first).lookup(second).lookup(third)
      .lookup(fourth).lookup(fifth);
  };
  const compareBytes = (left, right) => Buffer.compare(left, right);
  const compareQualified = (left, right) =>
    compareBytes(left.nonce, right.nonce)
    || compareBytes(left.color, right.color)
    || (left.value < right.value ? -1 : left.value > right.value ? 1 : 0)
    || (left.mt_index < right.mt_index ? -1 : left.mt_index > right.mt_index ? 1 : 0);
  const sortedSet = (state, path) => [...setAt(state, path)].sort(compareQualified);
  const allSets = state => paths.map(path => sortedSet(state, path));

  let state = initial;
  for (const path of paths) {
    const { context } = await contract.circuits.initializePath(contextFor('initializePath', state), ...path);
    state = context.callContext.currentQueryContext.state;
  }
  assert.deepEqual(allSets(state), [[], [], [], [], [], []]);

  const insert = (context, path, nonceByte, value, options = {}) => {
    const {
      book = true,
      bookingAddress = own,
      prefixMint = false,
    } = options;
    return contract.circuits.insertBookedCoin(
      context,
      ...path,
      domain,
      new Uint8Array(32).fill(nonceByte),
      BigInt(value),
      book,
      true,
      Uint8Array.from(Buffer.from(bookingAddress, 'hex')),
      prefixMint,
      paddingNonce,
      1n,
    );
  };
  const seed = async (pathIndex, nonceByte, value) => {
    const { context, result } = await insert(
      contextFor('insertBookedCoin', state), paths[pathIndex], nonceByte, value,
    );
    const query = context.callContext.currentQueryContext;
    const zswap = context.callContext.currentZswapLocalState;
    assert.equal(zswap.currentIndex, 1n);
    assert.equal(zswap.outputs.length, 1);
    assert.deepEqual(zswap.outputs[0].coinInfo, result);
    const qualified = { ...result, mt_index: 0n };
    state = query.state;
    assert.deepEqual(sortedSet(state, paths[pathIndex]), [qualified]);
    return qualified;
  };

  const seeded = [];
  for (let index = 0; index < paths.length; index += 1) {
    seeded.push(await seed(index, 20 + index, 5 + index));
  }
  const beforeMainInsert = allSets(state);
  assert.deepEqual(beforeMainInsert, seeded.map(coin => [coin]));

  const mainCall = await insert(
    contextFor('insertBookedCoin', state), selected, 40, 13, { prefixMint: true },
  );
  const { context: mainContext, result } = mainCall;
  const zswap = mainContext.callContext.currentZswapLocalState;
  const query = mainContext.callContext.currentQueryContext;
  assert.equal(zswap.currentIndex, 2n);
  assert.equal(zswap.outputs.length, 2);
  assert.deepEqual(zswap.outputs[1].coinInfo, result);
  assert.deepEqual(zswap.outputs[0].coinInfo.nonce, paddingNonce);
  assert.equal(zswap.outputs[0].coinInfo.value, 1n);
  assert.deepEqual(ledger(query.state).paddingSlot, { ...zswap.outputs[0].coinInfo, mt_index: 0n });
  const selectedBooked = { ...result, mt_index: 1n };
  state = query.state;
  assert.deepEqual(allSets(state), [[seeded[0], selectedBooked], ...seeded.slice(1).map(coin => [coin])]
    .map(coins => [...coins].sort(compareQualified)));
  assert.equal(setAt(state, selected).member(selectedBooked), true);
  assert.equal(setAt(state, selected).member({ ...result, mt_index: 0n }), false);

  const expectedAfterInsert = allSets(state);
  for (const options of [
    { book: false },
    { book: true, bookingAddress: wrongContract },
  ]) {
    const failed = contextFor('insertBookedCoin', state);
    await assert.rejects(insert(failed, selected, 50, 17, options), /Coin commitment not found/);
    assert.deepEqual(allSets(failed.callContext.currentQueryContext.state), expectedAfterInsert);
  }

  const absent = contextFor('insertBookedCoin', state);
  await assert.rejects(
    insert(absent, absentPath, 51, 19),
    /invalid operation for type: attempted to ins/,
  );
  assert.deepEqual(allSets(absent.callContext.currentQueryContext.state), expectedAfterInsert);
  assert.equal(ledger(absent.callContext.currentQueryContext.state).deepSets
    .lookup(selected[0]).lookup(selected[1]).lookup(selected[2]).lookup(selected[3])
    .member(absentPath[4]), false);
  console.log('Compact 0.36.1 preserved five-level sibling Sets and stored booked index 1');
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
