import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectoryArgument] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectoryArgument,
  'usage: node tests/compact/two-parent-qualified-coin-list.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/,
  `expected pinned Compact 0.36.1 compiler, got ${compilerVersion}`);
const runtimeDirectory = resolve(runtimeDirectoryArgument);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/TwoParentQualifiedCoinList.compact');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'two-parent-qualified-coin-list-'));

try {
  const generated = join(scratch, 'compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
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
  const owners = [new Uint8Array(32).fill(1), new Uint8Array(32).fill(2)];
  const buckets = [new Uint8Array(32).fill(5), new Uint8Array(32).fill(6)];
  const missingOwner = new Uint8Array(32).fill(3);
  const missingBucket = new Uint8Array(32).fill(7);
  const domain = new Uint8Array(32).fill(8);
  const paddingNonce = new Uint8Array(32).fill(0xfe);
  const initial = (await contract.initialState(createConstructorContext(null, wallet)))
    .currentContractState.data;
  const contextFor = (entry, contractState) => createCircuitContext({
    circuitId: entry,
    contractAddress: own,
    coinPublicKeyOrZswapState: wallet,
    contractState,
    privateState: null,
  });
  const listAt = (state, owner, bucket) => [
    ...ledger(state).coinLists.lookup(owner).lookup(bucket),
  ];
  const allLists = state => [
    listAt(state, owners[0], buckets[0]),
    listAt(state, owners[0], buckets[1]),
    listAt(state, owners[1], buckets[0]),
    listAt(state, owners[1], buckets[1]),
  ];

  let state = initial;
  for (const owner of owners) {
    const initialized = await contract.circuits.initializeOwner(contextFor('initializeOwner', state), owner);
    state = initialized.context.callContext.currentQueryContext.state;
    for (const bucket of buckets) {
      const initializedBucket = await contract.circuits.initializeBucket(
        contextFor('initializeBucket', state), owner, bucket,
      );
      state = initializedBucket.context.callContext.currentQueryContext.state;
    }
  }
  assert.deepEqual(allLists(state), [[], [], [], []]);

  const push = (context, owner, bucket, nonceByte, value,
                bookingAddress = own, book = true, prefixMint = false) =>
    contract.circuits.pushCoin(
      context,
      owner,
      bucket,
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
  const append = async (ownerIndex, bucketIndex, nonceByte, value, prefixMint = false) => {
    const { context, result } = await push(
      contextFor('pushCoin', state), owners[ownerIndex], buckets[bucketIndex], nonceByte,
      value, own, true, prefixMint,
    );
    const zswap = context.callContext.currentZswapLocalState;
    const outputCount = prefixMint ? 2n : 1n;
    assert.equal(zswap.currentIndex, outputCount);
    assert.equal(zswap.outputs.length, Number(outputCount));
    assert.deepEqual(zswap.outputs.at(-1).coinInfo, result);
    let padding;
    if (prefixMint) {
      const paddingOutput = zswap.outputs[0].coinInfo;
      assert.notDeepEqual(paddingOutput.nonce, result.nonce);
      assert.deepEqual(paddingOutput.nonce, paddingNonce);
      assert.equal(paddingOutput.value, 1n);
      padding = { ...paddingOutput, mt_index: 0n };
    }
    const qualified = { ...result, mt_index: zswap.currentIndex - 1n };
    state = context.callContext.currentQueryContext.state;
    if (prefixMint) assert.deepEqual(ledger(state).paddingSlot, padding);
    return { qualified, padding };
  };

  const { qualified: original } = await append(0, 0, 2, 5);
  const { qualified: sibling } = await append(0, 1, 3, 7);
  const { qualified: otherOwner } = await append(1, 0, 4, 11);
  const { qualified: newest, padding } = await append(0, 0, 5, 13, true);
  assert.equal(newest.mt_index, 1n);
  assert.equal(padding.mt_index, 0n);
  assert.deepEqual(allLists(state), [[newest, original], [sibling], [otherOwner], []]);

  const expected = allLists(state);
  for (const [bookingAddress, book] of [[own, false], [wrongContract, true]]) {
    const context = contextFor('pushCoin', state);
    await assert.rejects(push(context, owners[0], buckets[0], 6, 17, bookingAddress, book),
      /Coin commitment not found/);
    assert.deepEqual(allLists(context.callContext.currentQueryContext.state), expected);
  }

  for (const [owner, bucket] of [
    [owners[0], missingBucket],
    [missingOwner, buckets[0]],
  ]) {
    const context = contextFor('pushCoin', state);
    await assert.rejects(push(context, owner, bucket, 7, 19));
    assert.deepEqual(allLists(context.callContext.currentQueryContext.state), expected);
  }
  console.log('Compact 0.36.1 preserved sibling Lists and assigned index 1 after a same-call mint');
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
