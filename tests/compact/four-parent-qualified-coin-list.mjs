import assert from 'node:assert/strict';
import { execFileSync, spawn } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectoryArgument] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectoryArgument,
  'usage: node tests/compact/four-parent-qualified-coin-list.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/,
  `expected pinned Compact 0.36.1 compiler, got ${compilerVersion}`);
const runtimeDirectory = resolve(runtimeDirectoryArgument);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/FourParentQualifiedCoinList.compact');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'four-parent-qualified-coin-list-'));

async function compileWithProcessGroup(command, args, timeoutMs) {
  return new Promise(resolveResult => {
    const child = spawn(command, args, {
      detached: true,
      stdio: ['ignore', 'pipe', 'pipe'],
    });
    let stdout = '';
    let stderr = '';
    let timedOut = false;
    let spawnError;
    child.stdout.setEncoding('utf8');
    child.stderr.setEncoding('utf8');
    child.stdout.on('data', chunk => { stdout += chunk; });
    child.stderr.on('data', chunk => { stderr += chunk; });
    child.on('error', error => { spawnError = error; });
    const timer = setTimeout(() => {
      timedOut = true;
      try {
        process.kill(-child.pid, 'SIGTERM');
      } catch {}
      const forceKill = setTimeout(() => {
        try {
          process.kill(-child.pid, 'SIGKILL');
        } catch {}
      }, 5_000);
      forceKill.unref();
    }, timeoutMs);
    child.on('close', (status, signal) => {
      clearTimeout(timer);
      resolveResult({
        status,
        signal,
        stdout,
        stderr,
        error: spawnError ?? (timedOut ? new Error(`process group timed out after ${timeoutMs} ms`) : undefined),
      });
    });
  });
}

try {
  const generated = join(scratch, 'compact');
  const compile = await compileWithProcessGroup(compactc, ['--skip-zk', source, generated], 180_000);
  assert.equal(compile.error, undefined,
    `pinned Compact compilation failed to start or exceeded 180 seconds: ${compile.error}\n${compile.stderr || compile.stdout}`);
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
  const explicitRecipient = '0a'.repeat(32);
  const wrongRecipient = '0b'.repeat(32);
  const domain = new Uint8Array(32).fill(8);
  const paddingNonce = new Uint8Array(32).fill(0xfe);
  const selected = [1, 2, 3, 4].map(byte => new Uint8Array(32).fill(byte));
  const siblings = [
    [1, 2, 3, 6],
    [1, 2, 7, 4],
  ].map(path => path.map(byte => new Uint8Array(32).fill(byte)));
  const absentPath = [1, 2, 3, 11].map(byte => new Uint8Array(32).fill(byte));
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
  const listAt = (state, path) => {
    const [first, second, third, fourth] = path;
    return [...ledger(state).coinLists.lookup(first).lookup(second).lookup(third).lookup(fourth)];
  };
  const allLists = state => paths.map(path => listAt(state, path));

  const initialized = await contract.circuits.initializePaths(
    contextFor('initializePaths', initial),
    ...selected,
    siblings[1][2],
    siblings[0][3],
  );
  let state = initialized.context.callContext.currentQueryContext.state;
  assert.deepEqual(allLists(state), [[], [], []]);

  const push = (context, path, nonceByte, value, options = {}) => {
    const {
      book = true,
      bookingAddress = own,
      recipientAddress = own,
      prefixMint = false,
    } = options;
    const addressBytes = address => Uint8Array.from(Buffer.from(address, 'hex'));
    return contract.circuits.pushCoin(
      context,
      ...path,
      domain,
      new Uint8Array(32).fill(nonceByte),
      BigInt(value),
      book,
      true,
      addressBytes(bookingAddress),
      true,
      addressBytes(recipientAddress),
      prefixMint,
      paddingNonce,
      1n,
    );
  };
  const append = async (path, nonceByte, value, options = {}) => {
    const { context, result } = await push(contextFor('pushCoin', state), path,
      nonceByte, value, options);
    const zswap = context.callContext.currentZswapLocalState;
    const outputCount = options.prefixMint ? 2n : 1n;
    assert.equal(zswap.currentIndex, outputCount);
    assert.equal(zswap.outputs.length, Number(outputCount));
    assert.deepEqual(zswap.outputs.at(-1).coinInfo, result);
    let padding;
    if (options.prefixMint) {
      const paddingOutput = zswap.outputs[0].coinInfo;
      assert.notDeepEqual(paddingOutput.nonce, result.nonce);
      assert.deepEqual(paddingOutput.nonce, paddingNonce);
      assert.equal(paddingOutput.value, 1n);
      padding = { ...paddingOutput, mt_index: 0n };
    }
    const qualified = { ...result, mt_index: zswap.currentIndex - 1n };
    state = context.callContext.currentQueryContext.state;
    if (options.prefixMint) assert.deepEqual(ledger(state).paddingSlot, padding);
    return qualified;
  };

  const original = await append(selected, 2, 5);
  const siblingFourth = await append(siblings[0], 3, 7);
  const siblingThird = await append(siblings[1], 4, 11);
  const beforeMainPush = allLists(state);
  assert.deepEqual(beforeMainPush, [[original], [siblingFourth], [siblingThird]]);

  const newest = await append(selected, 5, 13, {
    bookingAddress: explicitRecipient,
    recipientAddress: explicitRecipient,
    prefixMint: true,
  });
  assert.equal(newest.mt_index, 1n);
  assert.deepEqual(allLists(state), [[newest, original], [siblingFourth], [siblingThird]]);

  const expected = allLists(state);
  for (const options of [
    { book: false },
    { bookingAddress: wrongRecipient },
    { bookingAddress: own, recipientAddress: wrongRecipient },
  ]) {
    const context = contextFor('pushCoin', state);
    await assert.rejects(push(context, selected, 6, 17, options), /Coin commitment not found/);
    assert.deepEqual(allLists(context.callContext.currentQueryContext.state), expected);
  }

  const absent = contextFor('pushCoin', state);
  await assert.rejects(push(absent, absentPath, 7, 19));
  assert.deepEqual(allLists(absent.callContext.currentQueryContext.state), expected);
  const absentParents = ledger(absent.callContext.currentQueryContext.state).coinLists
    .lookup(selected[0]).lookup(selected[1]).lookup(selected[2]);
  assert.equal(absentParents.member(absentPath[3]), false);

  console.log('Compact 0.36.1 preserved four-parent List order, booking indices, and sibling paths');
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
