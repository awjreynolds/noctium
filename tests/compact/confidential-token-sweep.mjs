import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { execFileSync } from 'node:child_process';
import {
  existsSync,
  lstatSync,
  mkdirSync,
  readFileSync,
  realpathSync,
  symlinkSync,
} from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectory, openZeppelinRoot, outputOrRoute, routeArgument] = process.argv.slice(2);
const routeAsFourthArgument = routeArgument === undefined && ['sweep', 'transfer'].includes(outputOrRoute);
const outputArgument = routeAsFourthArgument ? undefined : outputOrRoute;
const route = routeArgument ?? (routeAsFourthArgument ? outputOrRoute : 'sweep');
assert.ok(compactc && runtimeDirectory && openZeppelinRoot,
  'usage: node tests/compact/confidential-token-sweep.mjs <compactc-0.36.1> <compact-runtime-0.21.0> <openzeppelin-contracts-compact-root> [compiled-output] [sweep|transfer]');
assert.ok(['sweep', 'transfer'].includes(route), `unsupported route ${route}`);

const expectedCompactCommit = '7fa3a117c5e7efe9d2c51da04263e5f0b3509144';
const expectedOpenZeppelinCommit = 'f85f1a23685c6bbedfc8c2589ae3aa128aff7c46';
const expectedWrapperHash = '4f30d84cf9567529ca15cade71f22cab08512a6371b6277655352943efa836f9';
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c /,
  `expected pinned Compact 0.36.1 compiler, got ${compilerVersion}`);

const runtime = resolve(runtimeDirectory);
const runtimePackage = JSON.parse(readFileSync(join(runtime, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const openZeppelin = resolve(openZeppelinRoot);
if (existsSync(join(openZeppelin, '.git'))) {
  const actualOpenZeppelinCommit = execFileSync('git', ['-C', openZeppelin, 'rev-parse', 'HEAD'], {
    encoding: 'utf8',
  }).trim();
  assert.equal(actualOpenZeppelinCommit, expectedOpenZeppelinCommit,
    `expected pinned OpenZeppelin commit ${expectedOpenZeppelinCommit}`);
}
const openZeppelinCommit = expectedOpenZeppelinCommit;

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(
  openZeppelin,
  'contracts/test/integration/_mocks/ComposedConfidentialFungibleTokenPublicSupply.compact',
);
const sourceHash = createHash('sha256').update(readFileSync(source)).digest('hex');
assert.equal(sourceHash, expectedWrapperHash,
  'expected the documented OpenZeppelin public-supply wrapper');

const defaultOutput = route === 'transfer'
  ? 'build/experiments/1383-compact/compiled'
  : 'build/experiments/1382-compact-sweep/compiled';
const generated = resolve(outputArgument ?? join(root, defaultOutput));
const manifestPath = join(generated, 'compiler/contract-manifest.json');
if (!existsSync(manifestPath)) {
  mkdirSync(dirname(generated), { recursive: true });
  execFileSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
}

const manifest = JSON.parse(readFileSync(manifestPath, 'utf8'));
assert.equal(manifest['compiler-version'], '0.36.1');
assert.equal(manifest['compiler-commit'], expectedCompactCommit);
assert.equal(manifest['runtime-version'], '0.21.0');
const relationPath = join(generated, `zkir/${route}.zkir`);
assert.ok(existsSync(relationPath), `the pinned compile must retain ${route}.zkir`);
const relation = JSON.parse(readFileSync(relationPath, 'utf8'));

const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
mkdirSync(dirname(runtimeLink), { recursive: true });
if (!existsSync(runtimeLink)) {
  symlinkSync(runtime, runtimeLink, 'dir');
} else {
  assert.ok(lstatSync(runtimeLink).isSymbolicLink(), 'generated runtime link must be a symlink');
  assert.equal(realpathSync(runtimeLink), realpathSync(runtime));
}

const compactRuntime = await import(pathToFileURL(join(runtime, 'dist/index.js')).href);
assert.equal(compactRuntime.versionString, '0.21.0');
const generatedContract = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
const { Contract, circuitSignatures, ledger, pureCircuits } = generatedContract;

const alicePrivateState = {
  secretKey: new Uint8Array(32).fill(17),
  encryptionKey: new Uint8Array(32).fill(7),
  randomnessSeed: new Uint8Array(32).fill(42),
};
const bobPrivateState = {
  secretKey: new Uint8Array(32).fill(18),
  encryptionKey: new Uint8Array(32).fill(8),
  randomnessSeed: new Uint8Array(32).fill(43),
};
const unregisteredPrivateState = {
  secretKey: new Uint8Array(32).fill(19),
  encryptionKey: new Uint8Array(32).fill(9),
  randomnessSeed: new Uint8Array(32).fill(44),
};
const wallet = '00'.repeat(32);
const contract = new Contract({
  wit_ConfidentialTokenSK: context => [context.privateState, context.privateState.secretKey],
  wit_ConfidentialTokenEK: context => [context.privateState, context.privateState.encryptionKey],
  wit_PlaintextBalance: context => [context.privateState, context.privateState.plaintextBalance ?? 0n],
  wit_RandomnessSeed: context => [context.privateState, context.privateState.randomnessSeed],
});

const constructorInputs = { name: 'Noctium Token', symbol: 'NOC', decimals: 6n };
const { currentContractState, currentPrivateState } = await contract.initialState(
  compactRuntime.createConstructorContext(alicePrivateState, wallet),
  constructorInputs.name,
  constructorInputs.symbol,
  constructorInputs.decimals,
);

const makeContext = (circuitId, state, privateState = currentPrivateState) =>
  compactRuntime.createCircuitContext({
    circuitId,
    contractAddress: compactRuntime.dummyContractAddress(),
    coinPublicKeyOrZswapState: wallet,
    contractState: state,
    privateState,
  });

const normalize = value => {
  if (typeof value === 'bigint') return { $bigint: value.toString() };
  if (value instanceof Uint8Array) return { $bytes: Buffer.from(value).toString('hex') };
  if (Array.isArray(value)) return value.map(normalize);
  if (value instanceof Map) {
    return [...value.entries()]
      .map(([key, entry]) => [normalize(key), normalize(entry)])
      .sort((left, right) => JSON.stringify(left[0]).localeCompare(JSON.stringify(right[0])));
  }
  if (value && typeof value === 'object') {
    return Object.fromEntries(Object.entries(value)
      .sort(([left], [right]) => left.localeCompare(right))
      .map(([key, entry]) => [key, normalize(entry)]));
  }
  return value;
};

const stateFrame = chargedState => JSON.stringify(normalize(chargedState.state.encode()));
const sha256 = value => createHash('sha256').update(value).digest('hex');
const hex = value => Buffer.from(value).toString('hex');

const aliceAccountId = pureCircuits.computeAccountId(alicePrivateState.secretKey);
const bobAccountId = pureCircuits.computeAccountId(bobPrivateState.secretKey);
const unregisteredAccountId = pureCircuits.computeAccountId(unregisteredPrivateState.secretKey);
const secretToScalarTag = new Uint8Array(32);
secretToScalarTag.set(new TextEncoder().encode('ElGamal:secretToScalar'));
const encryptionScalar = secret => compactRuntime.degradeToTransient(
  compactRuntime.persistentHash(
    new compactRuntime.CompactTypeVector(2, new compactRuntime.CompactTypeBytes(32)),
    [secretToScalarTag, secret],
  ),
);
const encryptionPublicKey = secret => compactRuntime.ecMulGenerator(encryptionScalar(secret));
const alicePublicKey = encryptionPublicKey(alicePrivateState.encryptionKey);
const bobPublicKey = encryptionPublicKey(bobPrivateState.encryptionKey);
const identity = compactRuntime.ecMulGenerator(0n);
const identityCiphertext = { c1: identity, c2: identity };
const decryptBalancePoint = (ciphertext, secret) => compactRuntime.ecAdd(
  ciphertext.c2,
  compactRuntime.ecNeg(compactRuntime.ecMul(ciphertext.c1, encryptionScalar(secret))),
);
const assertEncryptedBalance = (ciphertext, secret, expected, message) => {
  assert.deepEqual(decryptBalancePoint(ciphertext, secret), compactRuntime.ecMulGenerator(expected), message);
};
const memoDomain = new Uint8Array(32);
memoDomain.set(new TextEncoder().encode('OZ_CFT_ecdh_memo_v1'));
const decryptMemoAmount = (memo, secret) => {
  const sharedPoint = compactRuntime.ecMul(memo.ephemeralPk, encryptionScalar(secret));
  const sharedDigest = compactRuntime.persistentHash(compactRuntime.CompactTypeJubjubPoint, sharedPoint);
  const mask = compactRuntime.degradeToTransient(compactRuntime.persistentHash(
    new compactRuntime.CompactTypeVector(2, new compactRuntime.CompactTypeBytes(32)),
    [sharedDigest, memoDomain],
  ));
  return compactRuntime.bigIntModFr(memo.ct - mask);
};

const call = async (circuitId, state, privateState, ...args) => {
  const context = makeContext(circuitId, state, privateState);
  const result = await contract.circuits[circuitId](context, ...args);
  return {
    result: result.result,
    state: result.context.callContext.currentQueryContext.state,
  };
};

let state = currentContractState.data;
const registerAlice = await call('registerWithKey', state, alicePrivateState, alicePublicKey);
assert.deepEqual(registerAlice.result, aliceAccountId,
  'the first registration must return Alice’s derived account id');
state = registerAlice.state;
const registerBob = await call('registerWithKey', state, bobPrivateState, bobPublicKey);
assert.deepEqual(registerBob.result, bobAccountId,
  'the sibling registration must return Bob’s derived account id');
state = registerBob.state;

const mintAlice = await call('mint', state, alicePrivateState, aliceAccountId, 12n);
state = mintAlice.state;
const mintBob = await call('mint', state, bobPrivateState, bobAccountId, 7n);
state = mintBob.state;
const mintedState = state;

const read = async (circuitId, queryState, privateState, ...args) => {
  const context = makeContext(circuitId, queryState, privateState);
  const before = stateFrame(context.callContext.currentQueryContext.state);
  const result = await contract.circuits[circuitId](context, ...args);
  const afterState = result.context.callContext.currentQueryContext.state;
  const after = stateFrame(afterState);
  assert.equal(before, after, `${circuitId} view must preserve the exact Compact state frame`);
  return { result: result.result, state: afterState };
};

const observe = async observedState => {
  const [aliceBalance, alicePending, bobBalance, bobPending, totalSupply] = await Promise.all([
    read('balanceOf', observedState, alicePrivateState, aliceAccountId),
    read('pendingOf', observedState, alicePrivateState, aliceAccountId),
    read('balanceOf', observedState, alicePrivateState, bobAccountId),
    read('pendingOf', observedState, alicePrivateState, bobAccountId),
    read('totalSupply', observedState, alicePrivateState),
  ]);
  return {
    aliceBalance: aliceBalance.result,
    alicePending: alicePending.result,
    bobBalance: bobBalance.result,
    bobPending: bobPending.result,
    totalSupply: totalSupply.result,
  };
};

const before = await observe(mintedState);
assert.deepEqual(before.aliceBalance, identityCiphertext,
  'Alice starts with the encrypted-zero spendable balance');
assert.deepEqual(before.bobBalance, identityCiphertext,
  'Bob starts with the encrypted-zero spendable balance');
assert.equal(before.totalSupply, 19n, 'public mints must account for 12 + 7 supply');
assert.equal(ledger(mintedState).Token__encryptionKeys.member(aliceAccountId), true);
assert.equal(ledger(mintedState).Token__encryptionKeys.member(bobAccountId), true);
assert.deepEqual(ledger(mintedState).Token__balances.lookup(aliceAccountId), before.aliceBalance);
assert.deepEqual(ledger(mintedState).Token__pending.lookup(aliceAccountId), before.alicePending);
assert.deepEqual(ledger(mintedState).Token__balances.lookup(bobAccountId), before.bobBalance);
assert.deepEqual(ledger(mintedState).Token__pending.lookup(bobAccountId), before.bobPending);

const entries = map => [...map].map(([key, value]) => [hex(key), normalize(value)])
  .sort(([left], [right]) => left.localeCompare(right));
const siblingProjection = observedState => {
  const compactLedger = ledger(observedState);
  return {
    registeredKey: compactLedger.Token__encryptionKeys.lookup(bobAccountId),
    balance: compactLedger.Token__balances.lookup(bobAccountId),
    pending: compactLedger.Token__pending.lookup(bobAccountId),
    memos: [...compactLedger.Token__memos.lookup(bobAccountId)],
    escrow: compactLedger.Token__escrow.member(bobAccountId)
      ? [...compactLedger.Token__escrow.lookup(bobAccountId)]
      : [],
  };
};
const bobBeforeSweep = siblingProjection(mintedState);
const unchangedEntries = {
  encryptionKeys: entries(ledger(mintedState).Token__encryptionKeys),
};
const unrelatedAccountState = observedState => {
  const compactLedger = ledger(observedState);
  const memoList = accountId => compactLedger.Token__memos.member(accountId)
    ? [...compactLedger.Token__memos.lookup(accountId)]
    : null;
  const escrowRows = accountId => compactLedger.Token__escrow.member(accountId)
    ? [...compactLedger.Token__escrow.lookup(accountId)]
    : null;
  return {
    memoMapSize: compactLedger.Token__memos.size().toString(),
    aliceMemos: memoList(aliceAccountId),
    bobMemos: memoList(bobAccountId),
    escrowMapSize: compactLedger.Token__escrow.size().toString(),
    aliceEscrow: escrowRows(aliceAccountId),
    bobEscrow: escrowRows(bobAccountId),
  };
};
const unrelatedStateBefore = unrelatedAccountState(mintedState);

const runTransferRoute = async () => {
  const sweepContext = makeContext('sweep', mintedState, alicePrivateState);
  const successfulSweep = await contract.circuits.sweep(sweepContext);
  const transferBeforeState = successfulSweep.context.callContext.currentQueryContext.state;
  assert.deepEqual(successfulSweep.result, aliceAccountId,
    'the transfer route must sweep Alice and return her account id');

  const beforeTransfer = await observe(transferBeforeState);
  assertEncryptedBalance(beforeTransfer.aliceBalance, alicePrivateState.encryptionKey, 12n,
    'Alice must have 12 spendable tokens before transfer');
  assertEncryptedBalance(beforeTransfer.alicePending, alicePrivateState.encryptionKey, 0n,
    'Alice must have no pending tokens after sweep');
  assertEncryptedBalance(beforeTransfer.bobBalance, bobPrivateState.encryptionKey, 0n,
    'Bob must have no spendable tokens before transfer');
  assertEncryptedBalance(beforeTransfer.bobPending, bobPrivateState.encryptionKey, 7n,
    'Bob must retain his 7 pending minted tokens before transfer');
  assert.equal(beforeTransfer.totalSupply, 19n,
    'the transfer route must start from public supply 19');

  const bobBeforeTransfer = siblingProjection(transferBeforeState);
  const unrelatedBeforeTransfer = unrelatedAccountState(transferBeforeState);
  const aliceTransferPrivateState = { ...alicePrivateState, plaintextBalance: 12n };
  const transferFrameBefore = stateFrame(transferBeforeState);
  const transferContext = makeContext('transfer', transferBeforeState, aliceTransferPrivateState);
  const successfulTransfer = await contract.circuits.transfer(transferContext, bobAccountId, 5n);
  const transferredState = successfulTransfer.context.callContext.currentQueryContext.state;
  assert.deepEqual(successfulTransfer.result, aliceAccountId,
    'transfer must return the authenticated sender account id');

  const afterTransfer = await observe(transferredState);
  assertEncryptedBalance(afterTransfer.aliceBalance, alicePrivateState.encryptionKey, 7n,
    'Alice must have 7 spendable tokens after transferring 5');
  assertEncryptedBalance(afterTransfer.alicePending, alicePrivateState.encryptionKey, 0n,
    'Alice pending balance must remain zero');
  assertEncryptedBalance(afterTransfer.bobBalance, bobPrivateState.encryptionKey, 0n,
    'Bob spendable balance must remain zero');
  assertEncryptedBalance(afterTransfer.bobPending, bobPrivateState.encryptionKey, 12n,
    'Bob pending balance must increase from 7 to 12');
  assert.equal(afterTransfer.totalSupply, 19n,
    'transfer must preserve public total supply');

  const bobAfterTransfer = siblingProjection(transferredState);
  assert.equal(bobAfterTransfer.memos.length, bobBeforeTransfer.memos.length + 1,
    'transfer must prepend one memo to Bob’s existing memo list');
  assert.deepEqual(bobAfterTransfer.memos.slice(1), bobBeforeTransfer.memos,
    'transfer must preserve Bob’s older memos in order');
  const deliveredMemoValue = decryptMemoAmount(bobAfterTransfer.memos[0], bobPrivateState.encryptionKey);
  assert.equal(deliveredMemoValue, 5n,
    'the new Bob memo must decrypt to the transferred amount');
  assert.deepEqual(bobAfterTransfer.balance, bobBeforeTransfer.balance,
    'transfer must preserve Bob’s spendable ciphertext');
  assert.deepEqual(bobAfterTransfer.registeredKey, bobBeforeTransfer.registeredKey,
    'transfer must preserve Bob’s registered encryption key');
  assert.deepEqual(
    ledger(transferredState).Token__encryptionKeys.lookup(aliceAccountId),
    ledger(transferBeforeState).Token__encryptionKeys.lookup(aliceAccountId),
    'transfer must preserve Alice’s registered encryption key',
  );
  assert.deepEqual(bobAfterTransfer.escrow, bobBeforeTransfer.escrow,
    'transfer must preserve Bob’s escrow state');
  const unrelatedAfterTransfer = unrelatedAccountState(transferredState);
  assert.equal(unrelatedAfterTransfer.memoMapSize, unrelatedBeforeTransfer.memoMapSize,
    'transfer must not add or remove memo-map accounts');
  assert.deepEqual(unrelatedAfterTransfer.aliceMemos, unrelatedBeforeTransfer.aliceMemos,
    'transfer must preserve Alice’s memo list');
  assert.deepEqual(unrelatedAfterTransfer.aliceEscrow, unrelatedBeforeTransfer.aliceEscrow,
    'transfer must preserve Alice’s escrow state');
  assert.deepEqual(unrelatedAfterTransfer.bobEscrow, unrelatedBeforeTransfer.bobEscrow,
    'transfer must preserve Bob’s escrow state');

  const rejectionContext = makeContext('transfer', transferBeforeState, aliceTransferPrivateState);
  const rejectionFrameBefore = stateFrame(rejectionContext.callContext.currentQueryContext.state);
  let rejectionError;
  try {
    await contract.circuits.transfer(rejectionContext, bobAccountId, 13n);
  } catch (error) {
    rejectionError = error;
  }
  assert.ok(rejectionError, 'Alice must not transfer 13 from the same 12-token snapshot');
  assert.match(rejectionError.message, /ConfidentialFungibleToken: insufficient balance/);
  const rejectionFrameAfter = stateFrame(rejectionContext.callContext.currentQueryContext.state);
  assert.equal(rejectionFrameBefore, rejectionFrameAfter,
    'the rejected overspend must preserve the exact supplied Compact state frame');
  assert.equal(stateFrame(transferBeforeState), rejectionFrameBefore,
    'the rejected overspend must not mutate the shared before-transfer snapshot');

  const transferSignature = circuitSignatures.transfer;
  assert.deepEqual(transferSignature.argumentTypes, [
    { tag: 'Bytes', length: 32 },
    { tag: 'Uint', maxval: '340282366920938463463374607431768211455' },
  ], 'generated transfer ABI must take (Bytes<32>, Uint<128>)');
  assert.deepEqual(transferSignature.resultType, { tag: 'Bytes', length: 32 },
    'generated transfer ABI must return Bytes<32>');
  assert.equal(relation.inputs.length, 3,
    'transfer ZKIR header must expose two Bytes<32> coordinates plus the Uint<128> value');
  assert.equal(relation.outputs.length, 2,
    'transfer ZKIR header must retain both Bytes<32> result limbs');
  const relationHash = sha256(readFileSync(relationPath));
  const transferFrameAfter = stateFrame(transferredState);
  const stateEvidence = (beforeState, afterState) => ({
    sha256Before: sha256(beforeState),
    sha256After: sha256(afterState),
    unchanged: beforeState === afterState,
  });
  return {
    abi: {
      circuit: 'transfer',
      generatedArgumentTypes: transferSignature.argumentTypes,
      generatedResultType: transferSignature.resultType,
      inputs: ['Bytes<32>', 'Uint<128>'],
      returns: 'Bytes<32>',
    },
    observation: {
      before: {
        aliceBalance: '12',
        alicePending: '0',
        bobBalance: '0',
        bobPending: '7',
        totalSupply: beforeTransfer.totalSupply.toString(),
      },
      after: {
        aliceBalance: '7',
        alicePending: '0',
        bobBalance: '0',
        bobPending: '12',
        totalSupply: afterTransfer.totalSupply.toString(),
      },
      amountProvenance: 'synthetic ElGamal decryption checked against ecMulGenerator(amount)',
      returnedCaller: hex(successfulTransfer.result),
      aliceAccountId: hex(aliceAccountId),
      bobAccountId: hex(bobAccountId),
      totalSupplyUnchanged: beforeTransfer.totalSupply === afterTransfer.totalSupply,
      memo: {
        bobMemoCountBefore: bobBeforeTransfer.memos.length,
        bobMemoCountAfter: bobAfterTransfer.memos.length,
        newestMemoDecryptsTo: deliveredMemoValue.toString(),
        priorMemosPreservedInOrder: true,
      },
      exactState: stateEvidence(transferFrameBefore, transferFrameAfter),
      unchangedStateEvidence: {
        alicePending: true,
        bobSpendable: true,
        aliceAndBobKeys: true,
        aliceMemos: true,
        escrow: true,
      },
    },
    rejection: {
      circuit: 'transfer',
      callerAccountId: hex(aliceAccountId),
      recipientAccountId: hex(bobAccountId),
      attemptedValue: '13',
      expected: 'ConfidentialFungibleToken: insufficient balance',
      rejected: true,
      errorName: rejectionError.name,
      errorMessage: rejectionError.message,
      stateUnchanged: rejectionFrameBefore === rejectionFrameAfter,
      state: stateEvidence(rejectionFrameBefore, rejectionFrameAfter),
    },
    compact: {
      compiler: compilerVersion,
      runtime: runtimePackage.version,
      openZeppelinCommit,
      wrapperSha256: sourceHash,
      zkir: {
        rawFilePath: relationPath,
        sha256: relationHash,
        inputs: relation.inputs,
        outputs: relation.outputs,
      },
    },
  };
};

if (route === 'transfer') {
  console.log(JSON.stringify(await runTransferRoute()));
} else {
const balancesBefore = entries(ledger(mintedState).Token__balances);
const pendingBefore = entries(ledger(mintedState).Token__pending);

const sweepContext = makeContext('sweep', mintedState, alicePrivateState);
const successfulSweep = await contract.circuits.sweep(sweepContext);
const sweptState = successfulSweep.context.callContext.currentQueryContext.state;
assert.deepEqual(successfulSweep.result, aliceAccountId,
  'sweep must return the caller’s account id');
const after = await observe(sweptState);
const aliceBalanceAfter = after.aliceBalance;
const expectedAliceBalanceAfter = {
  c1: compactRuntime.ecAdd(before.aliceBalance.c1, before.alicePending.c1),
  c2: compactRuntime.ecAdd(before.aliceBalance.c2, before.alicePending.c2),
};
assert.deepEqual(aliceBalanceAfter, expectedAliceBalanceAfter,
  'sweep must homomorphically add both pending ciphertext points into spendable balance');
assert.deepEqual(after.alicePending, identityCiphertext,
  'sweep must reset both pending ciphertext points to the identity');
assert.deepEqual(after.bobBalance, before.bobBalance,
  'Alice’s sweep must preserve Bob’s spendable ciphertext');
assert.deepEqual(after.bobPending, before.bobPending,
  'Alice’s sweep must preserve Bob’s pending ciphertext');
assert.equal(after.totalSupply, before.totalSupply,
  'sweep must preserve the public total supply');
assert.deepEqual(siblingProjection(sweptState), bobBeforeSweep,
  'Alice’s sweep must preserve Bob’s key, both ciphertexts, memo list, and escrow state');
const bobAfterSweep = siblingProjection(sweptState);

const balancesAfter = entries(ledger(sweptState).Token__balances);
const pendingAfter = entries(ledger(sweptState).Token__pending);
const withoutAlice = key => rows => rows.filter(([rowKey]) => rowKey !== key);
assert.deepEqual(withoutAlice(hex(aliceAccountId))(balancesAfter),
  withoutAlice(hex(aliceAccountId))(balancesBefore),
  'only Alice’s balance-map entry may change during sweep');
assert.deepEqual(withoutAlice(hex(aliceAccountId))(pendingAfter),
  withoutAlice(hex(aliceAccountId))(pendingBefore),
  'only Alice’s pending-map entry may change during sweep');
const unchangedEntriesAfter = {
  encryptionKeys: entries(ledger(sweptState).Token__encryptionKeys),
};
assert.deepEqual(unchangedEntriesAfter, unchangedEntries,
  'sweep must preserve every registered encryption key');
assert.deepEqual(unrelatedAccountState(sweptState), unrelatedStateBefore,
  'sweep must preserve Alice and Bob memo lists and escrow state');

const unregisteredSweepContext = makeContext('sweep', sweptState, unregisteredPrivateState);
const rejectionBeforeFrame = stateFrame(unregisteredSweepContext.callContext.currentQueryContext.state);
let rejectionError;
try {
  await contract.circuits.sweep(unregisteredSweepContext);
} catch (error) {
  rejectionError = error;
}
assert.ok(rejectionError, 'an unregistered account must not sweep');
assert.match(rejectionError.message, /ConfidentialFungibleToken: not registered/);
const rejectionAfterFrame = stateFrame(unregisteredSweepContext.callContext.currentQueryContext.state);
assert.equal(rejectionBeforeFrame, rejectionAfterFrame,
  'the rejected unregistered sweep must preserve the exact supplied Compact state frame');
assert.equal(stateFrame(sweptState), rejectionBeforeFrame,
  'the rejected unregistered sweep must not mutate the supplied state object');

const sweepSignature = circuitSignatures.sweep;
assert.deepEqual(sweepSignature.argumentTypes, [], 'generated sweep ABI must take no arguments');
assert.deepEqual(sweepSignature.resultType, { tag: 'Bytes', length: 32 },
  'generated sweep ABI must return Bytes<32>');
assert.deepEqual(relation.inputs, [], 'sweep ZKIR header must have no declared inputs');
const relationHash = sha256(readFileSync(relationPath));
const stateEvidence = (beforeState, afterState) => ({
  sha256Before: sha256(beforeState),
  sha256After: sha256(afterState),
  unchanged: beforeState === afterState,
});
const result = {
  abi: {
    circuit: 'sweep',
    generatedArgumentTypes: sweepSignature.argumentTypes,
    generatedResultType: sweepSignature.resultType,
    inputs: [],
    returns: 'Bytes<32>',
  },
  observation: {
    before: {
      aliceBalance: '0',
      alicePending: '12',
      bobBalance: '0',
      bobPending: '7',
      totalSupply: before.totalSupply.toString(),
    },
    after: {
      aliceBalance: '12',
      alicePending: '0',
      bobBalance: '0',
      bobPending: '7',
      totalSupply: after.totalSupply.toString(),
    },
    amountProvenance: 'synthetic harness-known mint amounts; ciphertexts are checked homomorphically and not decrypted',
    returnedCaller: hex(successfulSweep.result),
    aliceAccountId: hex(aliceAccountId),
    siblingUnchanged: JSON.stringify(normalize(bobBeforeSweep)) === JSON.stringify(normalize(bobAfterSweep)),
    totalSupplyUnchanged: before.totalSupply === after.totalSupply,
  },
  rejection: {
    circuit: 'sweep',
    callerAccountId: hex(unregisteredAccountId),
    expected: 'ConfidentialFungibleToken: not registered',
    rejected: true,
    errorName: rejectionError.name,
    errorMessage: rejectionError.message,
    exactStateFrameUnchanged: rejectionBeforeFrame === rejectionAfterFrame,
    state: stateEvidence(rejectionBeforeFrame, rejectionAfterFrame),
  },
  compact: {
    compiler: compilerVersion,
    runtime: runtimePackage.version,
    openZeppelinCommit,
    wrapperSha256: sourceHash,
    constructorInputs: {
      ...constructorInputs,
      decimals: constructorInputs.decimals.toString(),
    },
    syntheticWallets: {
      alice: { accountSecretByte: 17, encryptionSecretByte: 7, randomnessSeedByte: 42 },
      bob: { accountSecretByte: 18, encryptionSecretByte: 8, randomnessSeedByte: 43 },
      unregistered: { accountSecretByte: 19, encryptionSecretByte: 9, randomnessSeedByte: 44 },
    },
    successfulMints: [
      { circuit: 'mint', accountId: hex(aliceAccountId), amount: '12' },
      { circuit: 'mint', accountId: hex(bobAccountId), amount: '7' },
    ],
    sweep: {
      actualInputAbi: sweepSignature.argumentTypes,
      actualResultType: sweepSignature.resultType,
      publicOutputs: relation.outputs,
      returnedCaller: hex(successfulSweep.result),
      aliceCiphertextBefore: normalize({ balance: before.aliceBalance, pending: before.alicePending }),
      aliceCiphertextAfter: normalize({ balance: after.aliceBalance, pending: after.alicePending }),
      aliceBalanceAfterEqualsHomomorphicSum: true,
      alicePendingAfterIsIdentity: true,
      bobLedgerProjectionBefore: normalize(bobBeforeSweep),
      bobLedgerProjectionAfter: normalize(bobAfterSweep),
      totalSupplyBefore: before.totalSupply.toString(),
      totalSupplyAfter: after.totalSupply.toString(),
      unchangedMapEvidence: {
        allEncryptionKeys: true,
        allMemoLists: true,
        allEscrowEntries: true,
        allNonAliceBalanceEntries: true,
        allNonAlicePendingEntries: true,
      },
      rejectionState: stateEvidence(rejectionBeforeFrame, rejectionAfterFrame),
    },
    zkir: {
      path: generated.replace(`${root}/`, '') + '/zkir/sweep.zkir',
      sha256: relationHash,
      inputs: relation.inputs,
      outputs: relation.outputs,
    },
  },
};

console.log(JSON.stringify(result));
}
