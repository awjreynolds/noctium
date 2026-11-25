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

const [compactc, runtimeDirectory, openZeppelinRoot, outputArgument] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory && openZeppelinRoot,
  'usage: node tests/compact/confidential-token-total-supply.mjs <compactc-0.36.1> <compact-runtime-0.21.0> <openzeppelin-contracts-compact-root> [compiled-output]');

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

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(
  resolve(openZeppelinRoot),
  'contracts/test/integration/_mocks/ComposedConfidentialFungibleTokenPublicSupply.compact',
);
const sourceHash = createHash('sha256').update(readFileSync(source)).digest('hex');
assert.equal(sourceHash, expectedWrapperHash,
  'expected the documented OpenZeppelin public-supply wrapper');

const generated = resolve(outputArgument ?? join(
  root,
  'build/experiments/1381-compact-total-supply/compiled',
));
const manifestPath = join(generated, 'compiler/contract-manifest.json');
if (!existsSync(manifestPath)) {
  mkdirSync(dirname(generated), { recursive: true });
  execFileSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
}

const manifest = JSON.parse(readFileSync(manifestPath, 'utf8'));
assert.equal(manifest['compiler-version'], '0.36.1');
assert.equal(manifest['compiler-commit'], expectedCompactCommit);
assert.equal(manifest['runtime-version'], '0.21.0');
const relationPath = join(generated, 'zkir/totalSupply.zkir');
assert.ok(existsSync(relationPath), 'the pinned compile must retain totalSupply.zkir');
const relation = JSON.parse(readFileSync(relationPath, 'utf8'));
assert.deepEqual(relation.inputs, []);
assert.deepEqual(relation.outputs, ['Scalar<BLS12-381>']);

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
const { Contract, ledger, pureCircuits } = generatedContract;

const secretKey = new Uint8Array(32).fill(17);
const encryptionKey = new Uint8Array(32).fill(7);
const randomnessSeed = new Uint8Array(32).fill(42);
const privateState = { secretKey, encryptionKey, randomnessSeed };
const wallet = '00'.repeat(32);
const contract = new Contract({
  wit_ConfidentialTokenSK: context => [context.privateState, context.privateState.secretKey],
  wit_ConfidentialTokenEK: context => [context.privateState, context.privateState.encryptionKey],
  wit_PlaintextBalance: context => [context.privateState, 0n],
  wit_RandomnessSeed: context => [context.privateState, context.privateState.randomnessSeed],
});

const constructorInputs = { name: 'Noctium Token', symbol: 'NOC', decimals: 6n };
const { currentContractState, currentPrivateState } = await contract.initialState(
  compactRuntime.createConstructorContext(privateState, wallet),
  constructorInputs.name,
  constructorInputs.symbol,
  constructorInputs.decimals,
);

const makeContext = (circuitId, state, callPrivateState = currentPrivateState) =>
  compactRuntime.createCircuitContext({
    circuitId,
    contractAddress: compactRuntime.dummyContractAddress(),
    coinPublicKeyOrZswapState: wallet,
    contractState: state,
    privateState: callPrivateState,
  });

const normalize = value => {
  if (typeof value === 'bigint') return { $bigint: value.toString() };
  if (value instanceof Uint8Array) {
    return { $bytes: Buffer.from(value).toString('hex') };
  }
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
const totalSupplyCellFrame = chargedState => {
  const cells = chargedState.state.asArray();
  assert.ok(cells && cells.length > 11, 'expected the upstream twelve-slot state frame');
  assert.equal(cells[11].type(), 'cell');
  return normalize(cells[11].asCell());
};

const readSupply = async state => {
  const call = await contract.circuits.totalSupply(makeContext('totalSupply', state));
  const after = call.context.callContext.currentQueryContext.state;
  return {
    result: call.result,
    state: after,
    beforeState: state,
    afterState: after,
    beforeFrame: stateFrame(state),
    afterFrame: stateFrame(after),
  };
};

const zeroBefore = currentContractState.data;
assert.equal(ledger(zeroBefore).Supply__totalSupply, 0n);
const zeroRead = await readSupply(zeroBefore);
assert.equal(typeof zeroRead.result, 'bigint');
assert.equal(zeroRead.result, 0n);
assert.equal(ledger(zeroRead.state).Supply__totalSupply, 0n);
assert.equal(zeroRead.beforeFrame, zeroRead.afterFrame,
  'the totalSupply read must preserve the exact Compact state frame at zero');

const accountId = pureCircuits.computeAccountId(secretKey);
const secretToScalarTag = new Uint8Array(32);
secretToScalarTag.set(new TextEncoder().encode('ElGamal:secretToScalar'));
const encryptionKeyHash = compactRuntime.persistentHash(
  new compactRuntime.CompactTypeVector(2, new compactRuntime.CompactTypeBytes(32)),
  [secretToScalarTag, encryptionKey],
);
const encryptionPublicKey = compactRuntime.ecMulGenerator(
  compactRuntime.degradeToTransient(encryptionKeyHash),
);

const registration = await contract.circuits.registerWithKey(
  makeContext('registerWithKey', zeroRead.state),
  encryptionPublicKey,
);
assert.deepEqual(registration.result, accountId,
  'registerWithKey must register the recipient derived from the synthetic secret');
const mint = await contract.circuits.mint(
  makeContext('mint', registration.context.callContext.currentQueryContext.state),
  accountId,
  10n,
);
const tenBefore = mint.context.callContext.currentQueryContext.state;
assert.equal(ledger(tenBefore).Supply__totalSupply, 10n,
  'the nonzero case must be reached by the public registerWithKey + mint sequence');
const mintEffects = mint.context.callContext.currentQueryContext.effects;
for (const effect of ['unshieldedMints', 'unshieldedInputs', 'unshieldedOutputs', 'claimedUnshieldedSpends']) {
  const entries = mintEffects[effect];
  assert.equal(entries instanceof Map ? entries.size : entries.length, 0,
    `the confidential mint must not create ${effect}`);
}

const tenRead = await readSupply(tenBefore);
assert.equal(tenRead.result, 10n);
assert.equal(ledger(tenRead.state).Supply__totalSupply, 10n);
assert.equal(tenRead.beforeFrame, tenRead.afterFrame,
  'the totalSupply read must preserve the exact Compact state frame after mint');

const rejectionFrame = stateFrame(tenBefore);
await assert.rejects(
  contract.circuits.totalSupply(makeContext('totalSupply', tenBefore), 10n),
  /totalSupply: expected 1 argument/,
);
assert.equal(stateFrame(tenBefore), rejectionFrame,
  'a wrong-arity Compact API call must leave the supplied state frame unchanged');

const relationHash = createHash('sha256').update(readFileSync(relationPath)).digest('hex');
const digest = value => createHash('sha256').update(value).digest('hex');
const frame = read => ({
  wholeStateFrameSha256BeforeRead: digest(read.beforeFrame),
  wholeStateFrameSha256AfterRead: digest(read.afterFrame),
  wholeStateUnchanged: read.beforeFrame === read.afterFrame,
  totalSupplyCellBeforeRead: totalSupplyCellFrame(read.beforeState),
  totalSupplyCellAfterRead: totalSupplyCellFrame(read.afterState),
});
const result = {
  abi: { inputs: [], returns: 'UInt128' },
  cases: [
    { stateSupply: '0', return: zeroRead.result.toString(), stateUnchanged: zeroRead.beforeFrame === zeroRead.afterFrame },
    { stateSupply: '10', return: tenRead.result.toString(), stateUnchanged: tenRead.beforeFrame === tenRead.afterFrame },
  ],
  compact: {
    compiler: compilerVersion,
    runtime: runtimePackage.version,
    openZeppelinCommit: expectedOpenZeppelinCommit,
    wrapperSha256: sourceHash,
    constructorInputs: {
      ...constructorInputs,
      decimals: constructorInputs.decimals.toString(),
    },
    totalSupplyCallerInputs: [],
    nonzeroReachability: {
      circuits: ['registerWithKey', 'mint'],
      mintAmount: '10',
      recipientAccountId: 'synthetic account derived by Compact computeAccountId(secretKey)',
      unshieldedEffects: 0,
    },
    stateMapping: {
      logicalState: 'totalSupply',
      compactLedgerField: 'Supply__totalSupply',
      topLevelStateArrayIndex: 11,
      compactType: 'Uint<128>',
      cellAlignment: [{ tag: 'atom', value: { tag: 'bytes', length: 16 } }],
      cellEncodingAtZero: totalSupplyCellFrame(zeroBefore),
      cellEncodingAtTen: totalSupplyCellFrame(tenBefore),
      stateFrameEncoding: 'Compact runtime StateValue.encode(), canonical JSON hashed with SHA-256 for the whole state; cell frames are emitted exactly',
    },
    stateFrames: { zero: frame(zeroRead), ten: frame(tenRead) },
    rejection: {
      boundary: 'generated Compact TypeScript circuit API',
      circuit: 'totalSupply',
      invalidCall: 'one unexpected argument',
      rejected: true,
      stateUnchanged: true,
    },
    zkir: {
      path: generated.replace(`${root}/`, '') + '/zkir/totalSupply.zkir',
      sha256: relationHash,
      inputs: relation.inputs,
      outputs: relation.outputs,
    },
  },
};

console.log(JSON.stringify(result));
