import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, rmdirSync, symlinkSync, writeFileSync } from 'node:fs';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/readable-iteration.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/,
  `expected pinned Compact 0.36.1 compiler, got ${compilerVersion}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0', 'expected pinned Compact runtime 0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/ReadableIteration.compact');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'readable-iteration-'));


process.on('exit', () => {
  rmSync(scratch, { recursive: true, force: true });
  try {
    rmdirSync(experiments);
  } catch (error) {
    if (error.code !== 'ENOENT' && error.code !== 'ENOTEMPTY') throw error;
  }
});
const generated = join(scratch, 'compact');
const compile = spawnSync(compactc, ['--skip-zk', source, generated], {
  cwd: projectRoot,
  encoding: 'utf8',
});
assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

const compileProbe = (name, circuit) => {
  const probeSource = join(scratch, `${name}.compact`);
  const probeOutput = join(scratch, name);
  writeFileSync(probeSource, `${readFileSync(source, 'utf8')}\n${circuit}\n`);
  return spawnSync(compactc, ['--skip-zk', probeSource, probeOutput], {
    cwd: projectRoot,
    encoding: 'utf8',
  });
};
const incompatibleBranches = compileProbe('incompatible-map-branches', `
  export circuit incompatibleMapBranches(): Boolean {
    const mapped = map((item) => true ? (0 as Field) : true, emptyTupleItems());
    return mapped == [];
  }
`);
assert.notEqual(incompatibleBranches.status, 0,
  'Compact should reject incompatible Field and Boolean map branches');
assert.match(`${incompatibleBranches.stderr}\n${incompatibleBranches.stdout}`,
  /mismatch between type Field and type Boolean of condition branches/);
const arithmeticWithoutItemType = compileProbe('empty-map-arithmetic-without-item-type', `
  export circuit emptyMapArithmeticWithoutItemType(): Vector<0, Field> {
    return map((item) => item + item, emptyTupleItems());
  }
`);
assert.notEqual(arithmeticWithoutItemType.status, 0,
  'Compact should reject callback arithmetic when an empty tuple leaves the item type unresolved');

const mismatchedPairLengths = compileProbe('mismatched-map-sequences', `
  export circuit mismatchedMapSequences(): Field {
    const mapped = map((left, right) => pairVisit(left, right), pairLeftItems(), [1]);
    return mapped[0];
  }
`);
assert.notEqual(mismatchedPairLengths.status, 0);
assert.match(`${mismatchedPairLengths.stderr}\n${mismatchedPairLengths.stdout}`, /length|size/);

const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
mkdirSync(dirname(runtimeLink), { recursive: true });
symlinkSync(runtimeDirectory, runtimeLink, 'dir');

const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
const { Contract, ledger } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
const { createCircuitContext, createConstructorContext, dummyContractAddress } = runtime;
assert.equal(runtime.versionString, '0.21.0');

const blockCalls = [];
const pairCalls = [];
const pairOrder = [];
let blockOffset = 10n;
const emptyNativeMapCalls = [];
const emptyMapVisitCalls = [];
const contract = new Contract({
  iterationSeed: ({ privateState }) => [[...privateState, 'seed'], 7n],
  iterationBytes: ({ privateState }) => [[...privateState, 'bytes'], Uint8Array.from([4, 5])],
  iterationVisit: ({ privateState }, item) => [[...privateState, `visit:${item}`], item * 2n],
  pairLeftItems: ({ privateState }) => {
    pairOrder.push('leftItems');
    return [[...privateState, 'leftItems'], [1n, 2n]];
  },
  pairRightItems: ({ privateState }) => {
    pairOrder.push('rightItems');
    return [[...privateState, 'rightItems'], [10n, 20n]];
  },
  pairVisit: ({ privateState }, left, right) => {
    pairCalls.push(`${left}:${right}`);
    pairOrder.push(`visit:${left}:${right}`);
    return [[...privateState, `visit:${left}:${right}`], left + right];
  },
  emptyTupleItems: ({ privateState }) => {
    emptyNativeMapCalls.push('emptyTupleItems');
    return [privateState, []];
  },
  emptyMapVisit: ({ privateState }, item) => {
    emptyMapVisitCalls.push(item);
    return [privateState, item];
  },
  acceptEmptyNativeVector: ({ privateState }, values) => {
    emptyNativeMapCalls.push('acceptEmptyNativeVector');
    assert.deepEqual(values, []);
    return [privateState, 41n];
  },
  blockItems: ({ privateState }, seed) => {
    blockCalls.push(`items:${seed}`);
    return [privateState, [2n, 3n]];
  },
  blockOffset: ({ privateState }, seed) => {
    blockCalls.push(`offset:${seed}`);
    return [privateState, blockOffset];
  },
  shadowItems: ({ privateState }, seed) => {
    blockCalls.push(`shadowItems:${seed}`);
    return [privateState, [4n, 5n]];
  },
  shadowVisit: ({ privateState }, item, outer) => {
    blockCalls.push(`shadowVisit:${item}:${outer}`);
    return [privateState, item + outer];
  },
});
const wallet = '00'.repeat(32);
const { currentContractState } = await contract.initialState(createConstructorContext([], wallet));
const circuitContext = (circuitId) => createCircuitContext({
  circuitId,
  contractAddress: dummyContractAddress(),
  coinPublicKeyOrZswapState: wallet,
  contractState: currentContractState.data,
  privateState: [],
});
const { result, context } = await contract.circuits.update(createCircuitContext({
  circuitId: 'update', contractAddress: dummyContractAddress(), coinPublicKeyOrZswapState: wallet,
  contractState: currentContractState.data, privateState: [],
}), 3n);
const total = ledger(context.callContext.currentQueryContext.state).total;
assert.equal(result, 31n);
assert.equal(total, 31n);
assert.deepEqual(context.callContext.currentPrivateState, ['seed', 'bytes', 'visit:4', 'visit:5']);
console.log(JSON.stringify({ result: result.toString(), total: total.toString(), order: context.callContext.currentPrivateState }));

const pairMap = await contract.circuits.runPairMap(circuitContext('runPairMap'));
assert.equal(pairMap.result, 33n);
assert.deepEqual(pairCalls, ['1:10', '2:20']);
assert.deepEqual(pairOrder, ['leftItems', 'rightItems', 'visit:1:10', 'visit:2:20']);
assert.deepEqual(pairMap.context.callContext.currentPrivateState,
  ['leftItems', 'rightItems', 'visit:1:10', 'visit:2:20']);
console.log(JSON.stringify({ result: pairMap.result.toString(), order: pairOrder }));

const runBlock = () => contract.circuits.runBlock(createCircuitContext({
  circuitId: 'runBlock', contractAddress: dummyContractAddress(), coinPublicKeyOrZswapState: wallet,
  contractState: currentContractState.data, privateState: [],
}), 7n);
assert.deepEqual((await runBlock()).result, [12n, 13n, 25n]);
assert.deepEqual(blockCalls.splice(0), ['items:7', 'offset:8']);
const shadow = await contract.circuits.runShadow(createCircuitContext({
  circuitId: 'runShadow', contractAddress: dummyContractAddress(), coinPublicKeyOrZswapState: wallet,
  contractState: currentContractState.data, privateState: [],
}), 0n);
assert.equal(shadow.result, 7n);
assert.deepEqual(blockCalls.splice(0), [
  'shadowItems:7', 'shadowVisit:4:7', 'shadowVisit:5:7',
  'shadowVisit:1:7', 'shadowVisit:2:7',
]);

const emptyNativeMap = await contract.circuits.emptyNativeMap(createCircuitContext({
  circuitId: 'emptyNativeMap', contractAddress: dummyContractAddress(), coinPublicKeyOrZswapState: wallet,
  contractState: currentContractState.data, privateState: [],
}));
assert.equal(emptyNativeMap.result, 41n);
assert.deepEqual(emptyNativeMapCalls, ['emptyTupleItems', 'acceptEmptyNativeVector']);
console.log(JSON.stringify({ result: emptyNativeMap.result.toString(), order: emptyNativeMapCalls }));

emptyNativeMapCalls.length = 0;
const siblingElse = await contract.circuits.emptyNativeMapSiblingElse(
  circuitContext('emptyNativeMapSiblingElse'), true,
);
assert.equal(siblingElse.result, true);
assert.deepEqual(emptyNativeMapCalls, ['emptyTupleItems']);
emptyNativeMapCalls.length = 0;
const siblingThen = await contract.circuits.emptyNativeMapSiblingThen(
  circuitContext('emptyNativeMapSiblingThen'), false,
);
assert.equal(siblingThen.result, true);
assert.deepEqual(emptyNativeMapCalls, ['emptyTupleItems']);
emptyNativeMapCalls.length = 0;
const unresolvedBranches = await contract.circuits.emptyNativeMapUnresolvedBranches(
  circuitContext('emptyNativeMapUnresolvedBranches'), true,
);
assert.equal(unresolvedBranches.result, true);
assert.deepEqual(emptyNativeMapCalls, ['emptyTupleItems']);
emptyNativeMapCalls.length = 0;
const emptyCallback = await contract.circuits.emptyNativeMapCallback(
  circuitContext('emptyNativeMapCallback'), true,
);
assert.equal(emptyCallback.result, true);
assert.deepEqual(emptyNativeMapCalls, ['emptyTupleItems']);
assert.deepEqual(emptyMapVisitCalls, [], 'zero-length map must not invoke its callback witness');
emptyNativeMapCalls.length = 0;
const declaredContext = await contract.circuits.emptyNativeMapDeclaredContext(
  circuitContext('emptyNativeMapDeclaredContext'),
);
assert.deepEqual(declaredContext.result, []);
assert.deepEqual(emptyNativeMapCalls, ['emptyTupleItems']);
console.log(JSON.stringify({
  siblingInference: { thenItem: siblingElse.result, elseItem: siblingThen.result },
  bothUnresolved: unresolvedBranches.result,
  declaredContext: declaredContext.result,
  incompatibleBranches: 'rejected',
  arithmeticWithoutItemType: 'rejected',
  emptyCallbackCalls: emptyMapVisitCalls,
  calls: ['emptyTupleItems'],
}));

blockOffset = 40n;
await assert.rejects(async () => runBlock(), /fold assertion/);
assert.deepEqual(blockCalls, ['items:7', 'offset:8']);
