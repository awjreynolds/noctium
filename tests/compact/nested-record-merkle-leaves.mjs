import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';

const [generatedDirectory] = process.argv.slice(2);
const runtimeDirectory = process.env.NOCTIUM_COMPACT_RUNTIME_DIR;
assert.ok(generatedDirectory && runtimeDirectory, 'pass the generated directory and set NOCTIUM_COMPACT_RUNTIME_DIR');
const { createCircuitContext, createConstructorContext, dummyContractAddress, leafHash } = await import(
  pathToFileURL(resolve(runtimeDirectory, 'dist/index.js')).href,
);
const { Contract, ledger } = await import(
  pathToFileURL(resolve(generatedDirectory, 'contract/index.js')).href,
);

const contract = new Contract({});
const walletKey = '00'.repeat(32);
const leaf = { tag: Uint8Array.of(12, 0, 0), meta: { approved: true, count: 258n } };
const defaultLeaf = { tag: new Uint8Array(3), meta: { approved: false, count: 0n } };
const replacementLeaf = { tag: leaf.tag, meta: { approved: false, count: 513n } };
const { currentContractState } = await contract.initialState(createConstructorContext(null, walletKey));
let state = currentContractState.data;

const invoke = async (entrypoint, ...args) => {
  const context = createCircuitContext({
    circuitId: entrypoint,
    contractAddress: dummyContractAddress(),
    coinPublicKeyOrZswapState: walletKey,
    contractState: state,
    privateState: null,
  });
  const call = await contract.circuits[entrypoint](context, ...args);
  state = call.context.callContext.currentQueryContext.state;
};

const alignment = [3, 1, 2].map((length) => ({ tag: 'atom', value: { tag: 'bytes', length } }));
const checkDigest = (bytes, value) => {
  const encoding = Buffer.from(bytes);
  const digest = createHash('sha256').update('mdn:lh').update(encoding).digest('hex');
  assert.equal(Buffer.from(leafHash({ value, alignment }).value[0]).toString('hex'), digest);
  return { encoding: encoding.toString('hex'), digest };
};
const leafDigest = checkDigest([12, 0, 0, 1, 2, 1], [Uint8Array.of(12), Uint8Array.of(1), Uint8Array.of(2, 1)]);
const defaultDigest = checkDigest(new Uint8Array(6), [new Uint8Array(), new Uint8Array(), new Uint8Array()]);
const replacementDigest = checkDigest([12, 0, 0, 0, 1, 2], [Uint8Array.of(12), new Uint8Array(), Uint8Array.of(1, 2)]);

const checkTree = async (name, suffix) => {
  const tree = () => ledger(state)[name];
  const snapshot = () => {
    const { root, firstFree } = tree();
    return { root: root().field.toString(), firstFree: firstFree().toString() };
  };
  assert.deepEqual(snapshot(), { root: '0', firstFree: '0' });
  if (name === 'history') assert.deepEqual([...tree().history()], [{ field: 0n }]);

  await invoke(`append${suffix}`, leaf);
  const append = snapshot();
  assert.deepEqual(tree().pathForLeaf(0n, leaf)?.leaf, leaf);

  await invoke(`write${suffix}`, 3n, leaf);
  const indexedWrite = snapshot();
  assert.deepEqual(tree().pathForLeaf(3n, leaf)?.leaf, leaf);

  await invoke(`default${suffix}`, 0n);
  const indexedDefault = snapshot();
  assert.deepEqual(tree().pathForLeaf(0n, defaultLeaf)?.leaf, defaultLeaf);

  await assert.rejects(async () => invoke(`write${suffix}`, 4n, leaf));
  assert.deepEqual(snapshot(), indexedDefault);

  await invoke(`write${suffix}`, 3n, replacementLeaf);
  const indexedReplacement = snapshot();
  assert.deepEqual(tree().pathForLeaf(3n, replacementLeaf)?.leaf, replacementLeaf);
  assert.notEqual(indexedReplacement.root, indexedDefault.root);

  const steps = { append, indexedWrite, indexedDefault, indexedReplacement };
  assert.deepEqual(Object.values(steps).map(({ firstFree }) => firstFree), ['1', '4', '4', '4']);
  if (name === 'history') {
    const roots = Object.values(steps).map(({ root }) => root);
    assert.deepEqual([...tree().history()].map(({ field }) => field.toString()).sort(), ['0', ...roots].sort());
  }
  return steps;
};

const ordinary = await checkTree('ordinary', 'Ordinary');
const historic = await checkTree('history', 'Historic');
assert.deepEqual(historic, ordinary);
console.log(JSON.stringify({ leaf: leafDigest, defaultLeaf: defaultDigest, replacementLeaf: replacementDigest, ordinary, historic }));
