import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {
  createCircuitContext, createConstructorContext, dummyContractAddress,
} from '@midnight-ntwrk/compact-runtime';
import { Contract, ledger } from './compact/contract/index.js';

const contract = new Contract({});
const walletKey = '00'.repeat(32);
const { currentContractState } = await contract.initialState(createConstructorContext(null, walletKey));
let state = currentContractState.data;
const invoke = (entry, ...args) => contract.circuits[entry](createCircuitContext({
  circuitId: entry, contractAddress: dummyContractAddress(),
  coinPublicKeyOrZswapState: walletKey, contractState: state, privateState: null,
}), ...args);
const leaf = {tag: new Uint8Array([12, 0, 0]), details: [true, 258n, 0]};
const changed = {...leaf, details: [true, 259n, 0]};
const first = await invoke('append', leaf);
const ordinary = ledger(first.context.callContext.currentQueryContext.state).claims;
assert.deepEqual(ordinary.findPathForLeaf(leaf), ordinary.pathForLeaf(0n, leaf));
const firstInsert = {
  leafHash: createHash('sha256').update('mdn:lh').update(Buffer.from([12, 0, 0, 1, 2, 1, 0])).digest('hex'),
  root: ordinary.root().field.toString(),
};

const call = await invoke('setHistoricIndex', leaf);
state = call.context.callContext.currentQueryContext.state;
const tree = ledger(state).archives;
const found = tree.findPathForLeaf(leaf);
assert.ok(found);
assert.deepEqual(found, tree.pathForLeaf(3n, leaf));
assert.equal(tree.findPathForLeaf(changed), undefined);
const replacement = tree.pathForLeaf(3n, changed);
const snapshotRoot = tree.root().field;
const candidateDigest = (await invoke('typedPathRoot', replacement)).result;
const snapshotDigest = (await invoke('typedPathRoot', found)).result;
assert.equal(snapshotRoot,
  31400609395615079034746563944767363629115546679921774204850545210160415781421n);
assert.deepEqual(candidateDigest, {
  field: 31726889946271747810121760555431048011583312353587929966004038628449158629802n,
});
assert.deepEqual(snapshotDigest, {
  field: 31400609395615079034746563944767363629115546679921774204850545210160415781421n,
});
const candidateRoot = candidateDigest.field;
assert.notEqual(candidateRoot, snapshotRoot);
console.log(JSON.stringify({
  firstInsert,
  snapshotRoot: snapshotDigest.field.toString(),
  candidateRoot: candidateDigest.field.toString(),
  steps: replacement.path.map(({sibling, goes_left}) => ({
    sibling: sibling.field.toString(), goesLeft: goes_left,
  })),
}));
