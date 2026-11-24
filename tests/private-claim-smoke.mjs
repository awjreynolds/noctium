import {readFileSync} from 'node:fs';
import {join} from 'node:path';
import {deepStrictEqual, equal, ok} from 'node:assert/strict';

const directory = process.argv[2];
if (!directory) throw Error('usage: node tests/private-claim-smoke.mjs ARTIFACT_DIRECTORY');

const readJson = (name) => {
  try {
    return JSON.parse(readFileSync(join(directory, name), 'utf8'));
  } catch (error) {
    if (error.code === 'ENOENT') throw Error(`missing ${name}`);
    throw error;
  }
};
const metadata = readJson('noctium.json');
const defaultProfile = JSON.parse(readFileSync(
  new URL('../profiles/midnight-ledger-9.json', import.meta.url), 'utf8'));
equal(metadata.target, defaultProfile.name, 'wrong target profile');
deepStrictEqual(metadata.targetProfile, defaultProfile, 'wrong target profile');

const contract = metadata.contracts.find((value) => value.name === 'PrivateClaim');
ok(contract, 'missing PrivateClaim contract');
deepStrictEqual(contract.entrypoints.map((value) => value.name), ['claim'], 'wrong operation');
const plan = readJson('PrivateClaim.claim.impact.json');
const circuit = readJson('PrivateClaim.claim.zkir');
equal(plan.contractName, 'PrivateClaim', 'wrong contract');
equal(plan.entrypoint, 'claim', 'wrong operation');
equal(plan.nativeCircuitFile, 'PrivateClaim.claim.zkir', 'wrong operation');

deepStrictEqual(plan.circuit.inputs.map(({name, type, visibility}) => [name, type, visibility]), [
  ['root', 'Native', 'public'],
  ['campaign', 'Native', 'public'],
  ['suppliedNullifier', 'Native', 'public'],
  ['secret', 'Native', 'private'],
  ['sibling0', 'Native', 'private'],
  ['sibling1', 'Native', 'private'],
  ['direction0', 'Bool', 'private'],
  ['direction1', 'Bool', 'private'],
]);
deepStrictEqual(plan.state.map(({name}) => name), ['acceptedRoot', 'campaignId', 'spent']);
ok(plan.operations.some(({op}) => op === 'member'), 'claim replay check is missing');
ok(plan.operations.some(({op}) => op === 'insert'), 'claim spent-state update is missing');
deepStrictEqual(plan.guards.length, 3, 'claim state guards changed');

deepStrictEqual(circuit.version, {minor: 2, major: 3});
const count = (op) => circuit.instructions.filter((instruction) => instruction.op === op).length;
equal(count('public_input'), 6, 'unexpected public transcript shape');
equal(count('private_input'), 5, 'unexpected private transcript shape');
equal(count('transient_hash'), 4, 'unexpected claim hash shape');
equal(circuit.do_communications_commitment, true, 'claim must bind communications');
equal(count('impact'), plan.operations.length, 'native Impact transcript length differs from the plan');
equal(count('output'), 1, 'unexpected circuit output shape');
equal(circuit.instructions.at(-1)?.op, 'output', 'circuit output is not final');

console.log('PrivateClaim default-profile compiler smoke passed');
