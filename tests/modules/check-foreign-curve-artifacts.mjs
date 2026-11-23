import assert from 'node:assert/strict';
import {existsSync, readFileSync} from 'node:fs';
import {join, resolve} from 'node:path';

const [outputDirectory] = process.argv.slice(2);
assert.ok(outputDirectory, 'pass the Noctium artifact output directory');
const output = resolve(outputDirectory);
const moduleManifest = JSON.parse(readFileSync(join(output, 'noctium.json'), 'utf8'));
const contractName = 'ForeignCurveGenericIdentity';
const expectedTypes = [
  'Secp256k1Base', 'Secp256k1Scalar', 'Secp256k1Point',
  'Secp256r1Base', 'Secp256r1Scalar', 'Secp256r1Point',
  'Curve25519Base', 'Curve25519Scalar', 'Curve25519Point',
];
const contract = moduleManifest.contracts.find(entry => entry.name === contractName);
assert.ok(contract, `missing ${contractName} in the Noctium manifest`);
assert.equal(contract.entrypoints.length, expectedTypes.length);
assert.equal(contract.state.length, 1, 'the POC declares one concrete scalar result cell');
const resultCell = contract.state[0];
assert.equal(resultCell.kind.cell, 'Secp256k1Scalar');

const artifacts = [];
for (const type of expectedTypes) {
  const name = `${type[0].toLowerCase()}${type.slice(1)}Identity`;
  const nativeStem = `${contractName}.${name}`;
  const impactPath = join(output, `${nativeStem}.impact.json`);
  assert.ok(existsSync(impactPath), `missing native impact artifact ${nativeStem}`);
  const plan = JSON.parse(readFileSync(impactPath, 'utf8'));
  assert.equal(plan.contractName, contractName);
  assert.equal(plan.entrypoint, name);
  assert.deepEqual(plan.state, contract.state);
  assert.equal(plan.circuit.inputs.length, 1);
  assert.deepEqual(
    {name: plan.circuit.inputs[0].name, type: plan.circuit.inputs[0].type},
    {name: 'value', type},
  );
  assert.equal(plan.circuit.outputs.length, 1);
  assert.deepEqual(
    {name: plan.circuit.outputs[0].name, type: plan.circuit.outputs[0].type},
    {name: 'result', type},
  );

  const moduleCircuit = moduleManifest.circuits.find(item =>
    item.name.endsWith(`.${plan.circuit.name}`));
  assert.ok(moduleCircuit, `missing circuit manifest entry for ${plan.circuit.name}`);
  const signaturePath = join(output, `${moduleCircuit.name}.specialization.json`);
  assert.ok(existsSync(signaturePath), `missing specialization signature ${moduleCircuit.name}`);
  const signature = JSON.parse(readFileSync(signaturePath, 'utf8'));
  assert.equal(signature.sourceExport, 'identity');
  const typedResults = signature.declarations.map(declaration => ({
    argument: declaration.arguments[0]?.type?.value?.foreign?.sourceName,
    parameter: declaration.parameters[0]?.type?.foreign?.sourceName,
    result: declaration.result?.foreign?.sourceName,
  }));
  assert.ok(typedResults.some(value =>
    value.argument === type && value.parameter === type && value.result === type),
  `missing foreign signature sidecar types for ${type}`);
  assert.ok(existsSync(join(output, `${moduleCircuit.name}.zkir`)),
    `missing emitted ZKIR relation ${moduleCircuit.name}`);
  const entrypoint = contract.entrypoints.find(item => item.name === name);
  if (name === 'secp256k1ScalarIdentity') {
    assert.deepEqual(entrypoint.effects, [{state: resultCell.name, op: 'writeCell', value: {ref: 'result'}}]);
    assert.ok(plan.operations.some(operation => operation.storage === true &&
      operation.schema === 'Secp256k1Scalar'), 'scalar entrypoint did not write its typed result cell');
  } else {
    assert.deepEqual(entrypoint.effects, []);
    assert.ok(!plan.operations.some(operation => operation.storage === true),
      `${name} unexpectedly writes ledger state`);
  }
  artifacts.push({nativeStem, relation: plan.circuit.name, input: {name: 'value', type}});
}

console.log(JSON.stringify({fixture: contractName, state: resultCell, artifacts}));
