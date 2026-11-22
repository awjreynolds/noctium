import {createHash} from 'node:crypto';
import {readFile, writeFile} from 'node:fs/promises';
import {pathToFileURL} from 'node:url';
import {resolve, dirname, join} from 'node:path';

const mode = process.argv[2];
const ledgerPath = process.argv[3];
if (!mode || !ledgerPath) throw Error('usage: prepare LEDGER_MODULE OUTPUT_JSON | compare LEDGER_MODULE CHECKER PLAN CALL FIXTURE');
const ledgerUrl = pathToFileURL(resolve(ledgerPath));
const ledger = await import(ledgerUrl.href);

const atom = {tag: 'atom', value: {tag: 'field'}};
const field = n => ({value: ledger.bigIntToValue(n), alignment: [atom]});
const bit = value => ({value: [value ? Uint8Array.of(1) : new Uint8Array()],
  alignment: [{tag: 'atom', value: {tag: 'bytes', length: 1}}]});
const empty = {value: [], alignment: []};
const hash = values => ledger.valueToBigInt(
  ledger.transientHash(values.map(() => atom), values.flatMap(ledger.bigIntToValue)));

function fixture() {
  const secret = 42n, campaign = 9n, sibling0 = 17n, sibling1 = 23n;
  const leaf = hash([1n, secret, campaign]);
  const node = hash([2n, leaf, sibling0]);
  const root = hash([2n, sibling1, node]);
  const nullifier = hash([3n, secret, campaign]);
  return {secret: String(secret), campaign: String(campaign), sibling0: String(sibling0),
    sibling1: String(sibling1), leaf: String(leaf), node: String(node), root: String(root),
    nullifier: String(nullifier), direction0: 0, direction1: 1, unrelatedKey: '333'};
}

if (mode === 'prepare') {
  const output = process.argv[4];
  if (!output || process.argv.length !== 5) throw Error('usage: prepare LEDGER_MODULE OUTPUT_JSON');
  await writeFile(output, JSON.stringify(fixture()));
  process.exit(0);
}
if (mode !== 'compare' || process.argv.length !== 8)
  throw Error('usage: compare LEDGER_MODULE OFFICIAL_321_CHECKER PLAN CALL FIXTURE');

const checkerPath = resolve(process.argv[4]);
const planPath = resolve(process.argv[5]);
const callPath = resolve(process.argv[6]);
const fixturePath = resolve(process.argv[7]);

const redact = (boundary, step, fieldName) => ({boundary, step, field: fieldName});
const fail = (classification, divergence) => {
  process.stdout.write(JSON.stringify({status: 'failed', classification, firstDivergence: divergence}) + '\n');
  process.exit(2);
};
const firstTraceDifference = (expected, actual, boundary) => {
  const count = Math.max(expected.length, actual.length);
  for (let i = 0; i < count; i++) {
    if (i >= expected.length || i >= actual.length)
      return redact(boundary, i + 1, 'trace.length');
    for (const key of ['boundary', 'field', 'outcome', 'value', 'key']) {
      if (expected[i][key] !== actual[i][key])
        return redact(actual[i].boundary || expected[i].boundary || boundary, i + 1,
          key === 'value' || key === 'key' ? expected[i].field : key);
    }
  }
  return null;
};
const firstObjectDifference = (expected, actual, boundary, step = 1, prefix = '') => {
  if (Object.is(expected, actual)) return null;
  if (expected === null || actual === null || typeof expected !== 'object' || typeof actual !== 'object')
    return redact(boundary, step, prefix || 'value');
  if (Array.isArray(expected) || Array.isArray(actual)) {
    if (!Array.isArray(expected) || !Array.isArray(actual)) return redact(boundary, step, prefix || 'shape');
    const count = Math.max(expected.length, actual.length);
    for (let i = 0; i < count; i++) {
      if (i >= expected.length || i >= actual.length) return redact(boundary, step, `${prefix}[${i}]`);
      const difference = firstObjectDifference(expected[i], actual[i], boundary, i + 1, `${prefix}[${i}]`);
      if (difference) return difference;
    }
    return null;
  }
  const keys = [...new Set([...Object.keys(expected), ...Object.keys(actual)])].sort();
  for (const key of keys) {
    if (!(key in expected) || !(key in actual)) return redact(boundary, step, prefix ? `${prefix}.${key}` : key);
    const difference = firstObjectDifference(expected[key], actual[key], boundary, step,
      prefix ? `${prefix}.${key}` : key);
    if (difference) return difference;
  }
  return null;
};

let planBytes, callBytes, fixtureInput;
try {
  [planBytes, callBytes] = await Promise.all([readFile(planPath), readFile(callPath)]);
  fixtureInput = JSON.parse(await readFile(fixturePath, 'utf8'));
} catch {
  fail('infrastructure-failure', redact('native-sample-input', 1, 'artifact-or-fixture-read'));
}

let plan, circuit;
try {
  plan = JSON.parse(planBytes);
  circuit = JSON.parse(callBytes);
} catch {
  fail('candidate-difference', redact('artifact-decode', 1, 'plan-or-call-json'));
}

let Zkir, check;
try {
  ({Zkir, check} = await import(pathToFileURL(checkerPath).href));
} catch {
  fail('infrastructure-failure', redact('zkir-checker-load', 1, 'official-module'));
}

let relation;
try {
  relation = Zkir.fromJson(JSON.stringify(circuit));
} catch {
  fail('candidate-difference', redact('native-call-decode', 1, 'zkir-call'));
}

const n = Object.fromEntries(['secret', 'campaign', 'sibling0', 'sibling1', 'leaf', 'node', 'root', 'nullifier', 'unrelatedKey']
  .map(key => [key, BigInt(fixtureInput[key])]));
if (plan.operations?.length !== 21 || circuit.instructions?.length !== 55)
  fail('candidate-difference', redact('artifact-shape', 1, 'operation-or-instruction-count'));
if (circuit.do_communications_commitment !== true)
  fail('candidate-difference', redact('native-call', 1, 'communications-commitment'));

const env = {root: n.root, campaign: n.campaign, suppliedNullifier: n.nullifier,
  nullifier: n.nullifier, storedRoot: n.root, storedCampaign: n.campaign};
function expression(e) {
  switch (e.tag) {
    case 'reference': if (e.name in env) return env[e.name]; break;
    case 'constant': if (typeof e.value === 'string' && /^\d+$/.test(e.value)) return BigInt(e.value); break;
    case 'bool': if (typeof e.value === 'boolean') return e.value ? 1n : 0n; break;
    case 'select': return expression(expression(e.condition) ? e.yes : e.no);
  }
  fail('candidate-difference', redact('impact-expression', 1, 'unsupported-expression'));
}
const aligned = op => op.alignment === 'field' ? field(expression(op.expression)) :
  op.alignment === 'bit' ? bit(Boolean(expression(op.expression))) :
  fail('candidate-difference', redact('impact-alignment', 1, 'alignment'));
let operations;
try {
  operations = plan.operations.map(op => {
    switch (op.op) {
      case 'push': return {push: {storage: op.storage, value: {tag: 'cell', content: aligned(op)}}};
      case 'popeq': return {popeq: {cached: false, result: aligned(op)}};
      case 'dup': return {dup: {n: 0}};
      case 'index': return {idx: {cached: false, pushPath: op.pushPath,
        path: [{tag: 'value', value: field(BigInt(op.slot))}]}};
      case 'member': return 'member';
      case 'insert': return {ins: {cached: false, n: op.n}};
      default: fail('candidate-difference', redact('impact-plan', 1, 'unsupported-operation'));
    }
  });
} catch {
  fail('candidate-difference', redact('impact-plan', 1, 'operation-conversion'));
}

const provider = {lookupKey: async () => ({ir: relation.serialize(), proverKey: new Uint8Array(), verifierKey: new Uint8Array()})};
const preimage = ops => ledger.proofDataIntoSerializedPreimage(empty, empty, ops,
  [n.secret, n.sibling0, n.sibling1, BigInt(fixtureInput.direction0), BigInt(fixtureInput.direction1)].map(field),
  'noctium/state-preservation');
let activity;
try {
  activity = await check(preimage(operations), provider);
} catch {
  fail('checker-rejection', redact('zkir-assignment-check', 1, 'accepted-fixture'));
}
if (activity.length !== 21 || !activity.every(group => group === undefined || group === null))
  fail('checker-rejection', redact('zkir-assignment-check', 1, 'active-impact-groups'));
const wrongExpectedRead = operations.map(op => op);
const wrongReadValue = n.root !== n.campaign ? n.campaign : n.root === 0n ? 1n : 0n;
wrongExpectedRead[8] = {popeq: {cached: false, result: field(wrongReadValue)}};
let checkerRejectionControl = false;
try {
  await check(preimage(wrongExpectedRead), provider);
} catch {
  checkerRejectionControl = true;
}
if (!checkerRejectionControl)
  fail('candidate-difference', redact('zkir-checker-control', 1, 'wrong-expected-read'));

const cost = ledger.CostModel.initialCostModel();
function context(entries = []) {
  let map = new ledger.StateMap();
  for (const [key, value] of entries)
    map = map.insert(field(key), ledger.StateValue.newCell(field(value)));
  let state = ledger.StateValue.newArray();
  state = state.arrayPush(ledger.StateValue.newCell(field(n.root)));
  state = state.arrayPush(ledger.StateValue.newCell(field(n.campaign)));
  state = state.arrayPush(ledger.StateValue.newMap(map));
  return new ledger.QueryContext(new ledger.ChargedState(state), ledger.dummyContractAddress());
}
function projected(ctx) {
  const slots = ctx.state.state.asArray();
  const map = slots[2].asMap();
  const read = key => map.get(field(key));
  const asField = value => value === undefined ? undefined : ledger.valueToBigInt(value.asCell().value);
  return {
    acceptedRoot: ledger.valueToBigInt(slots[0].asCell().value),
    campaignId: ledger.valueToBigInt(slots[1].asCell().value),
    consumedNullifier: asField(read(n.nullifier)),
    unrelatedEntry: asField(read(n.unrelatedKey)),
  };
}

const initial = context([[n.unrelatedKey, 1n]]);
const initialProjection = projected(initial);
const gather = operations.map(op => op.popeq ? {popeq: {...op.popeq, result: null}} : op);
let observed;
try {
  observed = initial.query(gather, cost);
} catch {
  fail('candidate-difference', redact('native-query', 1, 'plan-execution'));
}
const reads = observed.events.filter(event => event.tag === 'read').map(event => ledger.valueToBigInt(event.content.value));
const expectedReads = [n.root, n.campaign, n.nullifier, n.root, n.campaign, 0n];
for (let index = 0; index < expectedReads.length; index++)
  if (reads[index] !== expectedReads[index])
    fail('candidate-difference', redact('native-query', index + 1, `read[${index}]`));
if (reads.length !== expectedReads.length)
  fail('candidate-difference', redact('native-query', reads.length + 1, 'read.length'));

const transcript = {gas: observed.gasCost, effects: observed.context.effects, program: operations};
let accepted;
try {
  accepted = initial.runTranscript(transcript, cost);
} catch {
  fail('candidate-difference', redact('native-acceptance', 1, 'accepted-transcript'));
}
const acceptedProjection = projected(accepted);
const expectedProjection = {acceptedRoot: n.root, campaignId: n.campaign,
  consumedNullifier: 1n, unrelatedEntry: 1n};
const stateDifference = firstObjectDifference(expectedProjection, acceptedProjection, 'accepted-state');
if (stateDifference) fail('candidate-difference', stateDifference);
const initialAfterAcceptance = projected(initial);
const initialDifference = firstObjectDifference(initialProjection, initialAfterAcceptance, 'initial-state');
if (initialDifference) fail('candidate-difference', initialDifference);

const sourceTrace = [
  {step: 1, boundary: 'claim-result', field: 'outputs.nullifier', outcome: 'returned', value: n.nullifier},
  {step: 2, boundary: 'claim-effect', field: 'acceptedRoot', outcome: 'read-equal', value: n.root},
  {step: 3, boundary: 'claim-effect', field: 'campaignId', outcome: 'read-equal', value: n.campaign},
  {step: 4, boundary: 'claim-effect', field: 'spent[nullifier]', outcome: 'absent', value: 'absent'},
  {step: 5, boundary: 'claim-effect', field: 'spent[nullifier]', outcome: 'write-true', key: n.nullifier, value: 1n},
];
const nativeTrace = [
  {step: 1, boundary: 'claim-result', field: 'outputs.nullifier', outcome: 'returned', value: reads[2]},
  {step: 2, boundary: 'claim-effect', field: 'acceptedRoot', outcome: 'read-equal', value: reads[3]},
  {step: 3, boundary: 'claim-effect', field: 'campaignId', outcome: 'read-equal', value: reads[4]},
  {step: 4, boundary: 'claim-effect', field: 'spent[nullifier]', outcome: reads[5] === 0n ? 'absent' : 'present',
    value: reads[5] === 0n ? 'absent' : 'present'},
  {step: 5, boundary: 'claim-effect', field: 'spent[nullifier]', outcome: 'write-true',
    key: operations[18]?.push ? n.nullifier : undefined, value: acceptedProjection.consumedNullifier},
];
const traceDifference = firstTraceDifference(sourceTrace, nativeTrace, 'claim-trace');
if (traceDifference) fail('candidate-difference', traceDifference);

const replayPrior = projected(accepted);
let nativeReplayRejected = false;
let replayFailure = null;
try {
  accepted.runTranscript(transcript, cost);
} catch (error) {
  nativeReplayRejected = true;
  replayFailure = {name: error?.name || 'unknown', message: String(error?.message || error)
    .replace(/0x[0-9a-f]+/gi, '<hex>').replace(/\d{8,}/g, '<scalar>')};
}
const replayAfter = projected(accepted);
const replayStateDifference = firstObjectDifference(replayPrior, replayAfter, 'replay-state');
if (!nativeReplayRejected)
  fail('candidate-difference', redact('replay', 1, 'status'));
const expectedReadMismatch = replayFailure?.message.startsWith('mismatch between expected (') &&
  replayFailure.message.endsWith(' read');
if (!expectedReadMismatch)
  fail('candidate-difference', redact('replay', 1, 'ledger-rejection-reason'));
if (replayStateDifference) fail('candidate-difference', replayStateDifference);

const actualReplay = {status: 'rejected', state: replayAfter};
const changedExpectedReplay = {status: 'accepted', state: replayPrior};
const replayControlDifference = firstObjectDifference(changedExpectedReplay, actualReplay, 'replay');
if (!replayControlDifference || replayControlDifference.field !== 'status')
  fail('candidate-difference', redact('replay-control', 1, 'expected-status-sensitivity'));

const checkerPackage = JSON.parse(await readFile(join(dirname(checkerPath), 'package.json'), 'utf8'));
const ledgerPackage = JSON.parse(await readFile(join(dirname(ledgerPath), 'package.json'), 'utf8'));
process.stdout.write(JSON.stringify({
  status: 'passed',
  classification: 'candidate-match',
  nativeChecker: {packageVersion: checkerPackage.version, wasmSha256: createHash('sha256').update(await readFile(join(dirname(checkerPath), 'midnight_zkir_wasm_bg.wasm'))).digest('hex'),
    assignmentAccepted: true, activeImpactGroups: activity.length,
    wrongExpectedReadRejected: checkerRejectionControl},
  ledger: {packageVersion: ledgerPackage.version, stateQueryExecuted: true, transcriptApplied: true},
  artifact: {planSha256: createHash('sha256').update(planBytes).digest('hex'), callSha256: createHash('sha256').update(callBytes).digest('hex')},
  sourceVsNative: {traceSteps: sourceTrace.length, tracesEqual: true, publicOutputEqual: true, projectedStateEqual: true,
    nativeReturnBoundary: 'supplied-nullifier echo; the native call Output vector is empty'},
  acceptedState: {configuredCellsPreserved: true, nullifierInsertedTrue: true, unrelatedEntryPreserved: true, initialStatePreserved: true},
  replay: {sourceExpectedRejected: true, nativeRejected: nativeReplayRejected, acceptedStatePreservedAfterRejection: true,
    changedExpectedResultDetected: true, controlDivergence: replayControlDifference,
    rejectionKind: 'expected-ledger-read-mismatch'},
  witnessValuesReported: false,
}, null, 2) + '\n');
