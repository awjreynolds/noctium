import assert from 'node:assert/strict';
import {execFileSync} from 'node:child_process';
import {mkdir, mkdtemp, readFile, rm, symlink, rmdir, writeFile} from 'node:fs/promises';
import {dirname, join, resolve} from 'node:path';
import {fileURLToPath, pathToFileURL} from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node typed-contract-reference.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], {encoding: 'utf8'}).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/);
const runtimePackage = JSON.parse(await readFile(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');
const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(root, 'build/experiments');
await mkdir(experiments, {recursive: true});
const scratch = await mkdtemp(join(experiments, 'typed-contract-reference-'));
const fixture = fileURLToPath(new URL('./TypedContractReference.compact', import.meta.url));
const calleeSource = join(scratch, 'TypedRefUpdate.compact');
const calleeOutput = join(scratch, 'TypedRefUpdate');
const callerOutput = join(scratch, 'Forwarder');
const listSource = join(scratch, 'ForwarderList.compact');
const listOutput = join(scratch, 'ForwarderList');
try {
  await writeFile(calleeSource, `pragma language_version 0.28;
import CompactStandardLibrary;
contract TypedRefUpdate { circuit update(amount: Uint<8>): Uint<8>; }
contract implements TypedRefUpdate;
export ledger total: Uint<8>;
constructor() { total = 0 as Uint<8>; }
export circuit update(amount: Uint<8>): Uint<8> {
  total = disclose(amount);
  return total;
}
`);
  execFileSync(compactc, [calleeSource, calleeOutput], {encoding: 'utf8'});
  execFileSync(compactc, ['--compact-path', scratch, fixture, callerOutput], {encoding: 'utf8'});
  const contractInfo = JSON.parse(await readFile(join(callerOutput, 'compiler/contract-info.json'), 'utf8'));
  const targetLedger = contractInfo.ledger.find(({name}) => name === 'target');
  assert.equal(targetLedger?.storage, 'Cell');
  assert.equal(targetLedger?.type['type-name'], 'Contract');

  await writeFile(listSource, `pragma language_version 0.28;
import CompactStandardLibrary;
contract TypedRefUpdate { circuit update(amount: Uint<8>): Uint<8>; }
export ledger targets: List<TypedRefUpdate>;
constructor(targetRef: TypedRefUpdate) { targets.pushFront(disclose(targetRef)); }
export circuit forward(amount: Uint<8>): Uint<8> {
  const target = targets.head();
  assert(target.is_some, "missing target");
  return target.value.update(disclose(amount));
}
`);
  execFileSync(compactc, ['--compact-path', scratch, listSource, listOutput], {encoding: 'utf8'});

  for (const output of [calleeOutput, callerOutput, listOutput]) {
    const scopedRuntime = join(output, 'node_modules/@midnight-ntwrk/compact-runtime');
    await mkdir(dirname(scopedRuntime), {recursive: true});
    await symlink(runtimeDirectory, scopedRuntime, 'dir');
  }
  const {Contract: TypedRefUpdate} = await import(pathToFileURL(join(calleeOutput, 'contract/index.js')).href);
  const {Contract: Forwarder, ledger} = await import(pathToFileURL(join(callerOutput, 'contract/index.js')).href);
  const {Contract: ListForwarder, ledger: listLedger} = await import(pathToFileURL(join(listOutput, 'contract/index.js')).href);
  const key = '00'.repeat(32);
  const callee = new TypedRefUpdate({});
  const calleeState = await callee.initialState(runtime.createConstructorContext(null, key));
  const verifierKey = Uint8Array.from(await readFile(join(calleeOutput, 'keys/update.verifier')));
  const operation = new runtime.ContractOperation();
  operation.verifierKey = verifierKey;
  calleeState.currentContractState.setOperation('update', operation);

  const calleeAddress = runtime.sampleContractAddress();
  const reference = {bytes: Uint8Array.from(Buffer.from(calleeAddress, 'hex'))};
  const forwarder = new Forwarder({});
  const callerState = await forwarder.initialState(runtime.createConstructorContext(null, key), reference);
  assert.deepEqual(ledger(callerState.currentContractState.data).target.bytes, reference.bytes);

  const crossContract = {
    stateProvider: {async getContractState() { return calleeState.currentContractState; }},
    moduleProvider: {
      resolve() {
        return async () => import(pathToFileURL(join(calleeOutput, 'contract/index.js')).href);
      },
    },
  };
  const contextFor = (contractState) => runtime.createCircuitContext({
    circuitId: 'forward',
    contractAddress: runtime.sampleContractAddress(),
    coinPublicKeyOrZswapState: key,
    contractState,
    privateState: null,
    parentBlockHash: '00'.repeat(32),
    crossContract,
  });
  const {result} = await forwarder.circuits.forward(contextFor(callerState.currentContractState.data), 7n);
  assert.equal(result, 7n);

  const listForwarder = new ListForwarder({});
  const listState = await listForwarder.initialState(runtime.createConstructorContext(null, key), reference);
  assert.deepEqual(listLedger(listState.currentContractState.data).targets.head().value.bytes, reference.bytes);
  const {result: listResult} = await listForwarder.circuits.forward(contextFor(listState.currentContractState.data), 7n);
  assert.equal(listResult, 7n);
  console.log(`Compact ${compilerVersion} / runtime ${runtimePackage.version}: scalar Cell and List<TypedRefUpdate> references round-tripped; both forwarded update(7) and returned 7`);
} finally {
  await rm(scratch, {recursive: true, force: true});
  try {
    await rmdir(experiments);
  } catch {
    // Keep the shared experiments directory when another task uses it.
  }
}
