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
const routeSource = join(scratch, 'RouteForwarder.compact');
const routeOutput = join(scratch, 'RouteForwarder');
const listSource = join(scratch, 'ForwarderList.compact');
const listOutput = join(scratch, 'ForwarderList');
const routeListSource = join(scratch, 'RouteForwarderList.compact');
const routeListOutput = join(scratch, 'RouteForwarderList');
const echoCallerSource = join(scratch, 'TypedRefEchoCaller.compact');
const echoCallerOutput = join(scratch, 'TypedRefEchoCaller');
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
  const scalarLedger = contractInfo.ledger.find(({name}) => name === 'target');
  assert.equal(scalarLedger?.storage, 'Cell');
  assert.equal(scalarLedger?.type['type-name'], 'Contract');
  const routeMapLedger = contractInfo.ledger.find(({name}) => name === 'routes');
  assert.equal(routeMapLedger?.storage, 'Map');
  assert.equal(routeMapLedger?.value['type-name'], 'Struct');
  assert.equal(routeMapLedger?.value.name, 'Route');
  const routeListMapLedger = contractInfo.ledger.find(({name}) => name === 'routeLists');
  assert.equal(routeListMapLedger?.storage, 'Map');
  assert.equal(routeListMapLedger?.value['type-name'], 'List');
  assert.equal(routeListMapLedger?.value.type['type-name'], 'Struct');
  assert.equal(routeListMapLedger?.value.type.name, 'Route');
  const echoCircuit = contractInfo.circuits.find(({name}) => name === 'echo');
  assert.equal(echoCircuit?.arguments[0]?.type['type-name'], 'Contract');
  assert.equal(echoCircuit?.arguments[0]?.type.name, 'TypedRefValue');
  assert.equal(echoCircuit?.['result-type']?.['type-name'], 'Contract');
  assert.equal(echoCircuit?.['result-type']?.name, 'TypedRefValue');

  await writeFile(routeSource, `pragma language_version 0.28;
import CompactStandardLibrary;
contract TypedRefUpdate { circuit update(amount: Uint<8>): Uint<8>; }
struct Route { target: TypedRefUpdate, enabled: Boolean }
export ledger route: Route;
constructor(targetRef: TypedRefUpdate) {
  route = disclose(Route{target: disclose(targetRef), enabled: disclose(true)});
}
export circuit forward(amount: Uint<8>): Uint<8> {
  if (route.enabled) { return route.target.update(disclose(amount)); }
  return 0 as Uint<8>;
}
`);
  execFileSync(compactc, ['--compact-path', scratch, routeSource, routeOutput], {encoding: 'utf8'});
  const routeInfo = JSON.parse(await readFile(join(routeOutput, 'compiler/contract-info.json'), 'utf8'));
  const routeLedgerInfo = routeInfo.ledger.find(({name}) => name === 'route');
  assert.equal(routeLedgerInfo?.storage, 'Cell');
  assert.equal(routeLedgerInfo?.type['type-name'], 'Struct');
  assert.equal(routeLedgerInfo?.type.name, 'Route');

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

  await writeFile(routeListSource, `pragma language_version 0.28;
import CompactStandardLibrary;
contract TypedRefUpdate { circuit update(amount: Uint<8>): Uint<8>; }
struct Route { target: TypedRefUpdate, enabled: Boolean }
export ledger targets: List<Route>;
constructor(targetRef: TypedRefUpdate) {
  targets.pushFront(disclose(Route{target: disclose(targetRef), enabled: disclose(true)}));
}
export circuit forward(amount: Uint<8>): Uint<8> {
  const route = targets.head();
  assert(route.is_some, "missing route");
  if (route.value.enabled) {
    return route.value.target.update(disclose(amount));
  }
  return 0 as Uint<8>;
}
`);
  execFileSync(compactc, ['--compact-path', scratch, routeListSource, routeListOutput], {encoding: 'utf8'});

  await writeFile(echoCallerSource, `pragma language_version 0.28;
import CompactStandardLibrary;
contract TypedRefValue { circuit inspect(): Uint<8>; }
contract TypedRefEcho { circuit echo(value: TypedRefValue): TypedRefValue; }
export ledger echoer: TypedRefEcho;
constructor(initial: TypedRefEcho) { echoer = disclose(initial); }
export circuit roundTrip(value: TypedRefValue): TypedRefValue {
  return echoer.echo(disclose(value));
}
`);
  execFileSync(compactc, ['--compact-path', scratch, echoCallerSource, echoCallerOutput], {encoding: 'utf8'});

  const compileRejected = async (name, source, expected) => {
    const sourcePath = join(scratch, `${name}.compact`);
    const outputPath = join(scratch, name);
    await writeFile(sourcePath, source);
    let error;
    try {
      execFileSync(compactc, ['--skip-zk', sourcePath, outputPath], {encoding: 'utf8'});
    } catch (caught) {
      error = caught;
    }
    assert.ok(error && error.status !== 0, `${name} unexpectedly compiled`);
    const diagnostic = `${error.stdout ?? ''}${error.stderr ?? ''}`;
    assert.match(diagnostic, expected, `${name} diagnostic`);
  };
  await compileRejected('WrongRefArgument', `pragma language_version 0.28;
import CompactStandardLibrary;
contract TypedRefValue { circuit inspect(): Uint<8>; }
contract OtherRef { circuit inspect(): Uint<8>; }
contract TypedRefEcho { circuit echo(value: TypedRefValue): TypedRefValue; }
export ledger echoer: TypedRefEcho;
constructor(initial: TypedRefEcho) { echoer = disclose(initial); }
export circuit roundTrip(value: OtherRef): TypedRefValue {
  return echoer.echo(disclose(value));
}
`, /expected first argument of TypedRefEcho\.echo to have type contract TypedRefValue/);
  await compileRejected('RawBytesRefArgument', `pragma language_version 0.28;
import CompactStandardLibrary;
contract TypedRefValue { circuit inspect(): Uint<8>; }
contract TypedRefEcho { circuit echo(value: TypedRefValue): TypedRefValue; }
export ledger echoer: TypedRefEcho;
constructor(initial: TypedRefEcho) { echoer = disclose(initial); }
export circuit roundTrip(value: Bytes<32>): TypedRefValue {
  return echoer.echo(disclose(value));
}
`, /expected first argument of TypedRefEcho\.echo to have type contract TypedRefValue/);
  await compileRejected('WrongRefReturnImplementation', `pragma language_version 0.28;
import CompactStandardLibrary;
contract TypedRefValue { circuit inspect(): Uint<8>; }
contract OtherRef { circuit inspect(): Uint<8>; }
contract TypedRefEcho { circuit echo(value: TypedRefValue): TypedRefValue; }
contract implements TypedRefEcho;
export ledger result: OtherRef;
constructor(initial: OtherRef) { result = disclose(initial); }
export circuit echo(value: TypedRefValue): OtherRef {
  return result;
}
`, /its return type is contract OtherRef[\s\S]*rather than contract\s+TypedRefValue/);
  await compileRejected('WrongNominalRouteReference', `pragma language_version 0.28;
import CompactStandardLibrary;
contract TypedRefUpdate { circuit update(amount: Uint<8>): Uint<8>; }
contract OtherRef { circuit update(amount: Uint<8>): Uint<8>; }
struct Route { target: TypedRefUpdate, enabled: Boolean }
export ledger routes: Map<Bytes<32>, Route>;
constructor(targetRef: OtherRef) {
  routes.insert(disclose(0 as Bytes<32>), disclose(Route{target: disclose(targetRef), enabled: disclose(true)}));
}
export circuit forward(key: Bytes<32>, amount: Uint<8>): Uint<8> {
  return routes.lookup(disclose(key)).target.update(disclose(amount));
}
`, /mismatch between actual type contract OtherRef[\s\S]*declared type\s+contract TypedRefUpdate[\s\S]*field target of struct Route/);

  for (const output of [calleeOutput, callerOutput, routeOutput, listOutput, routeListOutput, echoCallerOutput]) {
    const scopedRuntime = join(output, 'node_modules/@midnight-ntwrk/compact-runtime');
    await mkdir(dirname(scopedRuntime), {recursive: true});
    await symlink(runtimeDirectory, scopedRuntime, 'dir');
  }
  const {Contract: TypedRefUpdate} = await import(pathToFileURL(join(calleeOutput, 'contract/index.js')).href);
  const {Contract: Forwarder, ledger} = await import(pathToFileURL(join(callerOutput, 'contract/index.js')).href);
  const {Contract: RouteForwarder, ledger: routeLedger} = await import(pathToFileURL(join(routeOutput, 'contract/index.js')).href);
  const {Contract: ListForwarder, ledger: listLedger} = await import(pathToFileURL(join(listOutput, 'contract/index.js')).href);
  const {Contract: RouteListForwarder, ledger: routeListLedger} = await import(pathToFileURL(join(routeListOutput, 'contract/index.js')).href);
  const {Contract: EchoCaller} = await import(pathToFileURL(join(echoCallerOutput, 'contract/index.js')).href);
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
  const routeKey = new Uint8Array(32);
  const mappedRoute = ledger(callerState.currentContractState.data).routes.lookup(routeKey);
  assert.deepEqual(mappedRoute.target.bytes, reference.bytes);
  assert.equal(mappedRoute.enabled, true);
  const mappedRouteList = ledger(callerState.currentContractState.data).routeLists.lookup(routeKey);
  assert.deepEqual(mappedRouteList.head().value.target.bytes, reference.bytes);
  assert.equal(mappedRouteList.head().value.enabled, true);

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
  const {result: scalarCellResult} = await forwarder.circuits.forward(contextFor(callerState.currentContractState.data), 7n);
  assert.equal(scalarCellResult, 7n);
  const {result: mappedRouteResult} = await forwarder.circuits.forwardRoute(
    contextFor(callerState.currentContractState.data), routeKey, 7n,
  );
  assert.equal(mappedRouteResult, 7n);
  const {result: mappedRouteListResult} = await forwarder.circuits.forwardRouteList(
    contextFor(callerState.currentContractState.data), routeKey, 7n,
  );
  assert.equal(mappedRouteListResult, 7n);

  const routeForwarder = new RouteForwarder({});
  const routeState = await routeForwarder.initialState(runtime.createConstructorContext(null, key), reference);
  const route = routeLedger(routeState.currentContractState.data).route;
  assert.deepEqual(route.target.bytes, reference.bytes);
  assert.equal(route.enabled, true);
  const {result: routeCellResult} = await routeForwarder.circuits.forward(contextFor(routeState.currentContractState.data), 7n);
  assert.equal(routeCellResult, 7n);

  const listForwarder = new ListForwarder({});
  const listState = await listForwarder.initialState(runtime.createConstructorContext(null, key), reference);
  assert.deepEqual(listLedger(listState.currentContractState.data).targets.head().value.bytes, reference.bytes);
  const {result: scalarListResult} = await listForwarder.circuits.forward(contextFor(listState.currentContractState.data), 7n);
  assert.equal(scalarListResult, 7n);

  const routeListForwarder = new RouteListForwarder({});
  const routeListState = await routeListForwarder.initialState(runtime.createConstructorContext(null, key), reference);
  const listedRoute = routeListLedger(routeListState.currentContractState.data).targets.head().value;
  assert.deepEqual(listedRoute.target.bytes, reference.bytes);
  assert.equal(listedRoute.enabled, true);
  const {result: routeListResult} = await routeListForwarder.circuits.forward(contextFor(routeListState.currentContractState.data), 7n);
  assert.equal(routeListResult, 7n);

  const echoService = new Forwarder({});
  const echoServiceState = await echoService.initialState(runtime.createConstructorContext(null, key), reference);
  const echoVerifierKey = Uint8Array.from(await readFile(join(callerOutput, 'keys/echo.verifier')));
  const echoOperation = new runtime.ContractOperation();
  echoOperation.verifierKey = echoVerifierKey;
  echoServiceState.currentContractState.setOperation('echo', echoOperation);
  const echoServiceReference = {
    bytes: Uint8Array.from(Buffer.from(runtime.sampleContractAddress(), 'hex')),
  };
  const echoCaller = new EchoCaller({});
  const echoCallerState = await echoCaller.initialState(
    runtime.createConstructorContext(null, key), echoServiceReference,
  );
  const echoCrossContract = {
    stateProvider: {async getContractState() { return echoServiceState.currentContractState; }},
    moduleProvider: {
      resolve() {
        return async () => import(pathToFileURL(join(callerOutput, 'contract/index.js')).href);
      },
    },
  };
  const echoContext = runtime.createCircuitContext({
    circuitId: 'roundTrip',
    contractAddress: runtime.sampleContractAddress(),
    coinPublicKeyOrZswapState: key,
    contractState: echoCallerState.currentContractState.data,
    privateState: null,
    parentBlockHash: '00'.repeat(32),
    crossContract: echoCrossContract,
  });
  const valueReference = {
    bytes: Uint8Array.from(Buffer.from(runtime.sampleContractAddress(), 'hex')),
  };
  const {result: echoedReference} = await echoCaller.circuits.roundTrip(echoContext, valueReference);
  assert.deepEqual(echoedReference.bytes, valueReference.bytes);
  console.log(`Compact ${compilerVersion} / runtime ${runtimePackage.version}: scalar Cell, Map<Bytes<32>, Route>, Map<Bytes<32>, List<Route>>, scalar List, Route Cell, List<Route>, and interface argument/result references round-tripped; compile-time mismatch cases were rejected`);
} finally {
  await rm(scratch, {recursive: true, force: true});
  try {
    await rmdir(experiments);
  } catch {
    // Keep the shared experiments directory when another task uses it.
  }
}
