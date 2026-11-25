import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimePath, resultsPath] = process.argv.slice(2);
assert.ok(compactc && runtimePath && resultsPath,
  'usage: node tests/compact/nested-opaque-map.mjs <compactc-0.36.1> <compact-runtime-0.21.0> <results.json>');

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/, `unexpected Compact compiler: ${compilerVersion}`);
const runtimeDirectory = resolve(runtimePath);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, '1200-nested-opaque-map-'));

try {
  const generated = join(scratch, 'compact');
  const source = join(projectRoot, 'tests/compact/NestedOpaqueMap.compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtimeUrl = pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href;
  const contractUrl = pathToFileURL(join(generated, 'contract/index.js')).href;
  const { createCircuitContext, createConstructorContext, dummyContractAddress } = await import(runtimeUrl);
  const { Contract, ledger } = await import(contractUrl);
  const contract = new Contract({});
  const wallet = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(createConstructorContext(null, wallet));
  const ownerOne = new Uint8Array(32).fill(0x11);
  const ownerTwo = new Uint8Array(32).fill(0x22);
  const missingOwner = new Uint8Array(32).fill(0x33);
  const primaryKey = new Uint8Array(32).fill(0x44);
  const siblingKey = new Uint8Array(32).fill(0x55);
  const missingKey = new Uint8Array(32).fill(0x66);
  const groupOne = new Uint8Array(32).fill(0x77);
  const groupTwo = new Uint8Array(32).fill(0x88);
  const missingGroup = new Uint8Array(32).fill(0x99);
  const deepMissingKey = new Uint8Array(32).fill(0xaa);
  const invoke = async (state, name, ...args) => {
    const context = createCircuitContext({
      circuitId: name,
      contractAddress: dummyContractAddress(),
      coinPublicKeyOrZswapState: wallet,
      contractState: state,
      privateState: null,
    });
    const call = await contract.circuits[name](context, ...args);
    return [call.result, call.context.callContext.currentQueryContext.state];
  };
  const byteCases = [
    { name: 'ownerOneEmpty', owner: ownerOne, key: primaryKey, payload: new Uint8Array() },
    { name: 'ownerOneBinary', owner: ownerOne, key: siblingKey, payload: Uint8Array.of(0x00, 0x01, 0xff) },
    { name: 'ownerTwoSameKey', owner: ownerTwo, key: primaryKey, payload: Uint8Array.of(0x80, 0x00, 0xfe) },
  ];
  const stringCases = [
    { name: 'ownerOneText', owner: ownerOne, key: primaryKey, payload: 'A\0B' },
    { name: 'ownerOneSibling', owner: ownerOne, key: siblingKey, payload: 'λ' },
    { name: 'ownerTwoSameKey', owner: ownerTwo, key: primaryKey, payload: 'B\0C' },
  ];
  const deepStringCases = [
    { name: 'primary', owner: ownerOne, group: groupOne, key: primaryKey, payload: 'A\0λ雪' },
    { name: 'siblingGroup', owner: ownerOne, group: groupTwo, key: primaryKey, payload: 'group🌙' },
    { name: 'siblingOwner', owner: ownerTwo, group: groupOne, key: primaryKey, payload: 'owner🦊' },
  ];

  let state = currentContractState.data;
  for (const item of byteCases) {
    [, state] = await invoke(state, 'storeBytes', item.owner, item.key, item.payload);
    const bucket = ledger(state).byteBuckets.lookup(item.owner);
    assert.deepEqual(bucket.lookup(item.key), item.payload, `${item.name} bytes stay exact in the ledger`);
  }
  for (const item of stringCases) {
    [, state] = await invoke(state, 'storeString', item.owner, item.key, item.payload);
    const bucket = ledger(state).stringBuckets.lookup(item.owner);
    assert.equal(bucket.lookup(item.key), item.payload, `${item.name} string stays exact in the ledger`);
  }
  for (const item of deepStringCases) {
    [, state] = await invoke(state, 'storeDeepString', item.owner, item.group, item.key, item.payload);
    const bucket = ledger(state).deepStringBuckets.lookup(item.owner).lookup(item.group);
    assert.equal(bucket.lookup(item.key), item.payload, `${item.name} deep string stays exact in the ledger`);
  }

  let primaryBeforeOverwrite;
  [primaryBeforeOverwrite, state] = await invoke(
    state, 'readDeepString', ownerOne, groupOne, primaryKey,
  );
  assert.equal(primaryBeforeOverwrite, deepStringCases[0].payload,
    'deep string read preserves embedded NUL and multibyte characters');
  const overwrittenPayload = 'overwritten\0é';
  [, state] = await invoke(state, 'storeDeepString', ownerOne, groupOne, primaryKey, overwrittenPayload);
  assert.equal(
    ledger(state).deepStringBuckets.lookup(ownerOne).lookup(groupOne).lookup(primaryKey),
    overwrittenPayload,
    'deep string insertion overwrites the existing key',
  );

  const byteBuckets = ledger(state).byteBuckets;
  const stringBuckets = ledger(state).stringBuckets;
  const deepStringBuckets = ledger(state).deepStringBuckets;
  assert.equal(byteBuckets.size(), 2n, 'byte stores initialize one bucket per owner');
  assert.equal(stringBuckets.size(), 2n, 'string stores initialize one bucket per owner');
  assert.equal(byteBuckets.lookup(ownerOne).size(), 2n, 'byte sibling remains under the first owner');
  assert.equal(byteBuckets.lookup(ownerTwo).size(), 1n, 'same byte key stays separate under the second owner');
  assert.equal(stringBuckets.lookup(ownerOne).size(), 2n, 'string sibling remains under the first owner');
  assert.equal(stringBuckets.lookup(ownerTwo).size(), 1n, 'same string key stays separate under the second owner');
  assert.equal(deepStringBuckets.size(), 2n, 'deep string stores initialize one bucket per owner');
  assert.equal(deepStringBuckets.lookup(ownerOne).size(), 2n, 'deep string sibling group stays under the first owner');
  assert.equal(deepStringBuckets.lookup(ownerTwo).size(), 1n, 'deep string same group stays separate under the second owner');
  assert.equal(deepStringBuckets.lookup(ownerOne).lookup(groupOne).size(), 1n,
    'overwriting a deep string key does not add another entry');
  assert.equal(deepStringBuckets.lookup(ownerOne).lookup(groupTwo).size(), 1n,
    'same key remains separate under a sibling group');
  assert.equal(deepStringBuckets.lookup(ownerTwo).lookup(groupOne).size(), 1n,
    'same key remains separate under a sibling owner');

  const booleanResult = result => Array.isArray(result) ? result[0] : result;
  const bytePresence = {};
  for (const item of byteCases) {
    let result;
    [result, state] = await invoke(state, 'hasBytes', item.owner, item.key);
    assert.equal(booleanResult(result), true, `${item.name} byte key is present`);
    bytePresence[item.name] = booleanResult(result);
  }
  let missingBytes;
  [missingBytes, state] = await invoke(state, 'hasBytes', ownerOne, missingKey);
  assert.equal(booleanResult(missingBytes), false, 'missing byte child reports absent');
  bytePresence.missingKey = booleanResult(missingBytes);
  [missingBytes, state] = await invoke(state, 'hasBytes', missingOwner, primaryKey);
  assert.equal(booleanResult(missingBytes), false, 'missing byte owner reports absent');
  bytePresence.missingOwner = booleanResult(missingBytes);

  const stringPresence = {};
  for (const item of stringCases) {
    let result;
    [result, state] = await invoke(state, 'hasString', item.owner, item.key);
    assert.equal(booleanResult(result), true, `${item.name} string key is present`);
    stringPresence[item.name] = booleanResult(result);
  }
  let missingStrings;
  [missingStrings, state] = await invoke(state, 'hasString', ownerOne, missingKey);
  assert.equal(booleanResult(missingStrings), false, 'missing string child reports absent');
  stringPresence.missingKey = booleanResult(missingStrings);
  [missingStrings, state] = await invoke(state, 'hasString', missingOwner, primaryKey);
  assert.equal(booleanResult(missingStrings), false, 'missing string owner reports absent');
  stringPresence.missingOwner = booleanResult(missingStrings);

  const byteReads = {};
  for (const item of byteCases) {
    let result;
    [result, state] = await invoke(state, 'readBytes', item.owner, item.key);
    assert.deepEqual(result, item.payload, `${item.name} read preserves each byte`);
    byteReads[item.name] = Buffer.from(result).toString('hex');
  }
  const stringReads = {};
  for (const item of stringCases) {
    let result;
    [result, state] = await invoke(state, 'readString', item.owner, item.key);
    assert.equal(result, item.payload, `${item.name} read preserves exact string contents`);
    stringReads[item.name] = result;
  }
  const deepStringReads = { primaryBeforeOverwrite };
  for (const item of deepStringCases.slice(1)) {
    let result;
    [result, state] = await invoke(state, 'readDeepString', item.owner, item.group, item.key);
    assert.equal(result, item.payload, `${item.name} deep string reads from its independent path`);
    deepStringReads[item.name] = result;
  }
  let primaryAfterOverwrite;
  [primaryAfterOverwrite, state] = await invoke(
    state, 'readDeepString', ownerOne, groupOne, primaryKey,
  );
  assert.equal(primaryAfterOverwrite, overwrittenPayload, 'deep string read returns the overwritten value');
  deepStringReads.primaryAfterOverwrite = primaryAfterOverwrite;

  await assert.rejects(
    () => invoke(state, 'readBytes', ownerOne, missingKey),
    'direct read of a missing byte child rejects',
  );
  await assert.rejects(
    () => invoke(state, 'readBytes', missingOwner, primaryKey),
    'direct read under a missing byte owner rejects',
  );
  await assert.rejects(
    () => invoke(state, 'readString', ownerOne, missingKey),
    'direct read of a missing string child rejects',
  );
  await assert.rejects(
    () => invoke(state, 'readString', missingOwner, primaryKey),
    'direct read under a missing string owner rejects',
  );
  await assert.rejects(
    () => invoke(state, 'readDeepString', ownerOne, groupOne, deepMissingKey),
    'direct read of a missing deep string child rejects',
  );
  await assert.rejects(
    () => invoke(state, 'readDeepString', ownerOne, missingGroup, primaryKey),
    'direct read under a missing deep string group rejects',
  );
  await assert.rejects(
    () => invoke(state, 'readDeepString', missingOwner, groupOne, primaryKey),
    'direct read under a missing deep string owner rejects',
  );

  const reference = {
    compact: compilerVersion,
    runtime: runtimePackage.version,
    byteReads,
    stringReads,
    deepStringReads,
    bytePresence,
    stringPresence,
    buckets: {
      byteOwners: byteBuckets.size().toString(),
      stringOwners: stringBuckets.size().toString(),
      deepStringOwners: deepStringBuckets.size().toString(),
      byteEntriesByOwner: [byteBuckets.lookup(ownerOne).size(), byteBuckets.lookup(ownerTwo).size()].map(String),
      stringEntriesByOwner: [stringBuckets.lookup(ownerOne).size(), stringBuckets.lookup(ownerTwo).size()].map(String),
      deepStringGroupsByOwner: [
        deepStringBuckets.lookup(ownerOne).size(),
        deepStringBuckets.lookup(ownerTwo).size(),
      ].map(String),
      deepStringEntriesByGroup: [
        deepStringBuckets.lookup(ownerOne).lookup(groupOne).size(),
        deepStringBuckets.lookup(ownerOne).lookup(groupTwo).size(),
        deepStringBuckets.lookup(ownerTwo).lookup(groupOne).size(),
      ].map(String),
    },
    missingReadsRejected: {
      byteChild: true,
      byteOwner: true,
      stringChild: true,
      stringOwner: true,
      deepStringChild: true,
      deepStringGroup: true,
      deepStringOwner: true,
    },
  };
  const outputPath = resolve(resultsPath);
  mkdirSync(dirname(outputPath), { recursive: true });
  writeFileSync(outputPath, `${JSON.stringify(reference, null, 2)}\n`);
  console.log(`Compact ${compilerVersion} matched nested opaque Map raw values and missing-key behavior. Results: ${outputPath}`);
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
