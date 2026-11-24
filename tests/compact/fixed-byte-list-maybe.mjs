import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/fixed-byte-list-maybe.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], {encoding: 'utf8'}).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/, `unexpected Compact compiler: ${compilerVersion}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(root, 'tests/compact/FixedByteListMaybe.compact');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, {recursive: true});
const scratch = mkdtempSync(join(experiments, 'fixed-byte-list-maybe-'));

try {
  const generated = join(scratch, 'compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], {encoding: 'utf8'});
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const zkir = JSON.parse(readFileSync(join(generated, 'zkir/inspect.zkir'), 'utf8'));
  const output = zkir.instructions.findLast(instruction => instruction.op === 'output');
  const outputFieldCounts = [1, 32, 128].map(length => 1 + Math.ceil(length / 31));
  assert.equal(zkir.outputs.length, outputFieldCounts.reduce((sum, count) => sum + count, 0));
  assert.equal(output.vals.length, zkir.outputs.length);
  assert.ok(zkir.outputs.every(type => type === 'Scalar<BLS12-381>'));
  for (const [length, fieldCount] of [1, 32, 128].map((length, index) =>
    [length, outputFieldCounts[index]])) {
    const single = JSON.parse(readFileSync(join(generated, `zkir/inspect${length}.zkir`), 'utf8'));
    const singleOutput = single.instructions.findLast(instruction => instruction.op === 'output');
    assert.equal(single.outputs.length, fieldCount, `Bytes<${length}> Maybe field count`);
    assert.equal(singleOutput.vals.length, fieldCount, `Bytes<${length}> Maybe output order`);
  }

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), {recursive: true});
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');
  const runtimeUrl = pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href;
  const contractUrl = pathToFileURL(join(generated, 'contract/index.js')).href;
  const {
    createCircuitContext, createConstructorContext, dummyContractAddress,
  } = await import(runtimeUrl);
  const {Contract} = await import(contractUrl);

  const contract = new Contract({});
  const walletKey = '00'.repeat(32);
  const byte1 = Uint8Array.from([77]);
  const byte32 = Uint8Array.from({length: 32}, (_, index) => index);
  const byte128 = Uint8Array.from({length: 128}, (_, index) => (index * 17 + 5) % 256);
  const zeros = [new Uint8Array(1), new Uint8Array(32), new Uint8Array(128)];
  const {currentContractState} = await contract.initialState(
    createConstructorContext(null, walletKey));
  const invoke = async (name, state, ...args) => {
    const context = createCircuitContext({
      circuitId: name,
      contractAddress: dummyContractAddress(),
      coinPublicKeyOrZswapState: walletKey,
      contractState: state,
      privateState: null,
    });
    const call = await contract.circuits[name](context, ...args);
    return [call.result, call.context.callContext.currentQueryContext.state];
  };
  const checkHeads = (heads, present, values) => {
    assert.equal(heads.length, 3);
    heads.forEach((head, index) => {
      assert.deepEqual(Object.keys(head), ['is_some', 'value']);
      assert.equal(head.is_some, present);
      assert.deepEqual(head.value, values[index]);
    });
  };

  const [empty, initial] = await invoke('inspect', currentContractState.data);
  checkHeads(empty, false, zeros);
  const [, populated] = await invoke('push', initial, byte1, byte32, byte128);
  const [heads] = await invoke('inspect', populated);
  checkHeads(heads, true, [byte1, byte32, byte128]);

  console.log(JSON.stringify({
    compact: compilerVersion,
    runtime: runtimePackage.version,
    nativeOutputFields: outputFieldCounts,
    empty: empty.map(value => ({is_some: value.is_some, length: value.value.length})),
    populated: heads.map(value => ({is_some: value.is_some, length: value.value.length})),
    zkirOutputs: zkir.outputs.length,
  }));
} finally {
  rmSync(scratch, {recursive: true, force: true});
}
