import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/opaque-equality.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const sourceDirectory = dirname(fileURLToPath(import.meta.url));
const root = resolve(sourceDirectory, '../..');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'opaque-equality-'));
try {
  const generated = join(scratch, 'compact');
  execFileSync(compactc, ['--skip-zk', join(sourceDirectory, 'OpaqueEquality.compact'), generated]);
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');
  const runtimeUrl = pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href;
  const contractUrl = pathToFileURL(join(generated, 'contract/index.js')).href;
  const runtime = await import(runtimeUrl);
  const { Contract, ledger, pureCircuits } = await import(contractUrl);
  assert.equal(runtime.versionString, '0.21.0');
  for (const circuit of ['recordString', 'recordBytes']) {
    const relation = JSON.parse(readFileSync(join(generated, `zkir/${circuit}.zkir`), 'utf8'));
    assert.ok(relation.instructions.some(({ op }) => op === 'test_eq'),
      `${circuit} relation must use Compact test_eq`);
  }

  const strings = [
    { a: '', b: '', same: true },
    { a: 'exact', b: 'exact', same: true },
    { a: 'a\0b', b: 'a\0b', same: true },
    { a: 'a', b: 'a\0b', same: false },
    { a: 'prefix\x01', b: 'prefix\x02', same: false },
    { a: 'left', b: 'right', same: false },
  ];
  const bytes = [
    { a: [], b: [], same: true },
    { a: [0x00, 0x01, 0xff], b: [0x00, 0x01, 0xff], same: true },
    { a: [0x41, 0x00, 0x42], b: [0x41, 0x00, 0x42], same: true },
    { a: [0x41], b: [0x41, 0x00, 0x42], same: false },
    { a: [0x70, 0x72, 0x65, 0x66, 0x69, 0x78, 0x01], b: [0x70, 0x72, 0x65, 0x66, 0x69, 0x78, 0x02], same: false },
    { a: [0x41], b: [0x42], same: false },
  ];
  for (const { a, b, same } of strings) {
    assert.equal(pureCircuits.sameString(a, b), same);
  }
  for (const { a, b, same } of bytes) {
    assert.equal(pureCircuits.sameBytes(Uint8Array.from(a), Uint8Array.from(b)), same);
  }

  const contract = new Contract({});
  const wallet = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(
    runtime.createConstructorContext(null, wallet),
  );
  const contextFor = (circuitId, contractState) => runtime.createCircuitContext({
    circuitId,
    contractAddress: runtime.dummyContractAddress(),
    coinPublicKeyOrZswapState: wallet,
    contractState,
    privateState: null,
  });
  const stateOf = (context) => context.callContext.currentQueryContext.state;
  let contractState = currentContractState.data;
  for (const { a, b, same } of strings) {
    const result = await contract.circuits.recordString(contextFor('record-string', contractState), a, b);
    assert.equal(result.result, same);
    contractState = stateOf(result.context);
    assert.equal(ledger(contractState).last, same);
  }
  for (const { a, b, same } of bytes) {
    const result = await contract.circuits.recordBytes(
      contextFor('record-bytes', contractState), Uint8Array.from(a), Uint8Array.from(b),
    );
    assert.equal(result.result, same);
    contractState = stateOf(result.context);
    assert.equal(ledger(contractState).last, same);
  }

  console.log(JSON.stringify({ compiler: compilerVersion, runtime: runtimePackage.version, strings, bytes }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
