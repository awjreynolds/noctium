import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/mixed-sequence-join.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
assert.match(execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim(),
  /^0\.36\.1 \(7fa3a117c/);
const runtimeDirectory = resolve(runtimePath);
const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
assert.equal(runtime.versionString, '0.21.0');

const fixtures = dirname(fileURLToPath(import.meta.url));
const experiments = resolve(fixtures, '../../build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'mixed-sequence-join-'));
try {
  const source = join(fixtures, 'MixedSequenceJoin.compact');
  const generated = join(scratch, 'compact');
  execFileSync(compactc, ['--skip-zk', source, generated]);
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const { Contract } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const wallet = '00'.repeat(32);
  for (const [choice, selected, expected] of [
    [true, 'vectorArm', [7n, 199n]],
    [false, 'tupleArm', [241n, 513n]],
  ]) {
    const calls = [];
    const contract = new Contract({
      vectorArm: ({ privateState }) => {
        calls.push('vectorArm');
        return [privateState, [7n, 199n]];
      },
      tupleArm: ({ privateState }) => {
        calls.push('tupleArm');
        return [privateState, [241n, 513n]];
      },
    });
    const { currentContractState } = await contract.initialState(
      runtime.createConstructorContext(null, wallet));
    const context = runtime.createCircuitContext({
      circuitId: 'choose',
      contractAddress: runtime.dummyContractAddress(),
      coinPublicKeyOrZswapState: wallet,
      contractState: currentContractState.data,
      privateState: null,
    });
    const call = await contract.circuits.choose(context, choice);
    assert.deepEqual(call.result, expected);
    assert.deepEqual(calls, [selected]);
    console.log(`${selected}: ${call.result.join(', ')}`);
  }

  const sourceText = readFileSync(source, 'utf8');
  for (const [name, original, replacement] of [
    ['arity', ' : tupleArm();', ' : [7];'],
    ['crossed-bounds', 'witness tupleArm(): [Uint<8>,', 'witness tupleArm(): [Uint<4>,'],
  ]) {
    assert.ok(sourceText.includes(original));
    const invalid = join(scratch, `${name}.compact`);
    writeFileSync(invalid, sourceText.replace(original, replacement));
    const rejected = spawnSync(compactc, ['--skip-zk', invalid, join(scratch, name)],
      { encoding: 'utf8' });
    assert.ok(rejected.status !== null && rejected.status !== 0, `${name} should reject`);
    assert.match(`${rejected.stderr}\n${rejected.stdout}`, /of condition branches/);
    console.log(`${name} rejected.`);
  }
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
