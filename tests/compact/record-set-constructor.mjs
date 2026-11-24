import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/record-set-constructor.mjs <compactc> <compact-runtime>');
const version = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(version, /^0\.36\.1 \(7fa3a117c/);
const runtimeDirectory = resolve(runtimePath);
const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')));
assert.equal(runtime.versionString, '0.21.0');
const experiments = fileURLToPath(new URL('../../build/experiments/', import.meta.url));
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'record-set-constructor-'));
try {
  const source = fileURLToPath(new URL('./RecordSetConstructor.compact', import.meta.url));
  execFileSync(compactc, ['--skip-zk', source, scratch]);
  const link = join(scratch, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(link), { recursive: true });
  symlinkSync(runtimeDirectory, link, 'dir');
  const { Contract, ledger } = await import(pathToFileURL(join(scratch, 'contract/index.js')));
  const contract = new Contract({});
  const wallet = '00'.repeat(32);
  const tag = new Uint8Array([7]);
  const firstId = new Uint8Array(33).fill(3);
  const lateId = firstId.slice();
  lateId[32] = 4;
  for (const enabled of [false, true]) {
    const { currentContractState } = await contract.initialState(
      runtime.createConstructorContext(null, wallet), enabled, tag, firstId, lateId,
    );
    const state = currentContractState.data;
    const count = enabled ? 2n : 1n;
    assert.equal(ledger(state).members.size(), count);
    const { result } = await contract.circuits.inspect(runtime.createCircuitContext({
      circuitId: 'inspect', contractAddress: runtime.dummyContractAddress(),
      coinPublicKeyOrZswapState: wallet, contractState: state, privateState: null,
    }), tag, firstId, lateId);
    assert.deepEqual(result, [true, enabled, count]);
  }
  console.log(`Compact ${version}: checked guarded record Set construction and duplicate insertion`);
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
