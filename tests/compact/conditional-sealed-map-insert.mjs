import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/conditional-sealed-map-insert.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/, `unexpected Compact compiler: ${compilerVersion}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/ConditionalSealedMapInsert.compact');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'conditional-sealed-map-insert-'));

try {
  const generated = join(scratch, 'compiled');
  execFileSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  assert.equal(runtime.versionString, '0.21.0');
  const { Contract, ledger } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const contract = new Contract({});
  const walletKey = '00'.repeat(32);
  const key = 19n;
  const cases = [];

  for (const enabled of [false, true]) {
    const initial = await contract.initialState(
      runtime.createConstructorContext(null, walletKey),
      key,
      enabled,
    );
    const state = initial.currentContractState.data;
    const view = ledger(state);
    const values = view.seeded;
    assert.equal(values.member(key), enabled);
    assert.equal(values.size(), enabled ? 1n : 0n);
    assert.equal(view.present, enabled);
    if (enabled) assert.equal(values.lookup(key), 41n);

    const context = runtime.createCircuitContext({
      circuitId: 'inspect',
      contractAddress: runtime.dummyContractAddress(),
      coinPublicKeyOrZswapState: walletKey,
      contractState: state,
      privateState: null,
    });
    const observation = (await contract.circuits.inspect(context, key)).result;
    assert.deepEqual(observation, [enabled, enabled]);
    cases.push({ enabled, mapMember: observation[0], sealedPresent: observation[1] });
  }

  assert.deepEqual(cases, [
    { enabled: false, mapMember: false, sealedPresent: false },
    { enabled: true, mapMember: true, sealedPresent: true },
  ]);
  console.log(JSON.stringify({
    compiler: compilerVersion,
    runtime: runtime.versionString,
    map: 'sealed Map<Field, Field>',
    sealedCell: 'Boolean present',
    key: key.toString(),
    insertedValue: '41',
    cases,
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
