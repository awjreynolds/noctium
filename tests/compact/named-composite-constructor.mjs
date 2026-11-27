import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/named-composite-constructor.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/,
  `expected pinned Compact 0.36.1 compiler, got ${compilerVersion}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0', 'expected pinned Compact runtime 0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/NamedCompositeConstructor.compact');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, '1497-named-composite-constructor-'));

try {
  const generated = join(scratch, 'compact');
  execFileSync(compactc, ['--skip-zk', source, generated], {
    cwd: projectRoot,
    encoding: 'utf8',
  });

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  const { Contract } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  assert.equal(runtime.versionString, '0.21.0');

  const walletKey = '00'.repeat(32);
  const seed = {
    position: { amount: 17n, enabled: true, ignored: 240n },
    extras: [23n, 241n],
  };
  const initialState = async argument => new Contract({}).initialState(
    runtime.createConstructorContext(null, walletKey), argument,
  );
  const { currentContractState } = await initialState(seed);
  const inspectContext = runtime.createCircuitContext({
    circuitId: 'inspect',
    contractAddress: runtime.dummyContractAddress(),
    coinPublicKeyOrZswapState: walletKey,
    contractState: currentContractState.data,
    privateState: null,
  });
  const inspected = await new Contract({}).circuits.inspect(inspectContext);
  assert.deepEqual(inspected.result, [17n, true, 23n]);

  for (const [label, invalid] of [
    ['malformed used amount', {
      ...seed, position: { ...seed.position, amount: '17' },
    }],
    ['out-of-range used amount', {
      ...seed, position: { ...seed.position, amount: 256n },
    }],
    ['malformed ignored record field', {
      ...seed, position: { ...seed.position, ignored: '240' },
    }],
    ['out-of-range ignored record field', {
      ...seed, position: { ...seed.position, ignored: 256n },
    }],
    ['malformed ignored tuple field', {
      ...seed, extras: [23n, '241'],
    }],
    ['out-of-range ignored tuple field', {
      ...seed, extras: [23n, 256n],
    }],
    ['out-of-range used tuple field', {
      ...seed, extras: [65_536n, 241n],
    }],
  ]) {
    await assert.rejects(() => initialState(invalid), label);
  }

  console.log(JSON.stringify({
    fixture: 'NamedCompositeConstructor',
    compiler: compilerVersion,
    runtime: runtimePackage.version,
    constructorArgument: {
      seed: { position: { amount: '17', enabled: true, ignored: '240' }, extras: ['23', '241'] },
    },
    inspect: ['17', true, '23'],
    rejectedInputs: 7,
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
