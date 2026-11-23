import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/raw-shielded-claims.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/, `unexpected Compact compiler: ${compilerVersion}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/RawShieldedClaims.compact');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'raw-shielded-claims-'));

const digest = (byte) => new Uint8Array(32).fill(byte);
const digestHex = (byte) => byte.toString(16).padStart(2, '0').repeat(32);
const emptyClaims = {
  claimedNullifiers: [],
  claimedShieldedReceives: [],
  claimedShieldedSpends: [],
};

try {
  const generated = join(scratch, 'compiled');
  const compiled = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compiled.status, 0, `Compact compilation failed:\n${compiled.stderr || compiled.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  assert.equal(runtime.versionString, '0.21.0');
  const { Contract } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const contract = new Contract({});
  const walletKey = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(
    runtime.createConstructorContext(null, walletKey),
  );
  const invoke = async (circuitId, ...args) => {
    const context = runtime.createCircuitContext({
      circuitId,
      contractAddress: runtime.dummyContractAddress(),
      coinPublicKeyOrZswapState: walletKey,
      contractState: currentContractState.data,
      privateState: null,
    });
    const call = await contract.circuits[circuitId](context, ...args);
    const effects = call.context.callContext.currentQueryContext.effects;
    return {
      claimedNullifiers: effects.claimedNullifiers,
      claimedShieldedReceives: effects.claimedShieldedReceives,
      claimedShieldedSpends: effects.claimedShieldedSpends,
    };
  };
  const claims = (nullifiers = [], receives = [], spends = []) => ({
    claimedNullifiers: nullifiers,
    claimedShieldedReceives: receives,
    claimedShieldedSpends: spends,
  });

  const directInputs = [digest(6), digest(7), digest(8)];
  const expectedDirect = claims(
    [digestHex(6)],
    [digestHex(7)],
    [digestHex(8)],
  );
  const direct = await invoke('rawClaims', ...directInputs);
  assert.deepEqual(direct, expectedDirect);
  const helpers = await invoke('helperClaims', ...directInputs);
  assert.deepEqual(helpers, expectedDirect, 'checked helper calls must preserve the three raw claim effects');

  const disabled = await invoke('guardedReceive', digest(7), false);
  assert.deepEqual(disabled, emptyClaims);
  const enabled = await invoke('guardedReceive', digest(7), true);
  assert.deepEqual(enabled, claims([], [digestHex(7)], []));

  const duplicates = await invoke('duplicateClaims', ...directInputs);
  assert.deepEqual(duplicates, expectedDirect, 'repeated same-kind digest claims must deduplicate');

  const distinct = await invoke(
    'distinctClaims',
    digest(6), digest(9),
    digest(7), digest(10),
    digest(8), digest(11),
  );
  const distinctExpected = claims(
    [digestHex(6), digestHex(9)],
    [digestHex(7), digestHex(10)],
    [digestHex(8), digestHex(11)],
  );
  const sortClaimKinds = (value) => Object.fromEntries(
    Object.entries(value).map(([kind, digests]) => [kind, [...digests].sort()]),
  );
  assert.deepEqual(sortClaimKinds(distinct), sortClaimKinds(distinctExpected));

  console.log(JSON.stringify({
    compiler: compilerVersion,
    runtime: runtime.versionString,
    rawDigests: {
      nullifier: digestHex(6),
      receive: digestHex(7),
      spend: digestHex(8),
    },
    direct,
    helperRoute: helpers,
    guarded: { disabled, enabled },
    duplicateClaims: duplicates,
    distinctDigests: distinct,
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
