import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/bounded-fab-hash-commit.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const runtimeDirectory = resolve(runtimePath);

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/, `unexpected Compact compiler: ${compilerVersion}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/BoundedFabHashCommit.compact');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'bounded-fab-hash-commit-'));

function compile(sourcePath, output) {
  return spawnSync(compactc, ['--skip-zk', sourcePath, output], { encoding: 'utf8' });
}

function resultFields(result) {
  assert.ok(Array.isArray(result) && result.length === 4, 'expected four FAB hash and commit outputs');
  return {
    persistentHash: Buffer.from(result[0]).toString('hex'),
    persistentCommit: Buffer.from(result[1]).toString('hex'),
    transientHash: result[2].toString(),
    transientCommit: result[3].toString(),
  };
}

try {
  const generated = join(scratch, 'compiled');
  const compiled = compile(source, generated);
  assert.equal(compiled.status, 0, `Compact compilation failed:\n${compiled.stderr || compiled.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  assert.equal(runtime.versionString, '0.21.0');
  const { Contract, pureCircuits } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const contract = new Contract({});
  const walletKey = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(
    runtime.createConstructorContext(null, walletKey),
  );
  const context = runtime.createCircuitContext({
    circuitId: 'hashRange',
    contractAddress: runtime.dummyContractAddress(),
    coinPublicKeyOrZswapState: walletKey,
    contractState: currentContractState.data,
    privateState: null,
  });

  const openingForward = Uint8Array.from({ length: 32 }, (_, index) => index + 1);
  const openingReverse = Uint8Array.from({ length: 32 }, (_, index) => 32 - index);
  const firstOpeningNonce = 17n;
  const secondOpeningNonce = 18n;
  async function hashRange(count, opening, nonce) {
    const call = await contract.circuits.hashRange(
      context,
      { count },
      opening,
      nonce,
    );
    return resultFields(call.result);
  }

  const countFive = await hashRange(5n, openingForward, firstOpeningNonce);
  const countSix = await hashRange(6n, openingForward, firstOpeningNonce);
  const countFiveSecondOpening = await hashRange(5n, openingReverse, secondOpeningNonce);

  assert.deepEqual(countFive, {
    persistentHash: 'e77b9a9ae9e30b0dbdb6f510a264ef9de781501d7b6b92ae89eb059c5ab743db',
    persistentCommit: '7a124d8ba6ccc92c05299f38e935e85816875e75d98b0a53133aa0632351c886',
    transientHash: '47699447692912459726522410466534423256066746656616207079667384395905208673480',
    transientCommit: '32897551855539531353075362223083106206342642377093571727659772813750899550245',
  });
  assert.deepEqual(countSix, {
    persistentHash: '67586e98fad27da0b9968bc039a1ef34c939b9b8e523a8bef89d478608c5ecf6',
    persistentCommit: '52f70840aa0bc85f12cf075bc1dcd09985aac5e98c7e2af1dd0aa7fe8474cb4b',
    transientHash: '6287741155009174685068248488276955603895669534698111446895299689163609634373',
    transientCommit: '22303504228254332940538443893749386311847149014689687363555693487392721321009',
  });
  assert.deepEqual(countFiveSecondOpening, {
    persistentHash: countFive.persistentHash,
    persistentCommit: '75d884ed4ce25784f89889084d0a0b110010eca921856af01a16a6668bfe281c',
    transientHash: countFive.transientHash,
    transientCommit: '3614288230654847062934431037799109620006385912217859110602866898799661824041',
  });
  await assert.rejects(hashRange(7n, openingForward, firstOpeningNonce));
  const scalarOpening = new Uint8Array(32).fill(9);
  const [persistent, transient] = pureCircuits.scalarCommit(41n, scalarOpening, 19n);
  assert.equal(Buffer.from(persistent).toString('hex'),
    '1095b00773ff16a5567335c81b6c23b6302e8b2a29a30ee3b1d8924b589e290e');
  assert.equal(transient, 18190385127810226412538976525783302391822206762158481351937660354805643878470n);
  assert.throws(() => pureCircuits.scalarCommit(41n, scalarOpening.slice(1), 19n));
  assert.throws(() => pureCircuits.scalarCommit(-1n, scalarOpening, 19n));

  const emptyPersistentOpening = openingForward;
  const changedPersistentOpening = Uint8Array.from(
    { length: 32 }, (_, index) => 255 - index,
  );
  async function emptyCommit(persistentOpening, transientOpening) {
    const [persistentResult, transientResult] = pureCircuits.emptyCommit(
      persistentOpening,
      transientOpening,
    );
    return {
      persistentCommit: Buffer.from(persistentResult).toString('hex'),
      transientCommit: transientResult.toString(),
    };
  }
  const emptyBase = await emptyCommit(emptyPersistentOpening, 19n);
  const emptyChangedPersistent = await emptyCommit(changedPersistentOpening, 19n);
  const emptyChangedTransient = await emptyCommit(emptyPersistentOpening, 20n);
  assert.deepEqual(emptyBase, {
    persistentCommit: 'ae216c2ef5247a3782c135efa279a3e4cdc61094270f5d2be58c6204b7a612c9',
    transientCommit: '12794700850233960416233463732843894202025917954986491544046826947248899317573',
  });
  assert.deepEqual(emptyChangedPersistent, {
    persistentCommit: '1865c00831e73f7ee23fc13cb2d0f588b9c341835ca7472f8ec035aba4b789d6',
    transientCommit: emptyBase.transientCommit,
  });
  assert.deepEqual(emptyChangedTransient, {
    persistentCommit: emptyBase.persistentCommit,
    transientCommit: '14450191916591004564031280932146803085578924438601728208718421638496337348179',
  });
  assert.throws(() => pureCircuits.emptyCommit(emptyPersistentOpening.slice(1), 19n));

  console.log(JSON.stringify({
    compiler: compilerVersion,
    runtime: runtime.versionString,
    circuit: 'hashRange',
    payload: 'Payload { count: Uint<0..7> }',
    openingForward: [...openingForward],
    openingReverse: [...openingReverse],
    openingNonces: [firstOpeningNonce.toString(), secondOpeningNonce.toString()],
    outputs: { countFive, countSix, countFiveSecondOpening },
    rejectedCount: 7,
    scalarCommit: { persistent: Buffer.from(persistent).toString('hex'), transient: transient.toString() },
    emptyCommit: {
      opening: [...emptyPersistentOpening],
      transientOpening: '19',
      changedOpening: [...changedPersistentOpening],
      changedTransientOpening: '20',
      outputs: { emptyBase, emptyChangedPersistent, emptyChangedTransient },
    },
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
