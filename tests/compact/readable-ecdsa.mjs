import assert from 'node:assert/strict';
import {execFileSync} from 'node:child_process';
import {mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync} from 'node:fs';
import {dirname, join, resolve} from 'node:path';
import {fileURLToPath, pathToFileURL} from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/readable-ecdsa.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], {encoding: 'utf8'}).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, {recursive: true});
const scratch = mkdtempSync(join(experiments, '606-readable-ecdsa-compact-'));

const vectors = [
  {
    stem: 'ReadableECDSAK1',
    source: 'ReadableECDSAK1.compact',
    digest: '4b688df40bcedbe641ddb16ff0a1842d9c67ea1c3bf63f3e0471baa664531d1a',
    r: '241097efbf8b63bf145c8961dbdf10c310efbb3b2676bbc0f8b08505c9e2f795',
    s: '021006b7838609339e8b415a7f9acb1b661828131aef1ecbc7955dfb01f3ca0e',
    keyX: '779dd197a5df977ed2cf6cb31d82d43328b790dc6b3b7d4437a427bd5847dfcd',
    keyY: 'e94b724a555b6d017bb7607c3e3281daf5b1699d6ef4124975c9237b917d426f',
  },
  {
    stem: 'ReadableECDSAR1',
    source: 'ReadableECDSAR1.compact',
    digest: '44acf6b7e36c1342c2c5897204fe09504e1e2efb1a900377dbc4e7a6a133ec56',
    r: 'f3ac8061b514795b8843e3d6629527ed2afd6b1f6a555a7acabb5e6f79c8c2ac',
    s: '8bf77819ca05a6b2786c76262bf7371cef97b218e96f175a3ccdda2acc058903',
    keyX: '1ccbe91c075fc7f4f033bfa248db8fccd3565de94bbfb12f3c59ff46c271bf83',
    keyY: 'ce4014c68811f9a21a1fdb2c0e6113e06db7ca93b7404e78dc7ccd5ca89a4ca9',
  },
];

try {
  for (const vector of vectors) {
    const generated = join(scratch, vector.stem);
    execFileSync(compactc, [
      '--skip-zk', join(root, 'tests/compact', vector.source), generated,
    ], {encoding: 'utf8'});
    const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
    mkdirSync(dirname(runtimeLink), {recursive: true});
    symlinkSync(resolve(runtimeDirectory), runtimeLink, 'dir');
    const {pureCircuits} = await import(pathToFileURL(join(generated, 'contract/index.js')).href);

    const digest = Uint8Array.from(Buffer.from(vector.digest, 'hex'));
    const signature = {r: BigInt(`0x${vector.r}`), s: BigInt(`0x${vector.s}`)};
    const key = {
      x: BigInt(`0x${vector.keyX}`),
      y: BigInt(`0x${vector.keyY}`),
      identity: false,
    };
    assert.equal(pureCircuits.verify(digest, signature, key), true, `${vector.stem} known vector`);

    const changedDigest = digest.slice();
    changedDigest[0] ^= 1;
    assert.equal(pureCircuits.verify(changedDigest, signature, key), false,
      `${vector.stem} changed digest`);

    for (const component of ['r', 's']) {
      const zero = {...signature, [component]: 0n};
      let result;
      try {
        result = pureCircuits.verify(digest, zero, key);
      } catch {
        result = false;
      }
      assert.equal(result, false, `${vector.stem} zero ${component}`);
    }
  }
  console.log(JSON.stringify({
    compiler: compilerVersion,
    runtime: runtimePackage.version,
    vectors: vectors.map(({stem}) => ({stem, valid: true, changedDigest: false, zeroScalar: false})),
  }, null, 2));
} finally {
  rmSync(scratch, {recursive: true, force: true});
}
