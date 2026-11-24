import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { createRequire } from 'node:module';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimePath, resultsPath] = process.argv.slice(2);
assert.ok(compactc && runtimePath && resultsPath,
  'usage: node tests/compact/readable-ethereum-address.mjs <compactc-0.36.1> <compact-runtime-0.21.0> <results.json>');
const version = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(version, /^0\.36\.1 \(7fa3a117c/);
const runtime = resolve(runtimePath);
assert.equal(JSON.parse(readFileSync(join(runtime, 'package.json'), 'utf8')).version, '0.21.0');

const source = fileURLToPath(new URL('./ReadableEthereumAddress.compact', import.meta.url));
const experiments = fileURLToPath(new URL('../../build/experiments/', import.meta.url));
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, '982-compact-address-'));
try {
  const output = join(scratch, 'compiled');
  execFileSync(compactc, ['--skip-zk', source, output], { encoding: 'utf8' });
  const runtimeLink = join(output, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtime, runtimeLink, 'dir');
  const { pureCircuits } = await import(pathToFileURL(join(output, 'contract/index.js')).href);
  const compactRuntime = await import(pathToFileURL(join(runtime, 'dist/index.js')).href);
  const requireRuntimeDependency = createRequire(join(runtime, 'package.json'));
  const { keccak_256 } = requireRuntimeDependency('@noble/hashes/sha3.js');
  const bytesBE = (value, length) => Array.from({ length }, (_, index) =>
    Number((value >> BigInt((length - index - 1) * 8)) & 255n));
  const pointInput = point => {
    if (point.identity) return { kind: 'foreign', type: 'Secp256k1Point', bytes: new Array(33).fill(0) };
    return {
      kind: 'foreign',
      type: 'Secp256k1Point',
      bytes: [Number(2n + (point.y & 1n)), ...bytesBE(point.x, 32)],
    };
  };
  const referenceAddress = point => {
    const preimage = [...bytesBE(point.x, 32), ...bytesBE(point.y, 32)];
    return { preimage, address: Array.from(keccak_256(Uint8Array.from(preimage)).slice(12)) };
  };

  const order = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141n;
  const vectors = [
    ['generator', compactRuntime.secp256k1MulGenerator(1n)],
    ['double-generator', compactRuntime.secp256k1MulGenerator(2n)],
    ['negative-double-generator', compactRuntime.secp256k1MulGenerator(order - 2n)],
  ];
  const cases = vectors.map(([id, point]) => {
    assert.equal(point.identity, false, `${id} must be nonidentity`);
    const expected = referenceAddress(point);
    const compactBytes = Array.from(pureCircuits.derive(point));
    assert.equal(compactBytes.length, 20, `${id} must return exactly Bytes20`);
    assert.deepEqual(compactBytes, expected.address, `${id} must match Keccak(x || y)[12..32]`);
    return {
      id,
      point: pointInput(point),
      preimage: expected.preimage,
      expected: { kind: 'bytes', values: compactBytes },
    };
  });
  const fieldPrime = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2fn;
  assert.notDeepEqual(cases[0].point.bytes, cases[1].point.bytes, '2G must differ from the generator');
  assert.equal(vectors[1][1].x, vectors[2][1].x, '2G and -2G must share x');
  assert.equal(vectors[1][1].y + vectors[2][1].y, fieldPrime, 'the final pair must be negatives');
  assert.notDeepEqual(cases[1].expected.values, cases[2].expected.values, '2G and -2G addresses must differ');

  const identity = compactRuntime.secp256k1MulGenerator(0n);
  assert.equal(identity.identity, true);
  assert.throws(() => pureCircuits.derive(identity), /identity/i);
  const result = {
    compiler: version,
    runtime: JSON.parse(readFileSync(join(runtime, 'package.json'), 'utf8')).version,
    algorithm: 'Keccak-256(big-endian x || big-endian y), bytes 12 through 31',
    cases,
    identityRejected: true,
  };
  mkdirSync(dirname(resolve(resultsPath)), { recursive: true });
  writeFileSync(resolve(resultsPath), `${JSON.stringify(result, null, 2)}\n`);
  console.log(`Compact ${version}: matched ${cases.length} exact Bytes20 vectors, identity rejected`);
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
