import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdir, mkdtemp, rm, symlink } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/secp-projections.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
assert.match(execFileSync(compactc, ['--version'], { encoding: 'utf8' }), /^0\.36\.1 \(7fa3a117c/);
const runtimeDirectory = resolve(runtimePath);
const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')));
assert.equal(runtime.versionString, '0.21.0');

function fieldBytes(value) {
  return Array.from({ length: 32 }, (_, index) => Number((value >> BigInt(8 * index)) & 255n));
}

function foreign(family, role, value) {
  const bytes = role === 'Point'
    ? [2 + Number(value.y & 1n), ...fieldBytes(value.x).reverse()]
    : fieldBytes(value);
  return { kind: 'foreign', type: family + role, bytes };
}

const scratch = await mkdtemp(join(tmpdir(), 'noctium-secp-projections-'));
try {
  const generated = join(scratch, 'compact');
  const source = fileURLToPath(new URL('./SecpProjections.compact', import.meta.url));
  execFileSync(compactc, ['--skip-zk', source, generated]);
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  await mkdir(dirname(runtimeLink), { recursive: true });
  await symlink(runtimeDirectory, runtimeLink, 'dir');
  const { pureCircuits } = await import(pathToFileURL(join(generated, 'contract/index.js')));
  const kPoint = runtime.secp256k1MulGenerator(1n);
  const rPoint = runtime.secp256r1MulGenerator(1n);
  const kScalar = 5n;
  const rScalar = 7n;
  const kIdentity = runtime.secp256k1MulGenerator(0n);
  const rIdentity = runtime.secp256r1MulGenerator(0n);
  assert.throws(
    () => pureCircuits.inspect(kIdentity, kScalar, rPoint, rScalar),
    { name: 'CompactError', message: 'cannot extract the x-coordinate of the secp256k1 identity point' },
  );
  assert.throws(
    () => pureCircuits.inspect(kPoint, kScalar, rIdentity, rScalar),
    { name: 'CompactError', message: 'cannot extract the x-coordinate of the secp256r1 identity point' },
  );
  for (const [family, point] of [['secp256k1', kIdentity], ['secp256r1', rIdentity]]) {
    assert.throws(
      () => runtime[`${family}PointX`](point),
      { name: 'CompactError', message: `cannot extract the x-coordinate of the ${family} identity point` },
    );
    assert.throws(
      () => runtime[`${family}PointY`](point),
      { name: 'CompactError', message: `cannot extract the y-coordinate of the ${family} identity point` },
    );
  }
  const values = pureCircuits.inspect(kPoint, kScalar, rPoint, rScalar);
  assert.deepEqual(values, [kPoint, kScalar, kPoint.x, kPoint.y, rPoint, rScalar, rPoint.x, rPoint.y]);

  const inputs = {};
  const outputs = {};
  for (const [prefix, family, index] of [['k', 'Secp256k1', 0], ['r', 'Secp256r1', 4]]) {
    inputs[prefix + 'Point'] = foreign(family, 'Point', values[index]);
    inputs[prefix + 'Scalar'] = foreign(family, 'Scalar', values[index + 1]);
    outputs[prefix + 'PointResult'] = inputs[prefix + 'Point'];
    outputs[prefix + 'ScalarResult'] = inputs[prefix + 'Scalar'];
    outputs[prefix + 'X'] = foreign(family, 'Base', values[index + 2]);
    outputs[prefix + 'Y'] = foreign(family, 'Base', values[index + 3]);
  }
  console.log(JSON.stringify({ inputs, outputs }));
} finally {
  await rm(scratch, { recursive: true, force: true });
}
