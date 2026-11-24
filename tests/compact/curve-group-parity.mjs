import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';

const [compactc, runtimeDirectory, resultsPath] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory && resultsPath,
  'usage: node tests/compact/curve-group-parity.mjs <compactc-0.36.1> <compact-runtime-0.21.0> <results.json>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');
const absoluteRuntimeDirectory = resolve(runtimeDirectory);

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(projectRoot, 'build/experiments/966');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'compact-curve-group-parity-'));

function bytesLE(value, length) {
  const bytes = new Array(length).fill(0);
  for (let i = 0; i < length; i += 1) {
    bytes[i] = Number(value & 255n);
    value >>= 8n;
  }
  assert.equal(value, 0n, 'integer does not fit in canonical byte width');
  return bytes;
}

function bytesBE(value, length) {
  return bytesLE(value, length).reverse();
}

function foreignPointBytes(family, point) {
  if (family === 'Curve25519') {
    const bytes = bytesLE(point.y, 32);
    bytes[31] |= Number(point.x & 1n) << 7;
    return bytes;
  }
  if (point.identity) return new Array(33).fill(0);
  return [Number(2n + (point.y & 1n)), ...bytesBE(point.x, 32)];
}

function pointJson(family, point) {
  if (family === 'Jubjub') {
    return { kind: 'jubjubPoint', x: point.x.toString(), y: point.y.toString() };
  }
  return {
    kind: 'foreign',
    type: `${family}Point`,
    bytes: foreignPointBytes(family, point),
  };
}

function scalarJson(family, scalar) {
  if (family === 'Jubjub') return { kind: 'jubjubScalar', value: scalar.toString() };
  return {
    kind: 'foreign',
    type: `${family}Scalar`,
    bytes: bytesLE(scalar, 32),
  };
}

function samePoint(left, right) {
  return left.x === right.x && left.y === right.y && Boolean(left.identity) === Boolean(right.identity);
}

function addCase(cases, family, api, pureCircuits, point, other, scalar, label) {
  const entry = `${family[0].toLowerCase()}${family.slice(1)}Group`;
  const result = pureCircuits[entry](point, other, scalar);
  const expected = [api.add(point, other)];
  if (family === 'Jubjub') expected.push(api.neg(point));
  expected.push(api.mul(point, scalar), api.generator(scalar));
  assert.equal(result.length, expected.length, `${entry} output count`);
  result.forEach((actual, index) => assert.ok(samePoint(actual, expected[index]), `${entry} ${label} result ${index}`));

  const expectedJson = {
    resultAdded: pointJson(family, result[0]),
  };
  let resultIndex = 1;
  if (family === 'Jubjub') expectedJson.resultNegated = pointJson(family, result[resultIndex++]);
  expectedJson.resultMultiplied = pointJson(family, result[resultIndex++]);
  expectedJson.resultGenerated = pointJson(family, result[resultIndex]);
  cases.push({
    id: `${family.toLowerCase()}-${label}`,
    entry,
    inputs: {
      point: pointJson(family, point),
      other: pointJson(family, other),
      scalar: scalarJson(family, scalar),
    },
    expected: expectedJson,
  });
}

try {
  const compactSource = join(projectRoot, 'tests/compact/CurveGroupParity.compact');
  const generated = join(scratch, 'compact');
  const compile = spawnSync(compactc, ['--skip-zk', compactSource, generated], {
    cwd: projectRoot,
    encoding: 'utf8',
  });
  assert.equal(compile.status, 0, compile.stderr || compile.stdout);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(absoluteRuntimeDirectory, runtimeLink, 'dir');
  const runtime = await import(pathToFileURL(join(absoluteRuntimeDirectory, 'dist/index.js')).href);
  const { pureCircuits } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  assert.equal(runtime.versionString, '0.21.0');

  const families = [
    {
      name: 'Jubjub',
      modulus: BigInt(runtime.JUBJUB_SCALAR_MODULUS),
      generator: runtime.ecMulGenerator,
      add: runtime.ecAdd,
      neg: runtime.ecNeg,
      mul: runtime.ecMul,
    },
    {
      name: 'Secp256k1',
      modulus: BigInt(runtime.SECP256K1_SCALAR_MODULUS),
      generator: runtime.secp256k1MulGenerator,
      add: runtime.secp256k1Add,
      mul: runtime.secp256k1Mul,
    },
    {
      name: 'Secp256r1',
      modulus: BigInt(runtime.SECP256R1_SCALAR_MODULUS),
      generator: runtime.secp256r1MulGenerator,
      add: runtime.secp256r1Add,
      mul: runtime.secp256r1Mul,
    },
    {
      name: 'Curve25519',
      modulus: BigInt(runtime.CURVE25519_SCALAR_MODULUS),
      generator: runtime.curve25519MulGenerator,
      add: runtime.curve25519Add,
      mul: runtime.curve25519Mul,
    },
  ];

  const cases = [];
  for (const family of families) {
    const identity = family.generator(0n);
    const generator = family.generator(1n);
    const doubleGenerator = family.generator(2n);
    const negativeGenerator = family.generator(family.modulus - 1n);
    const points = [identity, generator, doubleGenerator];
    const scalars = [0n, 1n, 2n, family.modulus - 1n];

    for (const point of points) {
      for (const scalar of scalars) {
        addCase(cases, family.name, family, pureCircuits, point, identity, scalar,
          `point-${points.indexOf(point)}-scalar-${scalars.indexOf(scalar)}`);
      }
    }
    for (const [label, left, right] of [
      ['identity-plus-identity', identity, identity],
      ['generator-plus-identity', generator, identity],
      ['identity-plus-generator', identity, generator],
      ['generator-plus-generator', generator, generator],
      ['generator-plus-double', generator, doubleGenerator],
      ['generator-plus-negative', generator, negativeGenerator],
    ]) {
      addCase(cases, family.name, family, pureCircuits, left, right, 1n, label);
    }
  }

  const result = JSON.stringify({ compiler: compilerVersion, runtime: runtimePackage.version, cases }, null, 2);
  mkdirSync(dirname(resolve(resultsPath)), { recursive: true });
  writeFileSync(resultsPath, `${result}\n`);
  console.log(`Compact ${compilerVersion} and runtime ${runtimePackage.version} matched ${cases.length} curve group vectors.`);
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
