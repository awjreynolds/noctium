import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/jubjub-group-parity.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/);
const packageJson = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(packageJson.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(root, 'tests/compact/JubjubGroupParity.compact');
const experiments = join(root, 'build/experiments/305');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'compact-jubjub-group-parity-'));
try {
  const generated = join(scratch, 'compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, compile.stderr || compile.stdout);
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');
  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  const { pureCircuits } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);

  const point = runtime.ecMulGenerator(1n);
  const identity = runtime.constructJubjubPoint(0n, 1n);
  const scalar = 1n;
  const generatorProjection = pureCircuits.project(point);
  const identityProjection = pureCircuits.project(identity);
  assert.deepEqual(generatorProjection, [
    28336281903124990867587793011069573392383982287722241916350956173377953689573n,
    39385640392217313770878525135509063452020585410343666726093009378539878503883n,
  ]);
  assert.deepEqual(identityProjection, [0n, 1n]);

  const fieldModulus = 52435875175126190479447740508185965837690552500527637822603658699938581184513n;
  const constructionCases = [
    ['generator', point],
    ['identity', identity],
    ['offCurve', { x: 0n, y: 0n }],
    ['lowOrder', { x: 0n, y: fieldModulus - 1n }],
  ];
  const construction = Object.fromEntries(constructionCases.map(([name, input]) => {
    const output = pureCircuits.construct(input.x, input.y);
    assert.deepEqual(output, input, name);
    return [name, { x: output.x.toString(), y: output.y.toString() }];
  }));

  const generatedPoint = runtime.ecMulGenerator(scalar);
  const multiplied = runtime.ecMul(point, scalar);
  const sum = runtime.ecAdd(point, identity);
  const negated = runtime.ecNeg(point);
  const cancelled = runtime.ecAdd(point, negated);
  const identityNegated = runtime.ecNeg(identity);
  const result = pureCircuits.groupParity(point.x, point.y, scalar);
  const expected = {
    checkedX: point.x,
    checkedY: point.y,
    generatorX: generatedPoint.x,
    generatorY: generatedPoint.y,
    multipliedX: multiplied.x,
    multipliedY: multiplied.y,
    sumX: sum.x,
    sumY: sum.y,
    negatedX: negated.x,
    negatedY: negated.y,
    cancelledX: cancelled.x,
    cancelledY: cancelled.y,
    identityNegatedX: identityNegated.x,
    identityNegatedY: identityNegated.y,
    scalarResult: scalar,
  };
  assert.deepEqual(result, expected);
  console.log(JSON.stringify({
    fixture: 'JubjubGroupParity.groupParity',
    compact: compilerVersion,
    runtime: packageJson.version,
    projections: {
      generator: generatorProjection.map(String),
      identity: identityProjection.map(String),
    },
    construction,
    input: { pointX: point.x.toString(), pointY: point.y.toString(), rawScalar: scalar.toString() },
    outputs: Object.fromEntries(Object.entries(result).map(([name, value]) => [name, value.toString()])),
  }));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
