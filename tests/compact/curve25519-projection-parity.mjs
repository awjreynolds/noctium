import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/curve25519-projection-parity.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/,
  `expected pinned Compact 0.36.1 compiler, got ${compilerVersion}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0', 'expected pinned Compact runtime 0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(projectRoot, 'build/experiments/871');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'curve25519-projection-parity-'));

try {
  const source = join(projectRoot, 'tests/compact/Curve25519ProjectionParity.compact');
  const generated = join(scratch, 'compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], {
    cwd: projectRoot,
    encoding: 'utf8',
  });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtimeUrl = pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href;
  const contractUrl = pathToFileURL(join(generated, 'contract/index.js')).href;
  const runtime = await import(runtimeUrl);
  const { pureCircuits } = await import(contractUrl);
  assert.equal(runtime.versionString, '0.21.0');

  const generator = runtime.curve25519MulGenerator(1n);
  const identity = { x: 0n, y: 1n };
  const generatorProjection = pureCircuits.project(generator);
  const identityProjection = pureCircuits.project(identity);
  assert.deepEqual(generatorProjection, [generator.x, generator.y]);
  assert.deepEqual(identityProjection, [0n, 1n]);

  console.log(JSON.stringify({
    compiler: compilerVersion,
    runtime: runtimePackage.version,
    entrypoint: 'project',
    generator: generatorProjection.map(String),
    identity: identityProjection.map(String),
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
