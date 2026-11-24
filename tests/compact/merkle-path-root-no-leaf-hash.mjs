import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/merkle-path-root-no-leaf-hash.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/, `unexpected Compact compiler: ${compilerVersion}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(projectRoot, 'build/experiments/314');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'compact-merkle-path-'));

try {
  const generated = join(scratch, 'compact');
  const source = join(projectRoot, 'tests/compact/MerklePathRootNoLeafHash.compact');
  execFileSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  assert.equal(runtime.versionString, '0.21.0');
  const { pureCircuits } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const path = {
    leaf: Uint8Array.from({ length: 32 }, (_, index) => index + 1),
    path: [
      { sibling: { field: 17n }, goes_left: true },
      { sibling: { field: 29n }, goes_left: false },
    ],
  };
  const emptyPath = { leaf: path.leaf, path: [] };
  const depthThreePath = {
    leaf: path.leaf,
    path: [
      ...path.path,
      { sibling: { field: 41n }, goes_left: true },
    ],
  };
  const expectedRoot = 23615363679718302500648733510038242834016166715802047945282536128750549339216n;
  const expectedEmptyRoot = 54980096196880238888162309298627284197919427551736292421657099673115230721n;
  const expectedDepthThreeRoot = 16638844364555447002226514103550815772834617616994228403980866356241338707105n;
  const digest = pureCircuits.digestFromPath(path);
  const emptyDigest = pureCircuits.digestFromEmptyPath(emptyPath);
  const depthThreeDigest = pureCircuits.digestFromDepthThreePath(depthThreePath);
  assert.deepEqual(digest, { field: expectedRoot });
  assert.deepEqual(emptyDigest, { field: expectedEmptyRoot });
  assert.deepEqual(depthThreeDigest, { field: expectedDepthThreeRoot });
  assert.equal(digest.field.toString(), expectedRoot.toString());
  assert.equal(emptyDigest.field.toString(), expectedEmptyRoot.toString());
  assert.equal(depthThreeDigest.field.toString(), expectedDepthThreeRoot.toString());
  console.log(JSON.stringify({
    depthTwo: { field: digest.field.toString() },
    depthZero: { field: emptyDigest.field.toString() },
    depthThree: { field: depthThreeDigest.field.toString() },
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
