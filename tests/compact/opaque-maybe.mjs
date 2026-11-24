import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/opaque-maybe.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const runtimeDirectory = resolve(runtimePath);
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/,
  `expected pinned Compact 0.36.1 compiler, got ${compilerVersion}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0', 'expected pinned Compact runtime 0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'opaque-maybe-'));

try {
  const generated = join(scratch, 'compact');
  const source = join(projectRoot, 'tests/compact/OpaqueMaybe.compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');
  const { pureCircuits } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);

  const text = 'A\0B';
  const bytes = Uint8Array.of(0, 255, 0, 1);
  const stringSome = pureCircuits.stringSome(text);
  const stringNone = pureCircuits.stringNone();
  const bytesSome = pureCircuits.bytesSome(bytes);
  const bytesNone = pureCircuits.bytesNone();
  assert.deepEqual(stringSome, { is_some: true, value: text });
  assert.deepEqual(stringNone, { is_some: false, value: '' });
  assert.deepEqual(bytesSome, { is_some: true, value: bytes });
  assert.deepEqual(bytesNone, { is_some: false, value: new Uint8Array() });

  console.log(JSON.stringify({
    fixture: 'OpaqueMaybe',
    compact: compilerVersion,
    runtime: runtimePackage.version,
    stringSome,
    stringNone,
    bytesSome: { ...bytesSome, value: [...bytesSome.value] },
    bytesNone: { ...bytesNone, value: [...bytesNone.value] },
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
