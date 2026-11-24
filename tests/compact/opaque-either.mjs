import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/opaque-either.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/);
const runtimeDirectory = resolve(runtimePath);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'opaque-either-'));

try {
  const generated = join(scratch, 'compact');
  execFileSync(compactc, ['--skip-zk', join(projectRoot, 'tests/compact/OpaqueEither.compact'), generated]);
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');
  const { pureCircuits } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);

  const textValue = 'A\0B';
  const bytesValue = Uint8Array.of(0, 255, 0, 1);
  const boolValue = true;
  const cases = [true, false].map(isLeft => {
    const stringChoice = pureCircuits.stringChoice(isLeft, textValue, boolValue);
    const bytesChoice = pureCircuits.bytesChoice(isLeft, boolValue, bytesValue);
    assert.deepEqual(stringChoice, {
      is_left: isLeft, left: isLeft ? textValue : '', right: !isLeft,
    });
    assert.deepEqual(bytesChoice, {
      is_left: isLeft, left: isLeft, right: isLeft ? new Uint8Array() : bytesValue,
    });
    return { isLeft, stringChoice, bytesChoice: { ...bytesChoice, right: [...bytesChoice.right] } };
  });
  console.log(JSON.stringify({
    compact: compilerVersion, runtime: runtimePackage.version,
    textValue, bytesValue: [...bytesValue], boolValue, cases,
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
