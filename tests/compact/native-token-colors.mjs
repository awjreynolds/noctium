import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/native-token-colors.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(root, 'tests/compact/NativeTokenColors.compact');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'native-token-colors-'));
try {
  const generated = join(scratch, 'compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, compile.stderr || compile.stdout);
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');
  const { pureCircuits } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const domain = Uint8Array.from({ length: 32 }, (_, index) => index + 1);
  const cases = [
    [domain, Uint8Array.from({ length: 32 }, (_, index) => index + 1)],
    [domain, new Uint8Array(32).fill(0xa5)],
    [new Uint8Array(32), new Uint8Array(32).fill(255)],
    [new Uint8Array(32).fill(255), new Uint8Array(32)],
  ];
  assert.deepEqual(pureCircuits.nativeTokenValue(), new Uint8Array(32));
  const results = cases.map(([separator, address]) => ({
    domain: Buffer.from(separator).toString('hex'),
    contractAddress: Buffer.from(address).toString('hex'),
    tokenColor: Buffer.from(pureCircuits.deriveTokenColor(separator, address)).toString('hex'),
  }));
  assert.equal(new Set(results.map(({ tokenColor }) => tokenColor)).size, cases.length);
  console.log(JSON.stringify({
    fixture: 'NativeTokenColors', compact: compilerVersion,
    nativeToken: '00'.repeat(32), cases: results,
  }));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
