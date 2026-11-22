import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/readable-ethereum-address.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const version = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(version, /^0\.36\.1 \(7fa3a117c/);
const runtime = resolve(runtimePath);
assert.equal(JSON.parse(readFileSync(join(runtime, 'package.json'), 'utf8')).version, '0.21.0');

const source = fileURLToPath(new URL('./ReadableEthereumAddress.compact', import.meta.url));
const experiments = fileURLToPath(new URL('../../build/experiments/', import.meta.url));
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, '603-compact-address-'));
try {
  const output = join(scratch, 'compiled');
  execFileSync(compactc, ['--skip-zk', source, output], { encoding: 'utf8' });
  const runtimeLink = join(output, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtime, runtimeLink, 'dir');
  const { pureCircuits } = await import(pathToFileURL(join(output, 'contract/index.js')).href);
  const generator = {
    x: 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798n,
    y: 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8n,
    identity: false,
  };
  const address = Buffer.from(pureCircuits.derive(generator)).toString('hex');
  assert.equal(address, '7e5f4552091a69125d5dfcb7b8c2659029395bdf');
  assert.throws(() => pureCircuits.derive({ x: 0n, y: 0n, identity: true }), /identity/i);
  console.log(`Compact ${version}: ${address}, identity rejected`);
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
