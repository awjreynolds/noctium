import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs';

const [compactc] = process.argv.slice(2);
assert.ok(compactc,
  'usage: node tests/compact/foreign-scalar-list-maybe.mjs <compactc-0.36.1>');
const compactVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compactVersion, /^0\.36\.1 \(7fa3a117c/, `unexpected Compact compiler: ${compactVersion}`);

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/ForeignScalarListMaybe.compact');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'foreign-scalar-list-maybe-'));

try {
  const scalarListControl = join(scratch, 'ForeignScalarListPush.compact');
  writeFileSync(scalarListControl, `pragma language_version 0.28;
import CompactStandardLibrary;

export ledger values: List<Secp256k1Scalar>;

export circuit push(value: Secp256k1Scalar): [] {
  values.pushFront(disclose(value));
}
`);
  const control = spawnSync(compactc, [
    '--skip-zk', scalarListControl, join(scratch, 'scalar-list-control'),
  ], { encoding: 'utf8' });
  assert.equal(control.status, 0,
    `Compact scalar List push control failed:\n${control.stderr || control.stdout}`);

  const probe = spawnSync(compactc, [
    '--skip-zk', source, join(scratch, 'scalar-list-maybe'),
  ], { encoding: 'utf8' });
  const diagnostic = probe.stderr || probe.stdout;
  assert.equal(probe.status, 254, `expected the pinned Compact compiler assertion:\n${diagnostic}`);
  assert.match(diagnostic,
    /failed assertion cannot-happen at line 518, char 18 of compiler\/zkir-v3-passes\/reduce-to-zkir\.ss/);

  console.log(JSON.stringify({
    compact: compactVersion,
    scalarListPush: 'compiled',
    scalarListHeadMaybe: {
      status: 'compiler-assertion',
      diagnostic: diagnostic.trim(),
    },
  }));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
