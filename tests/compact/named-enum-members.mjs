import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/named-enum-members.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

function assertCompileRejects(source, output, diagnostic) {
  const result = spawnSync(compactc, ['--skip-zk', source, output], { encoding: 'utf8' });
  assert.notEqual(result.status, 0, `${source} should fail to compile`);
  assert.match(result.stderr, diagnostic);
}

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'named-enum-members-'));
try {
  const generated = join(scratch, 'compact');
  execFileSync(compactc, [
    '--skip-zk', join(root, 'tests/compact/NamedEnumMembers.compact'), generated,
  ], { encoding: 'utf8' });
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const { pureCircuits } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const shieldedUser = pureCircuits.describe(0);
  const contract = pureCircuits.describe(2);
  const sameModuleEnumValue = pureCircuits.compareSameNamedEnums(0, 0);
  const differentModuleEnumValues = pureCircuits.compareSameNamedEnums(2, 1);
  const crossModuleCast = pureCircuits.castSameNamedEnum(2);
  assert.deepEqual(shieldedUser, [false, 2]);
  assert.deepEqual(contract, [true, 2]);
  assert.equal(sameModuleEnumValue, true);
  assert.equal(differentModuleEnumValues, false);
  assert.equal(crossModuleCast, 2);

  const distinctNames = join(scratch, 'distinct-enum-names.compact');
  writeFileSync(distinctNames, `
pragma language_version >= 0.28.0;
import CompactStandardLibrary;
enum Alpha { First, Second }
enum Beta { First, Second }
export pure circuit compare(left: Alpha, right: Beta): Boolean { return left == right; }
`);
  assertCompileRejects(
    distinctNames,
    join(scratch, 'distinct-enum-names-output'),
    /incompatible types [\s\S]* for equality\s+operator/,
  );

  const distinctCast = join(scratch, 'distinct-enum-cast.compact');
  writeFileSync(distinctCast, `
pragma language_version >= 0.28.0;
import CompactStandardLibrary;
enum Alpha { First, Second }
enum Beta { First, Second }
export pure circuit cast(value: Alpha): Beta { return value as Beta; }
`);
  assertCompileRejects(
    distinctCast,
    join(scratch, 'distinct-enum-cast-output'),
    /cannot cast from type Enum<Alpha, First, Second> to type Enum<Beta, First, Second>/,
  );

  for (const [label, rightVariants] of [
    ['order', 'ShieldedUser, Contract, UnshieldedUser'],
    ['set', 'ShieldedUser, UnshieldedUser, Merchant'],
  ]) {
    const incompatibleMembers = join(scratch, `incompatible-enum-${label}.compact`);
    writeFileSync(incompatibleMembers, `
pragma language_version >= 0.28.0;
import CompactStandardLibrary;
module LeftKinds { export enum RecipientKind { ShieldedUser, UnshieldedUser, Contract } }
module RightKinds { export enum RecipientKind { ${rightVariants} } }
import {RecipientKind as LeftRecipientKind} from LeftKinds;
import {RecipientKind as RightRecipientKind} from RightKinds;
export pure circuit compare(left: LeftRecipientKind, right: RightRecipientKind): Boolean { return left == right; }
`);
    assertCompileRejects(
      incompatibleMembers,
      join(scratch, `incompatible-enum-${label}-output`),
      /incompatible types [\s\S]* for equality\s+operator/,
    );
  }

  console.log(JSON.stringify({
    compiler: compilerVersion,
    runtime: runtimePackage.version,
    enum: { name: 'RecipientKind', members: ['ShieldedUser', 'UnshieldedUser', 'Contract'] },
    circuit: 'describe(choice)',
    inputs: { ShieldedUser: 0, Contract: 2 },
    outputs: { ShieldedUser: shieldedUser, Contract: contract },
    sameLeafNameEnumsAcrossModules: {
      accepted: true,
      equalValues: sameModuleEnumValue,
      differentValues: differentModuleEnumValues,
      castToAlias: crossModuleCast,
    },
    distinctEnumNames: { comparison: 'rejected', cast: 'rejected' },
    sameLeafNameEnumMembers: { differentOrder: 'rejected', differentSet: 'rejected' },
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
