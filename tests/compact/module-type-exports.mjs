import assert from 'node:assert/strict';
import {execFileSync, spawnSync} from 'node:child_process';
import {existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync} from 'node:fs';
import {dirname, join, resolve} from 'node:path';
import {fileURLToPath, pathToFileURL} from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node module-type-exports.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const version = execFileSync(compactc, ['--version'], {encoding: 'utf8'}).trim();
assert.match(version, /^0\.36\.1 \(7fa3a117c/);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const fixture = join(dirname(fileURLToPath(import.meta.url)), 'ModuleTypeExports.compact');
const source = readFileSync(fixture, 'utf8');
const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, {recursive: true});
const scratch = mkdtempSync(join(experiments, 'module-type-exports-'));
const output = join(scratch, 'positive');

function compileFailure(name, declaration, expectedName) {
  const marker = 'export pure circuit inspect(';
  assert.equal(source.split(marker).length - 1, 1);
  const candidate = join(scratch, `${name}.compact`);
  const failedOutput = join(scratch, `${name}-output`);
  writeFileSync(candidate, source.replace(marker, `${declaration}\n\n${marker}`));
  const result = spawnSync(compactc, ['--skip-zk', candidate, failedOutput], {encoding: 'utf8'});
  assert.notEqual(result.status, 0, `${name} unexpectedly compiled`);
  assert.match(result.stderr, new RegExp(expectedName));
  assert.equal(existsSync(failedOutput), false);
}

try {
  execFileSync(compactc, ['--skip-zk', fixture, output], {encoding: 'utf8'});

  const info = JSON.parse(readFileSync(join(output, 'compiler/contract-info.json'), 'utf8'));
  const inspect = info.circuits.find(({name}) => name === 'inspect');
  const echoCount = info.circuits.find(({name}) => name === 'echoCount');
  assert.ok(inspect && echoCount, 'expected both selected-type circuits');
  const countType = {
    'type-name': 'Alias',
    name: 'Count',
    type: {'type-name': 'Uint', maxval: 255},
  };
  assert.deepEqual(inspect.arguments[0].type, {
    'type-name': 'Struct',
    name: 'Packet',
    elements: [
      {name: 'value', type: {'type-name': 'Field'}},
      {name: 'valid', type: {'type-name': 'Boolean'}},
    ],
  });
  assert.deepEqual(echoCount.arguments[0].type, countType);
  assert.deepEqual(echoCount['result-type'], countType);

  const declarations = readFileSync(join(output, 'contract/index.d.ts'), 'utf8');
  assert.match(declarations, /export type LocalCount = bigint;/);
  assert.match(declarations, /export type LocalPacket = \{ value: bigint; valid: boolean \};/);
  assert.match(declarations, /inspect\(packet_0: LocalPacket\): boolean;/);
  assert.match(declarations, /echoCount\(count_0: LocalCount\): LocalCount;/);
  assert.doesNotMatch(declarations, /Local(?:Unselected|Hidden)/);

  compileFailure('private-access',
    'export pure circuit privateAccess(value: LocalHidden): Field { return value.value; }',
    'LocalHidden');
  compileFailure('unselected-access',
    'export pure circuit unselectedAccess(value: LocalUnselected): Uint<16> { return value; }',
    'LocalUnselected');

  mkdirSync(join(scratch, 'node_modules', '@midnight-ntwrk'), {recursive: true});
  symlinkSync(runtimeDirectory,
    join(scratch, 'node_modules', '@midnight-ntwrk', 'compact-runtime'), 'dir');
  writeFileSync(join(output, 'package.json'), '{"type":"module"}');
  const generated = await import(pathToFileURL(join(output, 'contract/index.js')).href);
  assert.equal(generated.pureCircuits.inspect({value: 19n, valid: true}), true);
  assert.equal(generated.pureCircuits.echoCount(7n), 7n);
} finally {
  rmSync(scratch, {recursive: true, force: true});
}

console.log(`Compact ${version} passed selected type export parity for value 19 and Count 7`);
