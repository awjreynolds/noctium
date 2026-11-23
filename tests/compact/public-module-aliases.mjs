import assert from 'node:assert/strict';
import {execFileSync} from 'node:child_process';
import {mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync} from 'node:fs';
import {dirname, join, resolve} from 'node:path';
import {fileURLToPath, pathToFileURL} from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node public-module-aliases.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const version = execFileSync(compactc, ['--version'], {encoding: 'utf8'}).trim();
assert.match(version, /^0\.36\.1 \(7fa3a117c/);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const fixture = join(dirname(fileURLToPath(import.meta.url)), 'PublicModuleAliases.compact');
const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, {recursive: true});
const scratch = mkdtempSync(join(experiments, 'public-module-aliases-'));
const output = join(scratch, 'output');

try {
  execFileSync(compactc, ['--skip-zk', fixture, output], {encoding: 'utf8'});

  const info = JSON.parse(readFileSync(join(output, 'compiler/contract-info.json'), 'utf8'));
  const inspect = info.circuits.find(({name}) => name === 'inspect');
  const echoCount = info.circuits.find(({name}) => name === 'echoCount');
  assert.ok(inspect && echoCount, 'expected both re-exported type circuits');
  assert.deepEqual(inspect.arguments[0].type, {
    'type-name': 'Struct',
    name: 'Packet',
    elements: [
      {name: 'value', type: {'type-name': 'Field'}},
      {name: 'valid', type: {'type-name': 'Boolean'}},
    ],
  });
  const countType = {
    'type-name': 'Alias',
    name: 'Count',
    type: {'type-name': 'Uint', maxval: 255},
  };
  assert.deepEqual(echoCount.arguments[0].type, countType);
  assert.deepEqual(echoCount['result-type'], countType);

  const declarations = readFileSync(join(output, 'contract/index.d.ts'), 'utf8');
  assert.match(declarations,
    /inspect\(packet_0: \{ value: bigint, valid: boolean \}\): boolean;/);
  assert.match(declarations, /echoCount\(count_0: bigint\): bigint;/);
  assert.doesNotMatch(declarations, /Local(?:Hidden|Unselected)/);

  mkdirSync(join(scratch, 'node_modules', '@midnight-ntwrk'), {recursive: true});
  symlinkSync(runtimeDirectory,
    join(scratch, 'node_modules', '@midnight-ntwrk', 'compact-runtime'), 'dir');
  writeFileSync(join(output, 'package.json'), '{"type":"module"}');
  const generated = await import(pathToFileURL(join(output, 'contract/index.js')).href);
  assert.equal(generated.pureCircuits.inspect({value: 19n, valid: true}), true);
  assert.equal(generated.pureCircuits.inspect({value: 19n, valid: false}), false);
  assert.equal(generated.pureCircuits.echoCount(7n), 7n);
} finally {
  rmSync(scratch, {recursive: true, force: true});
}

console.log(`Compact ${version} passed generic nested module alias checks`);
