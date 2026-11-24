import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/public-address-value.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/,
  `expected pinned Compact 0.36.1 compiler, got ${compilerVersion}`);
const runtimeDirectory = resolve(runtimePath);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0', 'expected pinned Compact runtime 0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'public-address-value-'));

try {
  const generated = join(scratch, 'compact');
  const source = join(projectRoot, 'tests/compact/PublicAddressValue.compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtimeUrl = pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href;
  const contractUrl = pathToFileURL(join(generated, 'contract/index.js')).href;
  const { createCircuitContext, createConstructorContext, dummyContractAddress } = await import(runtimeUrl);
  const { Contract } = await import(contractUrl);
  const contract = new Contract({});
  const wallet = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(createConstructorContext(null, wallet));
  const state = currentContractState.data;
  const bytes = (value) => new Uint8Array(32).fill(value);
  const invoke = async (circuitId, ...args) => {
    const context = createCircuitContext({
      circuitId,
      contractAddress: dummyContractAddress(),
      coinPublicKeyOrZswapState: wallet,
      contractState: state,
      privateState: null,
    });
    return contract.circuits[circuitId](context, ...args).then(({ result }) => result);
  };
  const expectedAddress = (contractByte, userByte) => ({
    is_left: true,
    left: { bytes: bytes(contractByte) },
    right: { bytes: bytes(userByte) },
  });

  for (const isLeft of [true, false]) {
    const value = {
      is_left: isLeft,
      left: { bytes: bytes(1) },
      right: { bytes: bytes(2) },
    };
    const result = await invoke('echo', value);
    assert.equal(result.is_left, isLeft, `echo changed tag ${isLeft}`);
    assert.deepEqual(result.left, value.left, `echo changed ContractAddress arm for tag ${isLeft}`);
    assert.deepEqual(result.right, value.right, `echo changed UserAddress arm for tag ${isLeft}`);
  }

  const contractResult = await invoke('asContract', bytes(1));
  assert.deepEqual(contractResult, expectedAddress(1, 0));
  const userResult = await invoke('asUser', bytes(2));
  assert.deepEqual(userResult, {
    is_left: false,
    left: { bytes: bytes(0) },
    right: { bytes: bytes(2) },
  });

  await assert.rejects(invoke('echo', {
    is_left: 'true',
    left: { bytes: bytes(1) },
    right: { bytes: bytes(2) },
  }), 'echo accepted a malformed Either tag');
  await assert.rejects(invoke('echo', {
    is_left: false,
    left: { bytes: bytes(1).subarray(1) },
    right: { bytes: bytes(2) },
  }), 'echo accepted a 31-byte ContractAddress arm');
  await assert.rejects(invoke('echo', {
    is_left: true,
    left: { bytes: bytes(1) },
    right: { bytes: bytes(2).subarray(1) },
  }), 'echo accepted a 31-byte UserAddress arm');

  console.log(JSON.stringify({
    fixture: 'PublicAddressValue',
    compact: compilerVersion,
    runtime: runtimePackage.version,
    echoTags: [true, false],
    echoArms: ['01'.repeat(32), '02'.repeat(32)],
    asContract: { is_left: true, active: '01'.repeat(32), inactive: '00'.repeat(32) },
    asUser: { is_left: false, active: '02'.repeat(32), inactive: '00'.repeat(32) },
    rejected: ['malformed tag', '31-byte ContractAddress', '31-byte UserAddress'],
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
