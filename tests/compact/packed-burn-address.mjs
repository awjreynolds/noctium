import assert from 'node:assert/strict';
import {resolve} from 'node:path';
import {pathToFileURL} from 'node:url';

const generated = process.argv[2];
assert.ok(generated, 'usage: node packed-burn-address.mjs <generated contract module>');
const {pureCircuits} = await import(pathToFileURL(resolve(generated)));
const bytes = Uint8Array.from({length: 32}, (_, index) => (index * 7) & 0xff);
bytes[30] = 0xa5;
bytes[31] = 0x5a;
const zero = new Uint8Array(32);

assert.deepEqual(pureCircuits.wallet(bytes), {
  is_left: true,
  left: {bytes},
  right: {bytes: zero},
});
assert.deepEqual(pureCircuits.contractRecipient(bytes), {
  is_left: false,
  left: {bytes: zero},
  right: {bytes},
});
console.log('Compact Either fixtures preserve nonzero Bytes32 values across byte 31/32.');
