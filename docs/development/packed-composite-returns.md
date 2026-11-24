# Packed composite returns

## Shielded burn address return

Compact 0.36.1 returns `shieldedBurnAddress()` as the logical object
`{is_left: true, left: {bytes: zero32}, right: {bytes: zero32}}`. The
existing Noctium helper retains this three-field type, including both nominal
address payloads, and exposes it through a composite return view.

## Packed return layout

The existing logical schema now supports an opt-in packed-byte return encoding
in `ReturnView`. Each descriptor gives the logical leaf offset and byte length,
the backing Native field names, and the FAB chunk widths. Ordinary return
views omit the metadata and retain their one-physical-field-per-leaf encoding.
The physical output contains five ordered Native fields.

1. `is_left` as Native 0 or 1.
2. Two packed chunks for `left.bytes`, with widths 1 and 31.
3. Two packed chunks for `right.bytes`, with widths 1 and 31.

Lean checks the selected ranges against checked byte layouts and verifies
chunk widths, ordering, uniqueness, and output names. Rust checks the metadata
again at the plan boundary, matches the offsets to actual `Bytes` nodes in the
schema, checks each chunk is below `2^(8 * chunkWidth)`, expands it to exact
little-endian bytes, then uses the existing aggregate schema decoder. This
preserves the logical record and the nominal wallet and contract address
identities while reducing the physical result from 65 Native fields to 5.
The opt-in encoding is part of the plan JSON.

## Qualification

The pinned Compact fixture checks both Either arms with nonzero bytes at
indexes 30 and 31. The Lean helper test checks matching Native chunks and
rejects a byte value of 256 before packing. A Rust runtime test reconstructs
the nonzero patterns into the same checked logical schema and rejects a chunk
that exceeds its declared one-byte width and metadata selecting a non-byte
field. The fresh ZKIR 3.2.1 relation has k=8 and 136 rows. The baseline
ShieldedBurn relation has k=10 and 675 rows. The packed relation text grows
from 2,920 bytes to about 5.5 KB while cutting the constraint rows.

The Rust artifact test checks the pinned zero wallet address in the logical
schema, generates and verifies a native proof with the official k8 SRS, and
rejects a changed return commitment. State remains unchanged and no ledger
effect is produced. The matrix tracks shielded settlement under its own entries.

The PrivateClaim source audit passed after reviewing the model change. The
export added the packed-field structure, constructor and recursor and changed
the return-view constructor and recursor. Both existing source proof roles
checked against the updated model pin.
