# OpenZeppelin confidential-token compilation benchmark

The latest November 19 development benchmark measured **3.69 s for Noctium** and **0.285 s for Compact 0.36.1**. Noctium used a prebuilt compiler and native Lean library from a development worktree based on `cedb6ef`, including uncommitted compiler changes. The [machine-readable sample](oz-compile-performance.json) records the revision, source and executable hashes.

The builds use different contract interfaces, state paths and artifact sets. Noctium ran with range deduplication and emitted ledger and witness artifacts with zero SDK bindings. Compact ran with `--skip-zk`. Both excluded key generation and proving.

![Noctium and Compact compilation time and per-entrypoint circuit K and rows](../assets/noctium-performance.png)

| Source compiler | Three alternating runs (s) | Median (s) | Files | Total bytes | ZKIR bytes |
| --- | ---: | ---: | ---: | ---: | ---: |
| Noctium development build | 4.166 / 3.675 / 3.694 | 3.69 | 53 | 2,596,304 | 304,477 |
| Compact 0.36.1 | 0.290 / 0.276 / 0.285 | 0.285 | 20 | 517,229 | 167,669 |

Each run used a fresh process, a fresh output directory and warm dependencies on the same Apple M3 Max with 48 GiB RAM. Each compiler reproduced its output bytes across its three runs. The previous sample measured 3.65 s for the same Noctium executable and native library. Noctium emits 16 ledger relations, Impact plans and witness artifacts. Compact emits 15 relations and JavaScript and TypeScript artifacts. Compact implements `computeAccountId` in JavaScript. Noctium's corresponding circuit measured K13 and 1,993 rows.

| Entrypoint | Noctium K | Noctium rows | Compact K | Compact rows | Row difference |
| --- | ---: | ---: | ---: | ---: | ---: |
| `_move` | 16 | 38,621 | 16 | 37,994 | +627 |
| `allowance` | 9 | 464 | 9 | 435 | +29 |
| `approve` | 16 | 37,856 | 16 | 38,349 | -493 |
| `balanceOf` | 8 | 228 | 10 | 901 | -673 |
| `burn` | 14 | 14,645 | 14 | 13,825 | +820 |
| `burnFrom` | 16 | 37,739 | 16 | 38,294 | -555 |
| `clearMemos` | 13 | 6,681 | 13 | 6,573 | +108 |
| `isRegistered` | 7 | 120 | 8 | 129 | -9 |
| `mint` | 15 | 24,978 | 15 | 25,140 | -162 |
| `pendingOf` | 8 | 228 | 10 | 901 | -673 |
| `registerWithKey` | 13 | 6,687 | 13 | 7,540 | -853 |
| `sweep` | 13 | 6,832 | 13 | 7,287 | -455 |
| `totalSupply` | 7 | 66 | 6 | 34 | +32 |
| `transfer` | 16 | 38,629 | 16 | 38,002 | +627 |
| `transferFrom` | 16 | 61,110 | 16 | 62,483 | -1,373 |

The pinned ZKIR 3.2.1 sizing tool measured every relation. Of the 15 pairings by name, Noctium used fewer rows in 9 and more in 6. Its K was lower in 3, equal in 11, and higher in 1. `totalSupply` used K7 in Noctium and K6 in Compact. These measurements cover source builds and circuit sizing.

## Earlier source compilation

| Compiler output | Three source runs (s) | Median (s) |
| --- | ---: | ---: |
| Noctium ledger and witness, minified plans | 4.57 / 4.45 / 4.45 | 4.45 |
| Noctium ledger and witness, plan digests | 6.00 / 4.59 / 4.58 | 4.59 |
| Noctium ledger and witness, paired baseline | 4.873 / 4.647 / 4.588 | 4.647 |
| Compact 0.36.1 with `--skip-zk` | 0.274 / 0.286 / 0.274 | 0.274 |

The paired baseline used three alternating runs on an Apple M3 Max with prebuilt compilers, warm dependencies, fresh processes and new output directories. The Noctium follow-ups ran on the same machine. All three minified-plan runs reproduced the emitted bytes. The ABI, state handling and artifact sets differ. [Machine-readable measurements and hashes](oz-compile-performance.json)

### Artifact inventory

| Compiler output | Output files | Total bytes | ZKIR bytes |
| --- | ---: | ---: | ---: |
| Noctium ledger and witness, minified plans | 53 | 3,707,277 | 704,238 |
| Noctium ledger and witness, plan digests | 53 | 4,542,348 | 758,817 |
| Noctium ledger and witness, paired baseline | 53 | 5,805,683 | 758,817 |
| Compact 0.36.1 with `--skip-zk` | 20 | 518,022 | 167,669 |

Noctium exports 16 ZKIR relations, 16 Impact ledger plans, 10 witness bindings,
10 language-neutral witness execution plans and `noctium.json`. The plans and
their embedded metadata account for most of Noctium's bytes. The timing command
requests zero SDK bindings. Compact exports 15 ZKIR relations, one JavaScript
module, a source map, a TypeScript declaration and two metadata files.
`computeAccountId` runs in JavaScript in the Compact build. Byte counts use the
files emitted before sizing. The circuit comparison below uses K and rows.

The ledger-only manifest now records each Impact plan's SHA-256 digest. The
manifest shrank from 1,348,540 to 85,205 bytes, reducing total output by 21.8%.
All other 52 files matched byte for byte. For three matched runs per version,
median source time rose from 4.38 s to 4.59 s and median user CPU rose from
3.46 s to 3.70 s. For each hosted entrypoint, the execution plan still embeds
the binding, and the binding embeds the ZKIR relation. The runtime checks
these associations when loading the artifacts. [Artifact verification](portable-artifacts.md)

## Historical source compilation

Apple M3 Max, 16 logical cores, 48 GiB RAM. Compilers were prebuilt, dependencies were warm, each run used a fresh process and output directory. Setup/download time, key generation, proving and deployment are excluded.

| Compiler | Three runs (seconds) | Median | Peak observed RSS |
| --- | --- | --- | --- |
| Noctium `adbc42c`, Lean 4.35.0 | 61.350 / 61.811 / 62.504 | 61.811 s | 1.50 GiB |
| Compact 0.36.1, `--skip-zk` | 0.277 / 0.255 / 0.255 | 0.255 s | 0.260 GiB |

These timings cover source processing and emitted artifacts. Noctium emits 16 native entrypoint relations, 13 standalone helper relations, Impact plans and witness/metadata sidecars. Compact emits 15 provable relations, one pure JavaScript function (`computeAccountId`), JavaScript/types and metadata. The workloads have comparable functions but different input/result layouts, explicit state-candidate handling and artifact sets. This is not a proven semantic/ABI equivalence benchmark.

## Single-pass Noctium follow-up

| OpenZeppelin port, ZKIR 3.2.1 | Wall | User CPU | System CPU |
| --- | ---: | ---: | ---: |
| Two Lean passes, `7643dc6` | 65.94 s | 62.96 s | 1.40 s |
| One Lean pass | 41.29 s | 39.51 s | 0.71 s |
| One Lean pass and witness compilation reuse | 38.90 s | 35.46 s | 0.83 s |

The combined changes saved 27.04 seconds (41%) in one matched run per version on the same M3 Max. The exporter reused 10 compiled witness plans when binding them to ledger entrypoint relations. All three runs generated 93 byte-identical files totaling 7,697,562 bytes. The CLI publishes the bundle directory after Lean exits successfully with a manifest. A late source error or early exit leaves no output directory or staging files, and a nonempty destination stays untouched. [Optimization issue](https://github.com/awjreynolds/noctium/issues/85)

## Reuse the Impact plan during export

The exporter now writes the Impact plan returned by the checked ZKIR lowerer. The native producer still derives its expected schedule independently from the pruned source. This removes one repeat of Impact lowering for each of the port's 16 entrypoints.

One before-and-after pair on the same M3 Max emitted all 93 files byte for byte, totaling 7,697,562 bytes. The baseline at `8a697a1` used 34.79 s of user CPU and the revised exporter used 34.72 s. Elapsed time was 41.76 s and 36.32 s respectively. The near-identical user CPU and the single pair leave the speedup unestablished. Identical relations preserve the existing K values. [Circuit-size issue](https://github.com/awjreynolds/noctium/issues/74)

## Exact range-check deduplication

The initial `--dedup-range-checks` pass kept the first unconditional check for each SSA operand and width. On the OpenZeppelin port, it removed 402 repeated checks across 11 of 29 emitted relations. Impact plans matched byte for byte. Witness bindings referenced the corresponding relation in each build.

| Changed entrypoint, ZKIR 3.2.1 | Checks removed | Default rows | Deduplicated rows | K in both builds |
| --- | ---: | ---: | ---: | ---: |
| `_move` | 42 | 41,779 | 39,175 | 16 |
| `approve` | 50 | 41,575 | 38,475 | 16 |
| `burn` | 20 | 16,323 | 15,083 | 14 |
| `burnFrom` | 27 | 39,122 | 38,258 | 16 |
| `transfer` | 42 | 41,787 | 39,183 | 16 |
| `transferFrom` | 41 | 63,125 | 61,813 | 16 |

The pinned `mock-compile` measured 2.1% to 7.6% fewer rows across these entrypoints. The pinned native checker gave the same results for 34 scalar cases in both modes, including acceptance at 255 and rejection at 256 when narrowing to eight bits. One serial full compile per mode took 36.57 and 35.69 seconds respectively, with nearly identical CPU time. These runs did not measure proving time. Generate fresh proving and verifier keys for any changed relation. [Circuit-size issue](https://github.com/awjreynolds/noctium/issues/74)

The current opt-in pass also removes a wider check when an earlier unconditional check already constrains the same operand. On this port, seven more 248-bit checks follow a 128-bit check on the same value. The pass removes 409 checks in total across 11 relations. Pinned synthesis reports 62 fewer rows in each affected ledger entrypoint (`_move`, `approve`, `burn` and `transfer`). For example, `transfer` drops from 39,183 to 39,121 rows and stays at K16. Impact files remain byte-identical and all 34 raw-witness cases agree with the default compiler.

Lean checks `RangeDedup.preserves_decoded` against the actual JSON pass and the independent scalar ZKIR decoder. For instruction lists accepted by that decoder, the optimized list also decodes, preserves ordered non-range instructions, and has the same satisfying assignments. The model covers the scalar decoder's instruction set. The ZKIR verifier, expanded instruction set and ledger execution require separate evidence. [Preservation theorem](../../Noctium/Verification/RangeDedup.lean)

## Reuse identical byte selections

Byte chunks now reuse the same exact-operand selector cache as scalars. The compiler still lowers both arms, including any assertions they contain. The cache compares the selector and both ordered SSA operands. [ZKIR lowerer](../../Noctium/Backend/Zkir.lean)

Nine of the token port's 16 ledger relations emitted fewer selectors. The pinned ZKIR 3.2.1 tool measured the following changes with the opt-in range pass disabled.

| Entrypoint | Selectors before → after | Rows before → after | K before → after |
| --- | ---: | ---: | ---: |
| `allowance` | 41 → 33 | 513 → 505 | 10 → 9 |
| `transferFrom` | 35 → 25 | 63,125 → 63,115 | 16 → 16 |
| `NativeBytes.inspect` | 18 → 6 | 1,137 → 1,108 | 11 → 11 |

The 16 token Impact plans matched byte for byte. The fresh byte fixture passed both branches and the altered-result rejection in the native checker. The fresh token allowance relation passed the existing token workload's empty and populated allowance checks. These measurements cover circuit sizing. Proving latency and fresh deployments of the changed token relations remain unmeasured. [Issue 74](https://github.com/awjreynolds/noctium/issues/74)

## Remove zero-seed arithmetic from byte packing

The byte packer starts from the highest byte in each nonempty chunk. Previously it multiplied zero by 256 and added the highest byte. The independent producer still checks the packed expression, input bounds and ordered transcript. [ZKIR packer](../../Noctium/Backend/Zkir.lean) · [Source normalization](../../Noctium/Backend/NativeMeaning.lean)

| Workload | Instructions before → after | Rows before → after | K |
| --- | ---: | ---: | ---: |
| Byte pack and reverse | 761 → 754 | 1,144 → 1,137 | 11 |
| Byte storage including Bytes1024 | 4,809 → 4,767 | 11,608 → 11,567 | 14 |
| Token `sweep` | 517 → 513 | 7,076 → 7,073 | 13 |
| Token `transfer` | 1,247 → 1,242 | 41,783 → 41,779 | 16 |
| Token `transferFrom` | 1,328 → 1,322 | 63,115 → 63,110 | 16 |

The comparison starts at `b8b469c`, with `--emit ledger --emit witness` and the default range-pass setting. Pinned `mock-compile` reported fewer rows in 14 of 16 token relations. All Impact plans matched byte for byte. The native byte pack test accepted the regenerated relation and rejected a forged result. The scalar CSE fixture emitted identical bytes. A single token compile in each mode took 4.70 s and 4.68 s. This establishes a small circuit-size reduction. Proof time and funded deployment fall outside this measurement. [Byte packing test](../../runtime/tests/native_byte_packing.rs) · [Issue 74](https://github.com/awjreynolds/noctium/issues/74)

## Fold literal Bytes32 hash-vector packing

A direct Bytes32 literal in a hash vector now uses its canonical FAB fields
as immediates. The compiler retains symbolic packing and input constraints.
The independent producer checks the same ordered hash operands.

| Workload | Instructions before → after | Rows before → after | K |
| --- | ---: | ---: | ---: |
| One literal and one private Bytes32 | 187 → 127 | 3,999 → 3,949 | 13 |
| Token `transferFrom` | 1,281 → 1,005 | 61,798 → 61,522 | 16 |

Across the 16 token relations, this removed 1,353 instructions and 1,312 rows
in ten relations. The other six relations and all Impact plans matched byte
for byte. K stayed the same for every entrypoint. Pinned ZKIR 3.2.1
`mock-compile` measured these sizes with range deduplication enabled for the
token. Both mixed-vector builds matched the Compact runtime 0.21.0 digest
and rejected a changed return commitment in the native checker.
[Optimization ticket](https://github.com/awjreynolds/noctium/issues/403) · [Native fixture](../../runtime/tests/native_byte_packing.rs)

## Fold literal Native zero in addition

The lowerer evaluates both operands in order and reuses the other operand
when a source operand is the Native literal zero. The source normalization
proof retains both operands' bounds and assertions. A focused circuit
removed three `add` instructions and its ledger form removed four. Both
kept their input order, four assertions and the intended public output.

All 16 ConfidentialToken relations and Impact plans matched the baseline
bytes. `transferFrom` used 1,005 instructions and 61,522 rows at K16 in
both builds. The native workload accepted transfer and rejected overspend
with each build's matching witness control files. The earlier combined
experiment also folded UInt additions. That rule has a separate range-check
requirement. [Native fold](https://github.com/awjreynolds/noctium/issues/211) ·
[UInt fold](https://github.com/awjreynolds/noctium/issues/770) ·
[Focused regression](../../tests/ScalarCseParity.lean)

## Fold literal UInt zero in addition

The UInt fold eagerly lowers both operands and applies the sum's original
range constraint to the surviving value. The focused fixture checks both
operand orders, including a non-power-of-two bound. Lean checks source
normalization and the lowering action's output-capacity frame.

All 16 pinned ConfidentialToken relations and Impact plans matched the
baseline bytes. `transferFrom` stayed at 1,005 instructions and 61,522 rows
at K16. Both native runs accepted transfer and rejected overspend. The
remaining `transferFrom` zero arithmetic runs inside byte packing, where
an all-zero chunk emits 30 adds and 30 multiplies. [UInt fold](https://github.com/awjreynolds/noctium/issues/770) ·
[Packing ticket](https://github.com/awjreynolds/noctium/issues/775) ·
[Focused regression](../../tests/ScalarCseParity.lean)

## Fold all-zero FAB chunks

The packer emits a zero immediate for a chunk of already-lowered zero bytes.
Mixed and dynamic chunks retain symbolic packing. The independent producer
checks the matching expected term.

| ConfidentialToken entrypoint | Instructions before → after | Rows before → after | K before → after |
| --- | ---: | ---: | ---: |
| `balanceOf` | 116 → 56 | 264 → 234 | 9 → 8 |
| `pendingOf` | 116 → 56 | 264 → 234 | 9 → 8 |
| `transferFrom` | 1,005 → 945 | 61,522 → 61,492 | 16 → 16 |

Pinned ZKIR 3.2.1 `mock-compile` measured 30 fewer rows in each of nine
changed relations. The whole suite's raw ZKIR went from 617,257 to 582,980
bytes. Seven relations and all 16 Impact plans matched byte for byte.
The native workload accepted transfer and rejected overspend with the
matching witness files. The PrivateClaim relation matched its baseline
SHA-256. [Packing ticket](https://github.com/awjreynolds/noctium/issues/775) ·
[Focused packing checks](../../tests/NativeBytePacking.lean)

## Fold consecutive zero bytes in a mixed chunk

The packer combines consecutive low-order literal zero bytes into one
multiplication by the corresponding power of 256. The native producer
derives the same expression. Lean checks the little-endian value and
preservation of the output allocation bound.

For the focused 31-byte fixture with 30 literal zero bytes and one private
byte, ZKIR 3.2.1 sizing measured 52 rows before and 23 after, both at K9.
The relation uses one multiplication in place of 30. [Focused packing checks](../../tests/NativeBytePacking.lean)

## Reuse existing byte leaves

Static slices select byte leaves directly when the inputs already use that
representation. The two-byte result in `inspectPayment` also avoids serializing
each range-checked byte as a full field. Pinned ZKIR 3.2.1 `mock-compile` measured
the following changes.

| Entrypoint | Rows before | Rows after | K before → after |
| --- | ---: | ---: | ---: |
| `NativeBytes.inspect` | 1,137 | 1,067 | 11 → 11 |
| `readPayment` | 298 | 275 | 9 → 9 |
| `inspectPayment` | 1,545 | 1,194 | 11 → 11 |
| `inspectPayment` with range-check removal | 1,194 | 730 | 11 → 10 |
| `inspectPayment` with comparison reuse added | 730 | 352 | 10 → 9 |

At the time of this measurement, `--dedup-range-checks` applied both range optimizations. The
comparison pass keeps two distinct `less_than` gates and replaces 63 repeated
gates with copies. It uses the same ordered SSA operands and bit width, and
keeps the output names and all assertion sites. The independent producer
validates the optimized relation. The six aggregate native cases pass,
including altered-frame rejection. The sizing run excludes key generation
and proving. [Issue 74](https://github.com/awjreynolds/noctium/issues/74)

A focused run on `febc3b33` isolates the current comparison opt-in for
`inspectPayment`. The default and flagged builds each emit 215 instructions.
The flag replaces 63 of 65 `less_than` instructions with `copy`. The pinned
ZKIR 3.2.1 tool measures 708 rows at K10 by default and 330 rows at K9 with
the flag. Both native executions return the same named aggregates and reject
a modified private frame under the original commitment. The Impact plan
matches byte for byte. Witness metadata changes only where it embeds the
new relation. The same paired PrivateClaim build reproduces all three files
byte for byte. [Comparison acceptance issue](https://github.com/awjreynolds/noctium/issues/691)

| `inspectPayment` artifact | SHA-256 |
| --- | --- |
| Default relation | `a70f2f66bfb89f48e76ed482170b1a6e6db273ff322c534271d718d9482dc2a2` |
| Opt-in relation | `9f7494528fcb49e07b74a116a3300b1ccfd8fa0fec91f04e05b134a96c2602fa` |
| Impact plan for both builds | `65cce3f9c946bc3954f79bff52a2bfafc665ec95306e47ba2c43edcd5e8d5336` |

A matched OpenZeppelin token run on the same M3 Max compiled all 16 ledger
entrypoints and witness artifacts in 4.75 s with the flag off and 4.67 s with
it on. `transferFrom` used 63,110 and 61,798 rows respectively at K16. The
Impact files matched exactly. The token had no repeated bounded comparisons
for the new pass to remove. These two runs measure one pair, with no
established compile-time change.

The same option now keeps the first unconditional `assert` on each immutable
SSA condition. The producer still checks the first occurrence of each
distinct source assertion in order. The readable iteration fixture emitted
47 instructions with the range pass and 33 with assertion deduplication
added. ZKIR 3.2.1 mock compilation reported 108 and 94 rows, both at K7. The
Impact plan matched byte for byte, and the native runtime test passed with the
optimized relation. [Issue 503](https://github.com/awjreynolds/noctium/issues/503)

## Reuse checked Jubjub coordinates

The compiler reuses a reconstructed Jubjub point only after emitting both
coordinate roundtrip equalities. Further uses of the same ordered SSA operands
reuse the checked point. The native producer still requires both equalities.

The OpenZeppelin ledger-and-witness export removes 882 repeated equality
instructions across ten relations. `transfer` drops from 1,199 to 901
instructions. ZKIR shrinks from 758,817 to 704,238 bytes, and total output
shrinks from 4,542,348 to 4,383,973 bytes. The file count and all 16 Impact
plans stay the same. Pinned ZKIR 3.2.1 reports the same K and row counts for
each modified relation. The refreshed CurveHelpers native case produces the
expected ciphertext and rejects a wrong key. [Focused test](../../runtime/tests/witness_control.rs)

## Selected ledger outputs

One serial run per mode on the same host compared a full compile with `--emit ledger --emit witness`. Both runs used the same executable, source and ZKIR 3.2.1 profile.

| Compiler outputs | Wall | User CPU | System CPU | Files | Bytes |
| --- | ---: | ---: | ---: | ---: | ---: |
| All | 35.64 s | 34.79 s | 0.68 s | 93 | 7,697,562 |
| Ledger and witness | 32.21 s | 31.42 s | 0.62 s | 53 | 5,868,886 |

The selected run saved 3.43 seconds (9.6%) and 1,828,676 bytes (23.8%). It retained all 16 entrypoints and ten ledger witness pairs. ZKIR and witness bytes matched. The selected plans removed only the unused standalone file property. The compiler manifest records the emitted paths and roles. [Compiler output roles](portable-artifacts.md#select-compiler-outputs)

The ledger export now writes minified Impact JSON when the build omits
standalone circuits. On the OpenZeppelin port the 16 plans shrank from
1,842,372 to 1,165,676 bytes. Total output dropped from 4,383,973 to 3,707,277
bytes (15.4%). All decoded plans matched, each digest matched the exact emitted
bytes, and all 36 ZKIR and witness files matched byte for byte. The build
still emits 53 files.

## Precompiled Lean frontend

A CPU sample of the OpenZeppelin compile showed Lean's IR interpreter among the busiest active frames. The CLI now loads the native shared library built by Lake when Lake reports a current artifact. The interpreter handles missing and stale builds. Both paths use the same source elaboration and compiler checks. [Lake library builds](https://lean-lang.org/doc/reference/latest/releases/v4.35.0/) · [CLI frontend](../../Noctium/Cli.lean)

| OpenZeppelin port, ZKIR 3.2.1, ledger and witness | Wall | User CPU | System CPU |
| --- | ---: | ---: | ---: |
| Before native library loading, `03ebadf` | 32.02 s | 31.20 s | 0.69 s |
| CLI with Lake-checked native library | 6.01 s | 4.14 s | 0.87 s |

These are two serial runs on the same M3 Max with warm dependencies. All 53 files matched byte for byte, including 16 native relations. The reduction was 81.2% in wall time. The shared library measured 14.6 MB on macOS. Source timing excludes building the compiler, generating keys and producing proofs. The earlier Compact timing used a different output set and appears in the historical baseline above.

## Reuse checked source sizes

Helper analysis now reuses the source-size results from program preparation.
The compiler still checks the weighted expansion budget and checks the expanded
source after lowering a finite range. Three matched OpenZeppelin runs on the
same M3 Max took 4.89, 4.64 and 4.74 s before this change, and 6.05, 4.68 and
4.62 s after. All 53 compiler artifacts matched byte for byte across the
matched runs. The timings establish no material throughput improvement.
The CPU sample put ZKIR's linear common-subexpression lookup among the busiest
Noctium functions. Its representation also appears in the lowering theorems.

## Reuse witness compilation during export

The exporter now reuses the checked witness plans created during source
elaboration. The cache lives for one compiler invocation. A ledger binding
still uses the checked ledger relation. The exporter rebuilds module sources
and recompiles a standalone witness plan when the requested range option
changes its relation.

Three OpenZeppelin ledger-and-witness runs took 4.86, 4.62 and 4.57 s before
the change and 5.91, 4.43 and 4.53 s after. Median user CPU fell from 3.76 s to
3.64 s. All 53 artifacts matched byte for byte. The hosted argument fixture
and the mixed result fixture also reproduced their range-deduplicated output.
The wall times varied across runs.

Witness registration now checks disclosure on the circuit it already compiled.
Previously it evaluated the generated Lean definition, which ran witness
compilation again. Three OpenZeppelin ledger-and-witness runs took 4.76, 4.75
and 4.57 s before the change and 5.87, 4.44 and 4.49 s after. Median user CPU
fell from 3.68 s to 3.49 s. All 53 artifacts matched byte for byte. The private
state fixture still rejects an implicit public release and accepts an explicit
one. This change removes compiler work and leaves circuit sizes unchanged.

Readable declarations now reuse the same checked compilation to build output
aliases and aggregate views and to register the witness circuit. Three
OpenZeppelin runs took 4.42, 4.34 and 4.41 s before the change and 5.69, 4.40
and 4.31 s after. Median user CPU fell from 3.47 to 3.40 s. All 53 OpenZeppelin
artifacts and the full aggregate example matched byte for byte. A rejected
private release leaves the declaration name available for a corrected command.

## What the timing includes

The older Noctium baseline ran two complete Lean frontend passes. The first checked the source. The second elaborated it again and exported artifacts. The follow-up times these workflows end to end.

The token source declares no contract theorems. Neither timed command generates cryptographic ZK proofs or keys. Lean theorem checking and transaction ZK proof generation are separate operations. This benchmark does not establish functional correctness of the contract or compiler.

## Contract size and functionality

The [Noctium port](../../examples/openzeppelin/ConfidentialToken.lean) contains 1,013 physical lines, 967 nonblank lines excluding full-line comments, 16 entrypoints, 12 public state slots, two private cells and 13 witness/circuit definitions. These source counts exclude imported compiler/library implementation.

The exact [OpenZeppelin wrapper](https://github.com/OpenZeppelin/compact-contracts/blob/f85f1a23685c6bbedfc8c2589ae3aa128aff7c46/contracts/test/integration/_mocks/ComposedConfidentialFungibleTokenPublicSupply.compact) contains 144 lines and imports the 1,512-line [token module](https://github.com/OpenZeppelin/compact-contracts/blob/f85f1a23685c6bbedfc8c2589ae3aa128aff7c46/contracts/src/token/ConfidentialFungibleToken.compact), the public-supply extension and crypto helpers. Comparing only the 144-line wrapper with the full Lean file would misrepresent source size.

The workload includes ElGamal encrypted balances on Jubjub, pending credits, ECDH memos, account/key registration, transfers, sweeping, mint/burn, delegated escrow spending, allowances, counters, nested maps/lists and private wallet witnesses. The existing isolated-localnet scenario covers all sixteen entrypoints. Nominal ABI and composition qualifications remain separate.

## Native circuit sizes

Both artifact sets were sized using the same pinned native ZKIR 3.2.1 implementation, revision `7a51b3385bbf4bce3604df87a7c70867c9ab43c0`. Its executable banner still says 3.2.0; the recorded source pin and binary SHA identify the selected patch. Sizing uses `mock-compile`, which builds the circuit model without generating keys or proofs.

Compact 0.36.1 also compiled a standalone test contract whose only operation
assigned `disclose(next)` to a `Field` ledger cell. The ordinary compile
generated the prover and verifier keys. Compact's bundled tool and the
independent pinned 3.2.1 tool both sized the emitted relation at K6 and 36 rows.
[Compact release](https://github.com/midnightntwrk/compact/releases/tag/compactc-v0.36.1)

K and rows describe each circuit. The table groups relations by entrypoint name and uses Noctium's range-deduplicated export. Δ rows and Δ % use Compact as the baseline. Noctium uses fewer rows for seven names and more for eight. Its K is lower for three and higher for one. The separate behavior checks below record where the artifact boundaries differ.

| Entrypoint | Noctium K | Noctium rows | Compact K | Compact rows | Δ rows | Δ % |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `registerWithKey` | 13 | 6,929 | 13 | 7,540 | -611 | -8.1% |
| `mint` | 15 | 25,230 | 15 | 25,140 | +90 | +0.4% |
| `sweep` | 13 | 7,073 | 13 | 7,287 | -214 | -2.9% |
| `transfer` | 16 | 39,113 | 16 | 38,002 | +1,111 | +2.9% |
| `_move` | 16 | 39,105 | 16 | 37,994 | +1,111 | +2.9% |
| `burn` | 14 | 15,017 | 14 | 13,825 | +1,192 | +8.6% |
| `clearMemos` | 13 | 6,921 | 13 | 6,573 | +348 | +5.3% |
| `totalSupply` | 7 | 66 | 6 | 34 | +32 | +94.1% |
| `isRegistered` | 7 | 120 | 8 | 129 | -9 | -7.0% |
| `balanceOf` | 9 | 264 | 10 | 901 | -637 | -70.7% |
| `pendingOf` | 9 | 264 | 10 | 901 | -637 | -70.7% |
| `computeAccountId` | 13 | 2,083 | Pure JS | n/a | n/a | n/a |
| `approve` | 16 | 38,403 | 16 | 38,349 | +54 | +0.1% |
| `allowance` | 9 | 504 | 9 | 435 | +69 | +15.9% |
| `transferFrom` | 16 | 61,798 | 16 | 62,483 | -685 | -1.1% |
| `burnFrom` | 16 | 38,248 | 16 | 38,294 | -46 | -0.1% |

The earlier native sizing and instruction counts are retained in the [machine-readable benchmark](oz-compile-performance.json). Circuit sizing measures synthesis rows and K. It excludes proving latency.

An isolated issue 74 sizing probe on base `2066c7c1` changed only
`cell totalSupply : UInt 128` to `cell totalSupply : UInt 128 alignedBytes` in
a scratch copy of `ConfidentialToken.lean`. The strict aligned variant measured
K7 and 66 rows, the same size as the unmodified field-aligned source. Adding
`--ledger-read-bound OpenZeppelinPort.ConfidentialToken.totalSupply` removed
only `constrain_bits %input_currentSupply, 128` and measured K6 and 34 rows
with the pinned `zkir mock-compile`. The source change also changes the ledger
layout. The default cell uses field encoding. The `alignedBytes` declaration
emits `cellAlignment: "u128"` and stores one 16-byte FAB atom. The aligned
strict and optimized Impact plans match byte for byte. The Compact comparison
above uses the default Noctium field layout.

## Matched totalSupply on the 16-byte supply cell

| Artifact | K | Synthesis rows |
| --- | ---: | ---: |
| Noctium aligned cell and read-bound export | 6 | 34 |
| Pinned OpenZeppelin Compact wrapper | 6 | 34 |

Both generated interfaces take zero user inputs and return a UInt128. The
read returned 0 after initialization and 10 after registration and a mint of
10. The supply cells use one 16-byte FAB atom. The runtime checks verified
each read preserves its full state frame. Both ZKIR relations expose one
BLS12-381 scalar output. [Matched observations and executable hashes](oz-total-supply-comparison.json)

The one-line Noctium source variant uses `alignedBytes` and the existing
`--ledger-read-bound` export. The historical table above measures the
original field-aligned port. The two contracts place supply in different
state slots and take different mint arguments. Compact presents a bigint
and minimal little-endian atom bytes. The native ABI presents a decimal
string and the observation pads the atom to 16 bytes. The rejection checks
cover an extra Compact read argument and a native mint amount of 2^128.

The same ZKIR 3.2.1 revision sized both relations. These are in-process
conformance and keyless synthesis measurements for this one read.
[Compact pin](https://github.com/LFDT-Minokawa/compact/releases/tag/compactc-v0.36.1) ·
[ZKIR source](https://github.com/midnightntwrk/midnight-zkir/tree/7a51b3385bbf4bce3604df87a7c70867c9ab43c0)

## Matched totalSupply reproduction

Use the pinned OpenZeppelin checkout and Compact 0.36.1 reference from the
reproduction notes. Set `COMPACTC_0361` to the compiler executable,
`COMPACT_RUNTIME_0210` to the Compact Runtime 0.21.0 package directory,
`OZ_SOURCE` to the OpenZeppelin checkout at
`f85f1a23685c6bbedfc8c2589ae3aa128aff7c46`, and `ZKIR_321` to the
selected ZKIR 3.2.1 sizing executable.

```sh
set -eu
scratch=$(mktemp -d)
trap 'rm -rf -- "$scratch"' EXIT
LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true lake build noctium
sed 's/^  cell totalSupply : UInt 128$/  cell totalSupply : UInt 128 alignedBytes/' \
  examples/openzeppelin/ConfidentialToken.lean > "$scratch/ConfidentialToken.lean"
.lake/build/bin/noctium compile "$scratch/ConfidentialToken.lean" \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --emit witness \
  --ledger-read-bound OpenZeppelinPort.ConfidentialToken.totalSupply \
  --output "$scratch/native"

NOCTIUM_TOTAL_SUPPLY_ARTIFACTS="$scratch/native" \
NOCTIUM_TOTAL_SUPPLY_RESULT="$scratch/native.json" \
  cargo +1.100.0 test --manifest-path runtime/Cargo.toml --locked \
    --no-default-features --features zkir-321 --test confidential_token \
    confidential_token_total_supply_native_observation -- --exact --ignored
node tests/compact/confidential-token-total-supply.mjs \
  "$COMPACTC_0361" "$COMPACT_RUNTIME_0210" "$OZ_SOURCE" "$scratch/compact" \
  > "$scratch/compact.json"

# Compare the read ABI and observed cases before sizing.
python3 - "$scratch/native.json" "$scratch/compact.json" <<'PYTHON'
import json
from pathlib import Path
import sys
native, compact = [json.loads(Path(name).read_bytes()) for name in sys.argv[1:]]
assert (native["abi"], native["cases"]) == (compact["abi"], compact["cases"])
state = compact["compact"]["stateMapping"]
atoms = [state[key] for key in ["cellEncodingAtZero", "cellEncodingAtTen"]]
assert [atom["value"][0]["$bytes"] for atom in atoms] == native["native"]["ledgerValueAtomHex"]
PYTHON

"$ZKIR_321" mock-compile "$scratch/native/OpenZeppelinPort.ConfidentialToken.totalSupply.zkir"
"$ZKIR_321" mock-compile "$scratch/compact/zkir/totalSupply.zkir"
```

## Paired sweep state observations

Both generated interfaces accepted a no-argument sweep and returned the
same Bytes32 caller. The test registered two synthetic accounts and minted
pending credits of 12 and 7. Both sides checked the ElGamal ciphertext sum
and identity reset. The amounts below describe this seeded fixture.
[Observations and artifact hashes](oz-sweep-comparison.json)

| Observed amount | Before | After |
| --- | ---: | ---: |
| Alice spendable | 0 | 12 |
| Alice pending | 12 | 0 |
| Bob spendable | 0 | 0 |
| Bob pending | 7 | 7 |
| Total supply | 19 | 19 |

Bob's checked ciphertexts and memo history stayed unchanged. Both sides
rejected the same unregistered caller and preserved the input state. The
Noctium run also replaced Alice's pending candidate with the old identity
ciphertext and rejected it at the native check.

The actual state paths are Noctium's `balances[accountId]` and
`pending[accountId]` and Compact's `Token__balances[accountId]` and
`Token__pending[accountId]`. The Noctium host witness takes the account ID
and eight old ciphertext coordinates and binds them to ledger reads. The
Compact circuit derives the ID and reads both ledger paths directly. Both
ZKIR headers have two scalar outputs and no declared inputs. Their
instruction streams bind inputs differently. This evidence qualifies the
tested state transition and leaves paired K and rows unreported.
[Native port](../../examples/openzeppelin/ConfidentialToken.lean) ·
[Pinned token module](https://github.com/OpenZeppelin/compact-contracts/blob/f85f1a23685c6bbedfc8c2589ae3aa128aff7c46/contracts/src/token/ConfidentialFungibleToken.compact)

## Paired sweep reproduction

Use the same pinned Compact compiler, runtime and OpenZeppelin checkout as
the totalSupply comparison. The native replay uses the stock Noctium port
and the selected Ledger 9.1.0.1 / ZKIR 3.2.1 profile.

```sh
set -eu
scratch=$(mktemp -d)
trap 'rm -rf -- "$scratch"' EXIT
lake build Noctium.Compiler Noctium.Frontend Noctium.Cli
lake env lean --run NoctiumMain.lean compile examples/openzeppelin/ConfidentialToken.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --emit witness --dedup-range-checks --output "$scratch/native"
NOCTIUM_SWEEP_ARTIFACTS="$scratch/native" NOCTIUM_SWEEP_RESULT="$scratch/native.json" \
  cargo +1.100.0 test --manifest-path runtime/Cargo.toml --locked \
    --no-default-features --features zkir-321 --test confidential_token \
    confidential_token_sweep_native_observation -- --exact --ignored
node tests/compact/confidential-token-sweep.mjs \
  "$COMPACTC_0361" "$COMPACT_RUNTIME_0210" "$OZ_SOURCE" "$scratch/compact" \
  > "$scratch/compact.json"
python3 - "$scratch/native.json" "$scratch/compact.json" <<'PYTHON'
import json
from pathlib import Path
import sys
native, compact = [json.loads(Path(name).read_bytes()) for name in sys.argv[1:]]
for field in ["before", "after", "returnedCaller", "siblingUnchanged"]:
    assert native["observation"][field] == compact["observation"][field]
PYTHON
```

## Paired transfer state observations

The in-process replay starts after two synthetic registrations, pending
mints of 12 for Alice and 7 for Bob, and Alice's sweep. Alice transfers 5
to Bob. Both sides return Alice's Bytes32 account ID and settle the
recipient credit in pending state. Bob's memo count grows from one to two,
and the newest memo decrypts to 5. An independent attempt to send 13
from the original snapshot fails on both sides and preserves that snapshot.
[Observations and artifact hashes](oz-transfer-comparison.json)

| Observed amount | Before | After |
| --- | ---: | ---: |
| Alice spendable | 12 | 7 |
| Alice pending | 0 | 0 |
| Bob spendable | 0 | 0 |
| Bob pending | 7 | 12 |
| Total supply | 19 | 19 |

Compact takes a `Bytes<32>` recipient and a `Uint<128>` amount as
circuit arguments, with three scalar lanes in the ZKIR input header.
Noctium has an empty call-input header. Its witness control declares a
public recipient and a private 128-bit amount, along with public
candidates for the caller, recipient key, prior ciphertext coordinates
and credit epoch. The native plan binds the state candidates to ledger
reads. Compact reads the corresponding state in the circuit. The
return and tested logical changes match. The different input and state
bindings leave this case unqualified for paired K and row measurements.

## Paired transfer reproduction

Use the same Compact compiler, runtime and OpenZeppelin inputs as the sweep.

```sh
set -eu
mkdir -p build/experiments
scratch=$(mktemp -d "$PWD/build/experiments/token-transfer.XXXXXX")
trap 'rm -rf -- "$scratch"' EXIT
lake build Noctium.Compiler Noctium.Frontend Noctium.Cli
lake env lean --run NoctiumMain.lean compile examples/openzeppelin/ConfidentialToken.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --emit witness --dedup-range-checks --output "$scratch/native"
NOCTIUM_TRANSFER_ARTIFACTS="$scratch/native" NOCTIUM_TRANSFER_RESULT="$scratch/native.json" \
  cargo +1.100.0 test --manifest-path runtime/Cargo.toml --locked \
    --no-default-features --features zkir-321 --test confidential_token \
    confidential_token_transfer_native_observation -- --exact --ignored
node tests/compact/confidential-token-sweep.mjs \
  "$COMPACTC_0361" "$COMPACT_RUNTIME_0210" "$OZ_SOURCE" "$scratch/compact" transfer \
  > "$scratch/compact.json"
python3 - "$scratch/native.json" "$scratch/compact.json" <<'PYTHON'
import json
from pathlib import Path
import sys
native, compact = [json.loads(Path(name).read_bytes()) for name in sys.argv[1:]]
for field in ["before", "after", "returnedCaller"]:
    assert native["observation"][field] == compact["observation"][field], field
native_memo, compact_memo = [result["observation"]["memo"] for result in [native, compact]]
assert native_memo["bobCountBefore"] == compact_memo["bobMemoCountBefore"]
assert native_memo["bobCountAfter"] == compact_memo["bobMemoCountAfter"]
assert native_memo["transferredAmount"] == compact_memo["newestMemoDecryptsTo"]
for result in [native, compact]:
    assert result["rejection"]["rejected"] is True
    assert result["rejection"]["stateUnchanged"] is True
PYTHON
```

## Reproduction and limits

```sh
.lake/build/bin/noctium compile examples/openzeppelin/ConfidentialToken.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --emit witness --dedup-range-checks --output FRESH_DIRECTORY

compactc --skip-zk \
  contracts/test/integration/_mocks/ComposedConfidentialFungibleTokenPublicSupply.compact \
  FRESH_DIRECTORY

zkir mock-compile ENTRYPOINT.zkir
```

Use fresh output directories and serial timed runs. The Compact compiler ran externally from temporary storage and is not a Noctium build/runtime dependency. The [official release](https://github.com/midnightntwrk/compact/releases/tag/compactc-v0.36.1) archive SHA-256 was verified before execution. Machine-readable runs, hashes and counts are retained in [oz-compile-performance.json](oz-compile-performance.json).

The first historical Noctium timing sample overlapped one small sizing process; the subsequent two source runs and all Compact runs ran without concurrent benchmark synthesis. RSS was recorded for the last two Noctium runs and all Compact runs. Background system activity was not controlled. No key-generation/proving-time conclusion follows from these source timings or from matching K. Broad compiler optimization remains under [issue 74](https://github.com/awjreynolds/noctium/issues/74).
