# Compact parity delivery

For each supported Compact capability, show equivalent observable behavior in Noctium. Compare typed inputs and results, admitted and rejected executions, and the state, events, calls and failures visible at the applicable boundary. The [Compact register](compact-feature-matrix.json) owns case IDs, source references, required evidence, observed evidence and status. The [four-week plan](https://github.com/awjreynolds/noctium/issues/1365) owns the current implementation slices. Use the [contributor workflow](../../CONTRIBUTING.md) to find and claim available work.

Use Compact 0.36.1, language 0.28.0, source revision `7fa3a117c5e7efe9d2c51da04263e5f0b3509144` and Compact Runtime 0.21.0 where the oracle needs the runtime. Use the selected Noctium Ledger 9.1.0.1 and ZKIR 3.2.1 profile. Record each tool and artifact identity. Compact is an external comparison tool for fixtures. Lean and Rust remain the Noctium implementation.

## Workstreams

Assign each row to one package by matching the selectors below from top to bottom. Counts describe the register at `c4bf8ec4`. Of 220 Compact reference rows, 70 already have verified scope and 150 still need work. Retain the verified cases as regressions. The register also contains one Noctium extension.

| Register selector | Rows | Work to complete | Tracking |
| --- | ---: | --- | --- |
| `C-LANG-*` | 24 | Complete scalar ranges and conversions, nominal identity, records, tuples and vectors, then typed helpers, generics, modules and bounded control. Check selected and skipped effects, scope and bounds. | [Native capability #25](https://github.com/awjreynolds/noctium/issues/25), [reference semantics #96](https://github.com/awjreynolds/noctium/issues/96) |
| `C-PRIVATE-*` | 4 | Compare witness inputs, outputs, callback order and allowed disclosure. Specify what each host observes and when staged state commits, rolls back or recovers. Exercise selected and inactive paths, including private guards controlling public effects. | [Privacy and host lifecycle #98](https://github.com/awjreynolds/noctium/issues/98), [SDK qualification #99](https://github.com/awjreynolds/noctium/issues/99) |
| `host-ledger-view` layer | 12 | Compare snapshot Map, Set and List contents plus ordinary and historic Merkle observations. Check typed paths, absence, order where specified, pagination and malformed snapshots. Use the same public snapshot and plan identities across advertised hosts. | [SDK qualification #99](https://github.com/awjreynolds/noctium/issues/99) |
| `C-STATE-*` and ledger Cell, Counter, Set, Map and List rows | 35 | Complete constructors, sealed fields and admitted collection shapes. Check empty and missing cases, parent and leaf identity, typed defaults, guard behavior, same-key order and preservation of adjacent state. | [Native capability #25](https://github.com/awjreynolds/noctium/issues/25), [reference semantics #96](https://github.com/awjreynolds/noctium/issues/96) |
| Ledger MerkleTree and HistoricMerkleTree rows, and `C-STDLIB-MERKLETREE*` | 22 | Check typed leaf encoding, append and sparse indexed writes, roots and paths, capacity, history and reset. Retain evidence for each tree family and distinguish host queries from state-changing operations. | [Conformance #35](https://github.com/awjreynolds/noctium/issues/35), [reference semantics #96](https://github.com/awjreynolds/noctium/issues/96) |
| `C-CONTRACT-*`, `C-ADT-KERNEL-*`, `C-STDLIB-KERNEL` and `C-STDLIB-BLOCKTIME*` | 24 | Specify interface identity, Kernel context, ordered contract and asset claims, and typed communication commitments. Compare caller, target, arguments and resulting effects, including inactive claims and failure of a composed operation. | [Native capability #25](https://github.com/awjreynolds/noctium/issues/25), [composition #105](https://github.com/awjreynolds/noctium/issues/105) |
| `C-EVENT-EMIT` and the remaining standard-library rows in `language-ledger` | 12 | Verify each event schema and guarded occurrence, order and finalized payload. Keep source event support, finalized event observation and external indexer behavior distinct. | [Conformance #35](https://github.com/awjreynolds/noctium/issues/35), [SDK qualification #99](https://github.com/awjreynolds/noctium/issues/99) |
| Standard-library Maybe, Either, some, none, left, right, serialize and deserialize | 8 | Check nested tags, inactive defaults, nominal identity, exact value layouts and malformed values at the circuit, storage and ABI boundaries. | [Conformance #35](https://github.com/awjreynolds/noctium/issues/35) |
| Standard-library Jubjub, constructJubjub, Secp, Curve, EC and Ed25519 families, plus neg, inv and hashToCurve | 36 | Exercise each declared curve and role overload. Check canonical encodings, identities and admitted group operations with pinned vectors. Cover rejected or exceptional inputs, partial operations and selected guard behavior. | [Native capability #25](https://github.com/awjreynolds/noctium/issues/25), [conformance #35](https://github.com/awjreynolds/noctium/issues/35) |
| Standard-library transientHash, transientCommit, persistentHash, persistentCommit, degradeToTransient, upgradeFromTransient, keccak256 and sha512 | 8 | Match digests and commitments for each admitted type and domain. Check preimage framing, empty and nonempty values, type and length bounds, and native binding. | [Conformance #35](https://github.com/awjreynolds/noctium/issues/35), [native certificates #97](https://github.com/awjreynolds/noctium/issues/97) |
| Remaining `standard-library` rows | 28 | Check typed address, coin, token and recipient forms, and shielded and unshielded operations. Qualify booking and commitment semantics, boundary values, state conservation and guarded failure under each supported profile. | [Native capability #25](https://github.com/awjreynolds/noctium/issues/25), [SDK qualification #99](https://github.com/awjreynolds/noctium/issues/99) |
| `C-ARTIFACT-HOST` and `C-SDK-INTEGRATION` | 2 | Verify the portable value and witness ABI across each advertised host, then wallet approval, proof, funding, submission, finality and supported chain observation. Include wrong-profile and malformed cases. | [SDK qualification #99](https://github.com/awjreynolds/noctium/issues/99) |
| `C-ARTIFACT-ZKIR`, `C-ARTIFACT-MANIFEST`, `C-ARTIFACT-LEDGER`, `C-DIAGNOSTIC` and `C-SDK-MAINTENANCE` | 5 | Check profile and artifact identity, public bindings, exact state and transcript outcomes, stale and mismatched artifacts, and supported authority or verifier maintenance. Compare rejection at the relevant boundary and retain stable diagnostics where a consumer relies on them. | [Proof profiles #95](https://github.com/awjreynolds/noctium/issues/95), [native certificates #97](https://github.com/awjreynolds/noctium/issues/97), [releases #101](https://github.com/awjreynolds/noctium/issues/101) |
| `C-NATIVE-POSEIDON` | 1 | Qualify the domain-tagged primitive against its native specification. | [Native capability #25](https://github.com/awjreynolds/noctium/issues/25), [native inventory](zkir-feature-matrix.json) |

## Turn a gap into an implementation issue

1. Audit the pinned grammar, compiler type rules, standard-library overloads, ledger ADTs and generated interfaces against the register. Link discoveries to an existing case or give uncovered behavior a stable case ID under [conformance #35](https://github.com/awjreynolds/noctium/issues/35). Read the row's pinned source and current evidence. Choose one operation, overload and observable boundary. Name the Compact oracle and one existing Noctium fixture or entry point.
2. Describe the accepted result, relevant rejection or inactive case, exact state and observation scope, and how both checks run. Use synthetic values. Reuse Lean fixtures, Compact fixtures under `tests/compact/`, and the affected native or SDK tests.
3. Expose genuine blockers as GitHub dependencies. Land the required typed representation or fixture before its consumers. Sequence shared code paths, and keep independent hosts and fixtures available in parallel. Record a pinned upstream failure and its retest trigger when an external capability blocks the slice.
4. Attach the exact rows, commands, tool and artifact identities and scoped result to the PR. Update only the affected inventory evidence. A ticket covers its stated layout, overloads, host and profile. The row's `requiredEvidence` determines when broader equivalence has been verified.

The first List.head case records cover two executed UInt8 heads and an open Secp256k1Scalar compiler assertion. [Capability register](compact-feature-matrix.json) · [List.head evidence ticket](https://github.com/awjreynolds/noctium/issues/1390)

Extend that case-to-row mapping by workstream. Each case records its admitted domain, oracle, expected observations, evidence by kind and disposition. Include widened bounds, zero-width side effects, unsupported source forms and excluded host or ledger observations where they apply. Link the new work package to #35 when the issue's native sub-issue limit prevents a direct child.

## Check the capability register

Run the Foundation comparison baseline's offline register check from the repository root with Python 3.

```sh
python3 scripts/check-compact-capability-register.py
python3 tests/test_compact_capability_register.py
```

The first command checks the pinned Compact and Noctium profile identities, case IDs, source keys and local evidence files. It reports Noctium status and equivalence together and counts the native extension separately. The second command checks rejection of a duplicate ID, a missing evidence file and a changed Compact version using temporary copies of the register. Compact is optional for these checks. The reported counts reflect the recorded evidence status, which individual conformance cases establish. [Validator ticket](https://github.com/awjreynolds/noctium/issues/1384) · [Target profile](../../profiles/midnight-ledger-9-zkir-3.2.1-target.json)

For the structured List.head records, the validator also checks pinned oracle
outcome, declared context and local evidence by kind. An executed case needs
its required evidence. A compiler-assertion case stays open. The focused tests
remove required evidence and attempt to promote the failed oracle outcome.
[Existing List.head fixtures and reproduction commands](../development/native-lists.md)

## Verify the retained List.head comparison

The record binds two root UInt8 List.head observations to the exact
Noctium source commit, Compact 0.36.1 and Runtime 0.21.0. The input digests
include the Foundation source profile and the selected Ledger 9.1.0.1 /
ZKIR 3.2.1 target. The retained outputs are the Compact runner's JSON and
the fresh Lean compiler head relation. Lean checks the two typed source
results. [Comparison record](../../tests/compact/list-head-comparison-v1/record.json) ·
[Foundation source profile](../../profiles/foundation-source-v1.json)

From a checkout with the recorded commit in its Git history, run:

```sh
python3 scripts/check-compact-capability-register.py
python3 scripts/check-compact-comparison-record.py
python3 tests/test_compact_comparison_record.py
```

The offline checker reads the input bytes from the pinned Git revision and
checks the retained output bytes against their digests. The focused tests
accept the retained record and reject a copy with a changed Lean fixture
digest. Compact is only needed to replay the oracle.

To replay, check out the record's `noctiumCommit` in an isolated worktree.
Set `COMPACTC_0361` and `COMPACT_RUNTIME_0210` to absolute paths to the pinned
compiler and runtime package. Run these commands from that worktree:

```sh
set -eu
scratch=$(mktemp -d)
trap 'rm -rf -- "$scratch"' EXIT
lake build noctium
lake env lean tests/NativeScalarListMaybe.lean
.lake/build/bin/noctium compile tests/NativeScalarListMaybe.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --output "$scratch/native"
node tests/compact/list-head-maybe.mjs "$COMPACTC_0361" "$COMPACT_RUNTIME_0210" \
  > "$scratch/compact.json"
shasum -a 256 "$scratch/compact.json" "$scratch/native/NativeScalarListMaybe.head.zkir"
```

Compare both SHA-256 values with the `outputs` entries in the record.
This run covers empty absence with zero and present 37 after a push to the
list. It records source checks, the Compact runtime observation and native
relation emission. [List fixture and native checker scope](../development/native-lists.md)

## Qualification order

1. **Meaning and ABI.** Check language and standard-library cases and record the positive and rejection expectations. Carry them into explicit ledger paths and cross-contract scenarios. Compare values, encodings and canonical order where the profile specifies them.
2. **Ledger and host.** Check compiled constraints and public input bindings, then exercise accepted and rejected operations on the pinned isolated ledger where required. Compare ordered state effects, events, calls, receipts, rollback and host failure behavior. Use the same public fixtures to qualify supported hosts.
3. **Reproducible comparisons.** Bind versions, source, emitted artifacts and evidence. Begin with the private claim and confidential-token `totalSupply`, `sweep` and `transfer`. Measure K and rows only after preconditions, effects, ABI and disclosure match. Report the sizing method and exclusions and any unresolved differences. Keep later optimization and proof timing tied to the matched baseline. [Token comparison #74](https://github.com/awjreynolds/noctium/issues/74) · [Optimizations #93](https://github.com/awjreynolds/noctium/issues/93)
4. **Release evidence.** Check the coverage rows and unresolved blockers against the release profile. Complete scoped Lean preservation and privacy proofs, deployed artifact identity and independent review where the release claims those guarantees. [Assurance roadmap #94](https://github.com/awjreynolds/noctium/issues/94)

## Comparison boundaries

- **Semantic parity.** Compare the agreed observable behavior. Retain each compiler's source syntax and artifacts. Check numeric bounds, the scope of serialization and interface forms against the pinned compiler when the reference prose and implementation differ. For host ordering, compare exactly when the reference specifies order. Otherwise compare members under a documented normalization.
- **Interoperability.** Qualify any interoperation the release advertises on isolated localnet. For calls across compilers, exercise both caller/callee directions and check selector, installed keys, typed argument and result commitments, failure, state and finality. Separate same-behavior fixtures from these mixed-compiler checks. [Composition #105](https://github.com/awjreynolds/noctium/issues/105)
- **Host interfaces.** Validate the supported generated or native APIs, wire formats and observation contracts. Qualify event consumption through the advertised boundary and explicitly identify reliance on an external indexer. Wallet UIs, indexer services and explorers have their own product scope.
- **Upstream limits.** [Six-parent booked Map comparison #797](https://github.com/awjreynolds/noctium/issues/797) waits on a usable pinned build for [Compact #734](https://github.com/LFDT-Minokawa/compact/issues/734). The [foreign scalar List head probe](../../tests/compact/foreign-scalar-list-maybe.mjs) and the [scalar serialization notes](../development/scalar-serialization.md) record separate compiler limitations. Record the exact control that worked, the failed case, the qualifying Noctium scope, and the retest trigger.
- **Admitted resources.** Keep known narrower limits visible, including Noctium's 1,024-byte bound for the scoped bytes cases and its weighted finite-range budget. Record the accepted intersection and the remaining work for broader parity.

Close a parity case when it has the required evidence for its declared profile or an agreed, evidence-backed disposition for an intentional difference. Keep blocked cases open in the register. Full native coverage includes additional obligations from the [native inventory](zkir-feature-matrix.json). Release assurance adds its own proof-to-deployment gates.
