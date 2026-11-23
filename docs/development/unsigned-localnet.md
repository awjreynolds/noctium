# Bounded unsigned source to accepted ledger state

The actual [BoundedScalars source](../../examples/BoundedScalars.lean) compiles in Lean to native ZKIR and a symbolic Impact plan. The native Rust assembler builds its deployment and call intents without Node. The isolated local ledger finalized deployment at height 1304 and the call at 1308 on 2026-11-16. The resulting cell stores the public result 510, and fetched state bytes exactly match the Rust prediction.

[Machine evidence](../../tests/scalars/localnet-evidence.json) records source, circuit, plan, key, parameter and tool hashes, exact finalized transaction receipts and the qualification boundary. This is one bounded scalar slice, not full unsigned-language or native capability equivalence.

## Pipeline and representation

`UInt 8` denotes values zero through 255. `UIntRange 511` denotes zero through 510. Arithmetic uses inclusive maxima, so adding two eight-bit operands infers maximum 510. The runtime schema normalizes the result to `UIntRange<511>`, with canonical decimal string values. The ledger stores the scalar in its native field encoding.

The source requires the initial cell to equal zero, proves that the two private inputs add to the public result, and writes that result. Lean emits range constraints for inputs, the arithmetic result and the ledger read. Subtraction rejects underflow. Narrowing casts add range checks. The [scalar design](../designs/scalar-types.md) and [runtime schema](native-unsigned-scalars.md) define the supported rules.

The independent native ZKIR 3.2.0 tool generated k8 keys for the 125-row entrypoint. The Rust assembler decoded the keys and parameters, created fresh deployment/intent/communication randomness, repartitioned the actual program and checked the official constructor-generated proof preimage. Eight guaranteed operations and no fallible operations enter the call.

The pinned native toolkit funds, proves and submits the serialized intents. The existing Node localnet harness orchestrates this development run and observes receipts. It does not evaluate the unsigned program or assemble its state/call. Rust applications use the native runtime and assembler directly. A native proof/submission SDK API and provider transaction lifecycle remain separate work.

## Accepted outcome

Contract: `ec4310960c77761a48f32638bfdaae5e9dd28f2ce9023e90f2fd6c1795c05a3c`.

| Operation | Finalized height | Ledger transaction |
| --- | --- | --- |
| Deployment | 1304 | `0x70238d343813888c4b6dab58811b63d383d681b0ceb1be5d9c302279b13a8d9c` |
| Call | 1308 | `0x68ae6a86d9ffb9727a27ead53d3b948972ecd4e2aec83e31acbed508973b6cee` |

Each receipt contains exactly one `TxApplied` and the expected contract event at the same extrinsic. Observed contract-state SHA-256 is `af3582afe2dfe37f8ffb362286cee7a1e0de035c481e63594b0fde25c609d9cf`, equal to the predicted bytes.

A wrong public sum and an out-of-range private input reject before submission. After acceptance, the native CLI decodes the fetched state and runs the plan plus official checker again. The initially-zero guard rejects reuse. No replay transaction was submitted. A second fetch confirms unchanged bytes.

## Offline source proof

Replay the registered proof roles for the actual `BoundedScalars.apply` entrypoint with the pinned Lean toolchain.

```sh
python3 scripts/proofs/check-private-claim-audit.py --report --operation BoundedScalars.apply
```

The functional proof checks that accepted calls add the two bounded private inputs, match the declared public total and update the cell to that total. The successful-only privacy proof compares source outputs and final state for calls with equal public inputs, starting state and evaluation context. The JSON report names the checked policy and theorems, model digest, axioms and target profile. The runtime receipts above record separate executions at their pinned revisions.

## Adversarial circuit checks

The [34 raw-witness cases](../../tests/scalars/constraint-cases.json) run against actual source-generated circuits with both official 3.2.0 and 3.2.1 checkers. They bypass the Noctium evaluator and ABI, so host input checks do not mask missing circuit constraints. Cases cover zero and 248-bit bounds, non-power-of-two ranges, addition/multiplication, wrong public statements, field-wrapped subtraction underflow, casts and malformed Boolean values.

Unused partial expressions retain their rejection behavior. Independent review found an underflow inside an unused Boolean wrapper disappearing from the relation. The fix conservatively retains nested subtraction and casts through Boolean, Native, hash and eager-selection wrappers. Each wrapper now has a positive and direct invalid-witness circuit case. A later optimizer must prove totality before removing such evaluation.

Lean also checks unsigned addition/multiplication no-wrap lemmas and proves that field-wrapped underflow exceeds every supported unsigned bound. These are scoped internal facts. Full lowering correctness remains an open assurance obligation.

Reproduce the source/checker cases after building Noctium and installing the pinned conformance libraries:

```sh
lake build
lake env lean tests/BoundedScalars.lean
bash tests/uint-cli.sh
.lake/build/bin/noctium compile tests/BoundedScalars.lean --output /tmp/noctium-scalar-cases
node scripts/zkir/check-scalar-cases.mjs /tmp/noctium-scalar-cases
```

Native assembly and its private output layout are documented in [native-assembler.md](native-assembler.md). For the existing isolated localnet harness, set `NOCTIUM_NATIVE_RUNTIME` to the built native runtime executable when passing Rust-assembled artifacts to `scripts/localnet/deploy-native.mjs`. The harness requires native preflight checks, exact receipt/state matching and native rejection against the fetched post-state.

The default profile remains unchanged. Nominal aliases, composites, general operators, lazy guarded branches, explicit disclosure analysis, multi-contract calls, assets, events and the remaining native types/instructions still require their own implementation and evidence.
