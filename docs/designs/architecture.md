# Architecture and assurance

Noctium combines contract authoring, specifications and correctness proofs in Lean 4, then compiles to Midnight's native formats. The compiler, typed IR, reference semantics and primary lowering also use Lean. A finite DSL defines executable contracts. Ordinary Lean theorems and tactics prove their specified properties.

Lean proofs and runtime ZK proofs have different jobs. The former establish properties of contract behavior. The latter establish satisfaction of a circuit and its bound statement for an invocation. Compilation preservation and artifact certificates connect source properties to native artifacts for the qualified private claim.

![Noctium source, compiler, artifacts and native execution, with published claim-specific evidence and open assurance links.](../assets/noctium-pitch.png)

## Four boundaries

**Source.** A circuit relates public inputs, private witnesses and outputs. A contract separately declares state cells, maps, reads, guards and writes around an entrypoint. The [private claim](../../examples/PrivateClaim.lean) uses a two-level Merkle path and records a nullifier to reject reuse. The workload exercises the architecture without defining its permanent scope.

**Lean compiler.** Elaboration produces typed circuit and contract IR. Validation checks the supported target profile. The [scalar disclosure pass](../development/disclosure.md) tracks private origins at public sinks. A [proved pruning pass](../development/assurance.md#kernel-checked-compiler-transformation) removes true constraints without changing reference behavior. Native lowering emits relations and plans, and the [producer gate](../development/native-producer-safety.md) rejects unsupported or invalid scalar descriptors.

**Native artifacts.** ZKIR v3 relations describe proof constraints. Impact plans describe ledger operations, state layout and ordered reads. [Bundle verification](../development/portable-artifacts.md) checks the artifacts, selected profile and keys against an authenticated manifest. The [PrivateClaim deployment audit](../development/private-claim-deployment-audit.md#evidence-and-assumptions) links the [reviewed source and exact artifact bytes](../development/private-claim-artifact-certificates.md) to independently regenerated keys, initialized state and a finalized localnet claim. The public audit covers the recorded deployment, source authority at `925164d0` and qualification implementation at `c48fc4b7`. Its assumptions include the native parser, VM, proving system and cryptography, pinned toolchain and host capabilities, SRS provenance, and a trusted node for canonical history and finality.

**Native application.** The Rust runtime executes plans through explicit host capabilities. The assembler constructs native intents. The proof API verifies the frozen statement before attaching a proof, and the [client](../development/native-client.md) funds, seals, submits and validates finalized results. Private journals support recovery and versioned compare-and-exchange. Chain acceptance and private-store commit are distinct outcomes. The [C runtime ABI](../development/native-runtime-abi.md) exposes execution and providers. The following checks cover the recorded SDK builds and isolated development networks, using ZKIR 3.2.1 unless specified.

| Host | Retained execution |
| --- | --- |
| Linked C++ client through the C ABI | Proved, deployed and called the retained claim contract on ZKIR 3.2.0 and 3.2.1. Recovered in a separate process after a lost acknowledgement by resubmitting identical sealed bytes. The host staged the private write. [C ABI qualification](../development/native-client-abi.md#qualification) |
| Swift on Apple Silicon macOS and arm64 iOS 27.0 simulator | Ran typed witnesses and verified a K7 proof. Finalized the typed-witness deployment and call, recovered the journal with a fresh client, and ran the K9 one-time claim with native replay rejection. The iOS 16 device slice linked. Physical-device execution remains open. [Swift qualification](../development/swift-witness-sdk.md#qualification) |
| Kotlin on arm64 AOSP Android 35 emulator | Ran the packaged witness and K7 proof, finalized the typed-witness deployment and call, and recovered the sealed bytes through a fresh client. Finalized the K9 one-time claim with native replay rejection. Physical-device execution remains open. [Android qualification](../development/android-witness-sdk.md#qualification) |
| TypeScript and WASM in a Chrome 157.0.8103.79 Web Worker | Verified a K7 proof, finalized the typed-witness deployment and call on Ledger 9.1.0.1 / ZKIR 3.2.1 localnet, and recovered the submitted attempt after worker restart using IndexedDB and a separate loopback Rust provider. [Browser proof](../development/web-witness-sdk.md#reproduce-the-browser-test) · [Localnet receipt](../development/web-localnet-receipt.json) |

The application path needs no Node or Compact runtime. Independent Midnight libraries and the pinned native ZKIR toolchain supply proving and ledger interfaces. Optional JavaScript tools remain for development orchestration and selected conformance checks.

## Assurance boundaries

Retained exact-byte and deployment receipts qualify their recorded historical commits.
The canonical namespace migration does not requalify the renamed source or native ABI.
See the [namespace and evidence boundary](../development/namespaces.md).

The published contract-to-artifact guarantees apply to the actual private-claim program. Its proofs connect imported source definitions to independent native relation and state models, then to retained artifact bytes. Soundness quantifies over arbitrary satisfying assignments and checked VM traces. The proof does not assume an honest witness generator.

| Layer | Established today | Remaining boundary |
| --- | --- | --- |
| [Source properties](../development/private-claim-proofs.md) | Eligibility equations, exact updates, invariants, framing, replay rejection and scoped source privacy | Correctness of the intended business specification and stated hash assumptions |
| [Proof audit](../development/proof-registration.md) | Typed obligation matching, pinned model comparison, fresh-kernel replay and transitive axiom checks | Business-specification review and authenticity of external authority pins |
| [Native relation](../development/private-claim-lowering-proofs.md) and [state](../development/private-claim-native-state-proofs.md) | Claim-specific soundness, completeness, state/transcript preservation and JSON-tree certificates | Native implementation agreement and real admission limits |
| [Native privacy](../development/private-claim-native-privacy-proofs.md) | Equal declared public observations for successful runs with coupled host context | Proof-byte zero knowledge, failure channels, timing, logs and provider observations |
| [Exact artifacts](../development/private-claim-artifact-certificates.md) | Independent immutable builds and kernel checks bind the claim proofs to exact retained bytes | Trusted bootstrap and authenticated authority inputs |
| [Deployed claim identity](../development/private-claim-deployment-audit.md) | Exact source authority, independently regenerated native keys, initial state and finalized operation matched by a public-only audit | Native cryptography, SRS provenance, host pins and trusted-node history/finality |
| [Scalar lowerer](../research/generic-scalar-preservation.md) | Generic soundness and source completeness for accepted scalar lowering, exact typed inputs/observations and independently pinned kernel audit | Frontend, raw-byte implementation agreement, other native primitives and general ledger preservation |
| [Native integration](../development/native-client.md#retained-qualification) | Real proofs, finalized localnet execution, state comparison and recovery tests | General feature coverage, public-network qualification and independent security review |

Fresh-kernel audits admit only the pinned foundational axioms `propext`, `Classical.choice` and `Quot.sound`. User axioms, admitted proofs and native-computation axioms reject. The checker enforces this policy over transitive dependencies and matches exact theorem statements.

The kernel checks the modeled propositions. Native parser, hash, VM, proof-system and host implementations retain explicit agreement assumptions. The scoped privacy theorem does not prove cryptographic secrecy of proof bytes or hide success versus failure. Functional correctness supplies no automatic confidentiality guarantee.

The selected claim now has a [qualified source/key/deployment identity join](../development/private-claim-deployment-audit.md). [Generic scalar lowering](../research/generic-scalar-preservation.md) now has independently audited soundness and source completeness. Frontend, other native primitives and general ledger effects need their own preservation evidence. Historical source-audit flags retain their original scope, including `compiledContractVerified: false`. The deployment audit adds its separate `PrivateClaimDeploymentIdentity/v1` guarantee without granting universal compiler or unconditional business-specification verification.

## Scope and growth

The current source slice includes `Native`, `Bool`, bounded unsigned scalars, [typed helpers](../development/named-helpers.md) and [lazy host control](../development/structured-control.md). Host control does not enable guarded native circuit or ledger execution. Composite layouts and codecs have checked foundations. [Component-aware source helper outputs](../development/component-disclosure.md) now preserve origins through checked flattening to native scalar leaves. General aggregate ledger effects and native private-state operations remain separate.

The [capability goal](../compatibility/GOAL.md) follows the full native ZKIR v3 and ledger interfaces. Compact supplies comparison cases and compiler engineering lessons, with no compiler or runtime dependency. [Capability inventories](../compatibility/zkir-feature-matrix.json) track the target surface separately from implemented and qualified source features.

For implementation order and active work, use the [public issue map](https://github.com/awjreynolds/noctium/issues/1). For reproducible checks, start at the [documentation index](../README.md).
