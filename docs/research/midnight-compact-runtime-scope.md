# Lean compiler target scope for Midnight

Research checked on 2026-11-16 against official Midnight documentation and repositories.

## Recommendation

Compact is one available source and artifact path, not the definition of Noctium's language or feature set. Derive supported circuit operations from the selected Midnight ledger and proving interfaces, then validate a complete artifact and deployment route separately.

The compatibility matrix checked on 2026-11-16 listed ledger 9 with Compact toolchain 0.36.0, language 0.28.0, Compact runtime 0.21.0, on-chain runtime 4.0.0, and proof server 9.0.0. Compact toolchain 0.36.0 generates ZKIR version 3, specifically ZKIR 3.1. Its bundled `zkir-v3` binary comes from `midnight-zkir` 3.2.0-rc.2. The [updated baseline](compact-equivalence-baseline.md) records the 2026-11-17 client patch. These profiles describe documented integration paths, not Noctium's source-language boundary. [Current compatibility matrix](https://docs.midnight.network/relnotes/support-matrix) [Compact toolchain 0.36.0 release notes](https://docs.midnight.network/relnotes/compact/toolchain-0.36.0)

## Evidence

- Midnight describes Compact as its smart-contract language. Its compiler outputs zero-knowledge circuits used to prove correct interactions with the ledger. The public compatibility matrix ties Compact compiler, language, runtime, on-chain runtime, and proof server versions to each network. [Compact overview](https://docs.midnight.network/compact) [Compatibility matrix](https://docs.midnight.network/relnotes/support-matrix)
- Ledger 9 documentation lists contract-to-contract calls, event emission, and new cryptographic primitives as capabilities usable by Compact contracts, and specifies the Compact toolchain version required for those features. [Ledger 9 upgrade](https://docs.midnight.network/relnotes/ledger-9) [Ledger 9.1.0.1 release notes](https://docs.midnight.network/relnotes/ledger/ledger-9-1-0-1)
- Compact toolchain 0.36.0 generates only ZKIR v3. The release notes warn that recompiling a contract changes verifier keys, and that matching Compact runtime versions are required for cross-contract modules. This makes artifact compatibility part of the compiler target, not just a choice of available VM operations. [Compact toolchain 0.36.0 release notes](https://docs.midnight.network/relnotes/compact/toolchain-0.36.0)
- Midnight.js documents Impact VM as the on-chain runtime and lists `onchain-runtime-v4` for ledger 9 and `onchain-runtime-v3` for the retained era. The same architecture describes both the ledger and Compact runtime as depending on Impact VM. [Midnight.js architecture](https://github.com/midnightntwrk/midnight-js#architecture)

## Terminology

The official term is “ZKIR version 3,” not “zkR3.” Compact toolchain 0.36.0 generates ZKIR 3.1, while its bundled `zkir-v3` binary comes from `midnight-zkir` 3.2.0-rc.2. “Impact VM” or “on-chain runtime” is a separate layer. Ledger 9 uses package line v4. [Compact toolchain 0.36.0 release notes](https://docs.midnight.network/relnotes/compact/toolchain-0.36.0) [Ledger 9 upgrade notes](https://docs.midnight.network/relnotes/ledger-9) [Midnight.js architecture](https://github.com/midnightntwrk/midnight-js#architecture)

## Scope implication

V1's feature boundary follows the ledger 9 contract, circuit, and proving interfaces Noctium chooses to support. Compact 0.28 is one documented route through those interfaces. A capability available lower in the ledger or proving stack still needs a complete, tested source-to-deployment path before Noctium promises it. This recommendation separates feature scope from backend integration evidence.
