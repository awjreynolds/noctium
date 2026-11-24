# Contributing to Noctium

Start with the [public issue map](https://github.com/awjreynolds/noctium/issues/1). GitHub Issues track decisions, research, implementation and dependencies. Open or join an issue before substantial work so the proposed scope and required evidence are clear.

Follow the [issue review and claim workflow](docs/agents/issue-tracker.md#review-and-claim-implementation-issues) when choosing or splitting work.

## Development checks

Follow the [POC workflow](AGENTS.md) for shared build directories, temporary-output cleanup and focused validation.

Install [elan](https://github.com/leanprover/elan#installation), Git and Python 3. The repository pins Lean 4.35.0. From the repository root:

```sh
python3 scripts/check-branding.py
lake build noctium Noctium.Compiler
lake env lean tests/StructuredCells.lean
```

Choose the source example or focused test affected by your change. Cover essential invalid inputs and failure behavior. Broad proof audits, native proving and localnet qualification use the separate workflows in the [documentation index](docs/README.md).

For Rust changes, install Rust 1.100.0 and a native C build toolchain, then run the runtime tests with the pinned dependencies:

```sh
cargo +1.100.0 test --manifest-path runtime/Cargo.toml --locked \
  --no-default-features --features zkir-321 --test structured_cells
```

The [native client guide](docs/development/native-client.md#retained-qualification) adds the optional `localnet` feature, exclusive 3.2.1 profile and real-chain prerequisites. Do not interpret an ordinary test pass as a new proof or ledger qualification.

## Reuse Lean builds across worktrees

Point each local worktree at the same absolute Lake cache directory. Keep the
cache under the main checkout's ignored `.lake/` directory.

```sh
export LAKE_CACHE_DIR=/absolute/path/to/noctium/.lake/artifact-cache
export LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true
lake build noctium Noctium:shared
```

The first build populates the cache. Lake matches artifacts to their build
inputs, so branches reuse the matching modules and rebuild changed ones and
their affected dependents. This command uses the local cache and restores the
compiler and shared library in each worktree.

On one arm64 macOS host with Lean 4.35.0, a cold build at `927da217` took
255.71 seconds. A fresh worktree restored the same targets in 0.49 seconds
and emitted byte-identical PrivateClaim metadata, Impact and ZKIR. Changing
the CLI version rebuilt the affected targets in 2.40 seconds and produced the
updated version string.

## What a useful change includes

- A bounded problem and an explanation of the resulting behavior.
- Tests at the affected boundary, including invalid inputs and failure behavior where relevant.
- For language or lowering changes, updated semantics, disclosure rules and preservation evidence, or an explicit unsupported gate.
- For proof changes, the exact statement, subject, assumptions and observer scope. Include a negative case which rejects the relevant source or artifact mutation.
- For native claims, the exact source revision, profile, toolchain and retained public evidence. Keep private witnesses, wallet seeds and private journals out of commits.

Keep source semantics, formal models and native implementation evidence distinguishable. A passing fixture does not establish generic compiler correctness. A functional theorem does not establish privacy.

Use the [glossary](GLOSSARY.md) and [architecture overview](docs/designs/architecture.md) for shared terminology. Report security issues through the [private reporting route](SECURITY.md).
