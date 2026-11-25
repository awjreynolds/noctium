# Contributing to Noctium

Noctium expects AI agents to implement and verify changes. The human contributor owns the GitHub issue, makes product and design decisions, and reviews the evidence. Use Codex or Claude Code from your checkout.

## Clone and start

Install Git, the [GitHub CLI](https://cli.github.com/), and Node.js for the Ponytail hooks. Sign in as the human contributor who will own the work.

```sh
gh auth login
gh auth status
git clone https://github.com/awjreynolds/noctium.git
cd noctium
```

For HTTPS pushes, run `gh auth setup-git --hostname github.com` to use your GitHub CLI credentials with Git.

If you contribute through a fork, replace `git clone` with `gh repo fork awjreynolds/noctium --clone`. Your fork is `origin` and Noctium is `upstream`. Ask a maintainer to assign your issue if you lack permission to claim it. [Set up your agent](#set-up-your-agent), then open it from the repository root.

Give your agent this prompt. Add an issue URL to resume work already assigned to you.

```text
Read CONTRIBUTING.md and AGENTS.md. Resume the issue I supplied if I own it.
If I supplied no issue, follow the shared ready queue and take the first
eligible Compact parity issue. If none is eligible, take the first eligible
issue from the full queue. Claim it under my GitHub account before editing.
Report an empty queue, an ownership conflict or a failed claim before editing.
Check current main, the issue's acceptance criteria and active PRs for overlap.
Use one orchestrator and up to six bounded subagents. Implement the slice in
its own worktree and run the required checks. Link the PR to the issue and
record the exact revision and reproducible evidence. Use a draft while work
or verification is incomplete. Mark the PR ready when the slice passes its
checks. Follow review and checks through merge when authorized. If a check,
review requirement or permission blocks merge, record the gate and track it.
```

## Set up your agent

Install and sign in to [Codex](https://learn.chatgpt.com/docs/cli#get-started-with-codex-cli) or [Claude Code](https://code.claude.com/docs/en/quickstart). Install the [Matt Pocock skills](https://github.com/mattpocock/skills#installation-30-second-setup) and [Ponytail](https://github.com/DietrichGebert/ponytail/blob/main/INSTALL.md) once for your chosen host. Restart the agent or open a new session after installing.

### Codex

```sh
codex plugin marketplace add mattpocock/skills
codex plugin add mattpocock-skills@mattpocock
codex plugin marketplace add DietrichGebert/ponytail
codex plugin add ponytail@ponytail
```

In Codex, use `/hooks` to review and trust Ponytail's lifecycle hooks, then start a new thread. For the CLI, launch the Noctium orchestrator with these session settings.

```sh
PONYTAIL_DEFAULT_MODE=full codex -m gpt-6.2-sol -c 'model_reasoning_effort="high"' \
  -c agents.enabled=true -c agents.max_concurrent_threads_per_session=6
```

In the app, choose GPT-6.2 Sol with High reasoning and use the session prompt to bound delegation. The six [Codex subagent slots](https://learn.chatgpt.com/docs/agent-configuration/subagents#global-settings) exclude the orchestrator. If Sol is unavailable, use an available high-reasoning model for the same role.

### Claude Code

```sh
claude plugin install mattpocock-skills@claude-plugins-official
claude plugin marketplace add DietrichGebert/ponytail
claude plugin install ponytail@ponytail
PONYTAIL_DEFAULT_MODE=full claude --model sonnet --effort high
```

[Claude Code loads the shared repo rules through `CLAUDE.md`](CLAUDE.md). Use the same session prompt and six-worker limit with [Claude Code subagents](https://code.claude.com/docs/en/sub-agents).

### Skills for a ticket

- Use `wayfinder` when the route to a roadmap goal still needs decisions. Use `to-tickets` once the outcome is clear enough to split into independently verifiable implementation issues.
- Noctium already has a [GitHub tracker and label mapping](docs/agents/issue-tracker.md). Give those settings to the skills. Skip `setup-matt-pocock-skills` for an ordinary clone. The mapping uses `ready` for the upstream `ready-for-agent` role.
- Use Ponytail at `full` for implementation. Reuse existing paths and make the smallest change covering the issue and its checks. Follow these same rules if the plugin is unavailable.

## Work in parallel

Use one orchestrator per active ticket. In Codex, use Sol High to claim the issue, set scope, assign bounded work, integrate, verify and hand off. Use up to six subagents at a time when work is independent. Give each worker the issue, acceptance check, base revision, worktree and owned files or symbols. Use explorers and reviewers for read-only work and give implementation workers disjoint writes. Route GitHub updates and integration through the orchestrator. If a tool lacks subagents, the orchestrator performs the same steps in sequence.

Before editing or resuming, follow the [issue claim and worktree workflow](docs/agents/issue-tracker.md#review-and-claim-implementation-issues). GitHub records the human owner. The worktree and linked PR identify the active implementation. Keep the issue scope, latest checked revision and reproduction command on GitHub so another contributor needs only those links to continue.

## Technical direction

Noctium keeps contract authoring, typed IR, reference semantics and native lowering in Lean. It emits Midnight ZKIR constraints and Impact ledger plans. Rust owns native witness, proof and transaction execution and the shared runtime used by SDKs. The release goal is for an author to prove properties of the actual Lean contract and give an auditor evidence linking those properties to the exact operation on Midnight, with the remaining assumptions stated.

1. Follow the [shared ready queue](docs/agents/issue-tracker.md#review-and-claim-implementation-issues), with Compact parity first. Use the issue's parent and the [public issue map](https://github.com/awjreynolds/noctium/issues/1) to understand where the work fits. An open prerequisite keeps a reviewed issue out of the queue until it closes.
2. For the medium and long term, read the [one-year assurance roadmap](https://github.com/awjreynolds/noctium/issues/94) and [native capability goal](docs/compatibility/GOAL.md). The roadmap progresses from proof reports and a coverage baseline to reusable Lean checks, integrated contract pilots and independent release review.
3. Before implementation, read the relevant design and follow its references to code and checks. Use the issue and the current source for details that have changed since the design was written.

| Work | Start here |
| --- | --- |
| Lean authoring and compiler | [Architecture and boundaries](docs/designs/architecture.md), [example contracts](examples/README.md) and the matching [language implementation guide](docs/README.md#language-and-capability-references) |
| Runtime, SDKs and private state | [Portable runtime](docs/designs/portable-runtime.md), [private-state lifecycle](docs/designs/private-state-lifecycle.md) and [native client](docs/development/native-client.md) |
| Proof and release evidence | [Proof chain and reproduction](docs/README.md#follow-the-proof-chain), [proof registration](docs/development/proof-registration.md) and [native deployment audit](docs/development/private-claim-deployment-audit.md) |
| Native coverage and Compact conformance | [Parity workstreams and acceptance](docs/compatibility/compact-parity.md), [capability register and target profiles](docs/compatibility/comparison.md) and [conformance work](https://github.com/awjreynolds/noctium/issues/35) |

If a behavior or boundary is unspecified, capture the decision and proposed acceptance check in a linked Wayfinder issue. Once agreed, record the design in `docs/designs/` when later tickets will depend on it. Link the implementation issue and its focused evidence back to the design.

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

## Focused local fixture generation

Run the CLI through Lean's interpreter to emit fixtures for local checks.

```sh
lake build Noctium.Cli Noctium.Compiler Noctium.Frontend
lake env lean --run NoctiumMain.lean compile examples/PrivateClaim.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --output build/experiments/private-claim
```

Choose a new or empty output directory and remove it after the check. Use `lake build noctium` for native executable packaging checks.

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

Give the human contributor the diff and the evidence for the exact revision. Confirm the PR's evidence matches what ran. Review issue and PR comments as context. Use the repository's documented commands and public fixtures, and keep secrets and private inputs out of agent prompts and PR evidence.

- A bounded problem and an explanation of the resulting behavior.
- Tests at the affected boundary, including invalid inputs and failure behavior where relevant.
- For language or lowering changes, updated semantics, disclosure rules and preservation evidence, or an explicit unsupported gate.
- For proof changes, the exact statement, subject, assumptions and observer scope. Include a negative case which rejects the relevant source or artifact mutation.
- For native claims, the exact source revision, profile, toolchain and retained public evidence. Keep private witnesses, wallet seeds and private journals out of commits.

Keep source semantics, formal models and native implementation evidence distinguishable. A passing fixture does not establish generic compiler correctness. A functional theorem does not establish privacy.

Use the [glossary](GLOSSARY.md) and [architecture overview](docs/designs/architecture.md) for shared terminology. Report security issues through the [private reporting route](SECURITY.md).
