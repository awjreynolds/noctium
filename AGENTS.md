# Noctium POC workflow

- Start, resume or hand off a ticket using [CONTRIBUTING.md](CONTRIBUTING.md) and the [GitHub issue workflow](docs/agents/issue-tracker.md). Confirm ownership and overlap before editing. Link the issue in the pull request and close it when the acceptance criteria are met.
- Keep the compiler, typed IR and lowering in Lean. Rust hosts Midnight's native runtime and proving integration.
- Reuse `.lake/`, `runtime/target/` and `build/` for generated outputs. Agents share these caches and coordinate builds. Use a separate cache only when isolation is required, then remove it after use.
- Put experiments under `build/experiments/`. Clean owned experiment directories when the experiment ends. External temporary directories need cleanup on exit.
- Commit generated fixtures only when a current example or focused test consumes them. Remove superseded outputs and unfinished scaffolds before handing off.
- Preserve source, wallet credentials and current private state during artifact cleanup. Restrict deletion to identified generated outputs owned by this project.
- POC checks cover compilation, the changed execution boundary and essential rejection cases. Run broader checks for a concrete failure or an explicit qualification gate.
- Historical backwards compatibility is not a delivery requirement. Avoid legacy artifact retention and compatibility campaigns.
