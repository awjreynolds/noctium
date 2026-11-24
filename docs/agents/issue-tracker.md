# Issue tracker: GitHub

The canonical issue tracker is GitHub Issues in `awjreynolds/noctium`.

The public map is [issue #1](https://github.com/awjreynolds/noctium/issues/1). Link every decision, research task, and implementation task as a native child issue. Link blockers with GitHub issue dependencies so a new implementation agent sees the actual execution order.

## Wayfinding operations

- The map is a GitHub issue labelled `wayfinder:map`.
- Each ticket is a child issue of the map and has one `wayfinder:<type>` label: `research`, `prototype`, `grilling`, or `task`.
- Use GitHub's native sub-issue and issue dependency relationships. Keep the map's Decisions so far section updated when a ticket closes.
- Use `gh` inside the repository for issue, label, and relationship operations.

## Review and claim implementation issues

1. Review the issue against `main` and check for active work. Update the scope with links to any evidence already on `main`.
2. Give each issue one demonstrable outcome. For compiler work, pick one source behavior and carry it through the affected lowering, runtime and verification boundaries. For SDK work, pick one host and one complete flow. State the success check, the relevant rejection or recovery check, and the environment or fixture needed to run them.
3. Keep broad work as a parent and link the deliverable slices as sub-issues. Use native GitHub dependencies for issues that must land first. Add `ready` once the slice has clear checks, its prerequisites are available, and no open issue blocks it. Remove `ready` if those conditions change.
4. Pick an issue from the [ready queue](https://github.com/awjreynolds/noctium/issues?q=is%3Aopen+is%3Aissue+label%3Aready+no%3Aassignee+-is%3Ablocked). Assign yourself in the issue sidebar before starting and refresh to confirm you are the sole assignee. If you use an agent, have it check the assignee and respect existing claims. Keep the assignment through review, link the PR to the issue, and unassign yourself if you hand the work back.

## Parallel worktree handoff

Record the issue, worktree path, branch, base revision and owned files before
dispatch. Keep the exact pending check and its expected result alongside
completed results. Put local process handles and scratch paths in an ignored
handoff note under the main checkout's `.lake/` directory. Link the note when
delegating. Keep scope and durable evidence on the issue and PR.

On recovery, read the handoff and verify the current diff and live process
before resuming. Reuse a passing check while its tested inputs remain unchanged.

Use the [shared Lean cache](../../CONTRIBUTING.md#reuse-lean-builds-across-worktrees)
and one local environment for pinned toolchain paths. Compile runtime tests in
the shared Cargo target. For a long proof or localnet run, build with
`cargo test --no-run --message-format=json` and launch the reported test
executable for that manifest and profile. Use a temporary target for a concrete
artifact mismatch and remove it after verification.

Run compilation and affected positive and rejection cases for a POC change.
Add proof, funded acceptance or an assurance audit when the ticket changes
that boundary or calls for new evidence. Acquire live parameters and prepare
key provenance while the build runs. Keep the exact finalized identifiers
with the sanitized receipt.

## Pull requests

Pull requests are not a request surface for triage.
