# Issue tracker: GitHub

The canonical issue tracker is GitHub Issues in `awjreynolds/noctium`.

The public map is [issue #1](https://github.com/awjreynolds/noctium/issues/1). Attach new work to its relevant roadmap issue or work package as a native GitHub sub-issue. Use issue dependencies for prerequisites. The [assurance roadmap](https://github.com/awjreynolds/noctium/issues/94) holds release gates and work packages.

## Wayfinding operations

- The map is a GitHub issue labelled `wayfinder:map`.
- Give each decision ticket one Wayfinder label. Use `wayfinder:research` for investigation, `wayfinder:prototype` for an experiment, `wayfinder:grilling` for a decision with a human, or `wayfinder:task` for a prerequisite to a decision.
- Use GitHub's native sub-issue and issue dependency relationships. Keep the map's Decisions so far section updated when a ticket closes.
- With `gh`, target `awjreynolds/noctium` for issue, label, and relationship operations, including from a fork.

## Review and claim implementation issues

1. Fetch the canonical `main` (`origin/main` for a direct clone, `upstream/main` for a fork). Read the issue, parent, blockers, recent comments and linked or overlapping open PRs. Update the scope with links to any acceptance evidence already on `main`.
2. Give each issue one demonstrable outcome. For compiler work, pick one source behavior and carry it through the affected lowering, runtime and verification boundaries. For SDK work, pick one host and one complete flow. State the success check, the relevant rejection or recovery check, and the environment or fixture needed to run them.
3. Keep broad work as a parent and link its implementation slices as sub-issues. Add `ready` to a reviewed slice with a bounded outcome, reproducible acceptance checks and explicit prerequisites. Link open implementation prerequisites as `Blocked by` dependencies. Both queue views filter them out until all such issues close. Leave work waiting on an external prerequisite out of `ready` until the prerequisite is available. Matt Pocock's `ready-for-agent` role maps to `ready`. Apply `compact-parity` to slices comparing Compact behavior or evidence.
4. Resume the supplied issue if your contributor owns it. With no issue supplied, take the first eligible result in the [Compact parity view](https://github.com/awjreynolds/noctium/issues?q=is%3Aopen+is%3Aissue+label%3Aready+label%3Acompact-parity+no%3Aassignee+-is%3Ablocked), then use the [full ready queue](https://github.com/awjreynolds/noctium/issues?q=is%3Aopen+is%3Aissue+label%3Aready+no%3Aassignee+-is%3Ablocked) if the first view is empty. Recheck that the issue is open, ready, unassigned and unblocked, then claim it under your contributor's account. Refresh to confirm the sole assignee. If a competing claim appeared, remove only your own assignment and move to the next eligible result. If your account already has active work on the issue, resume it or coordinate before starting another session. Report an empty queue, an ownership conflict on a supplied issue, or a failed claim before editing.
5. Start a branch and worktree named for the issue from the checked base, or reuse the existing branch when resuming. Record the branch and planned write scope on the issue or linked draft PR. If two issues need the same code path or evidence, agree on the write boundary or sequence them with a dependency. Keep the assignment through review and unassign yourself if you return the work to the queue.

List Compact parity first from either a direct clone or a fork. If this returns no issues, repeat the query without `label:compact-parity`.

```sh
gh issue list -R awjreynolds/noctium --state open \
  --search 'label:ready label:compact-parity no:assignee -is:blocked'
```

## Parallel worktree handoff

Record the issue, worktree path, branch, base revision and owned files before
dispatch. Keep the exact pending check and its expected result alongside
completed results. Put local process handles and scratch paths in an ignored
handoff note under the main checkout's `.lake/` directory. Link the note when
delegating locally. For a contributor handoff, leave the branch, head revision,
checks and remaining work on the issue or linked PR. Change the assignee after
the next contributor accepts the handoff.

On recovery and before marking a PR ready, fetch canonical `main` again and
check the issue, current diff and any live process. Incorporate relevant upstream
changes on your own branch. Reuse a passing check while its tested inputs remain
unchanged. If upstream work satisfies the issue or changes its scope, reconcile
the ticket with the linked evidence before more edits.

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

For changes in shared lowering or elaboration, run the existing fixture for
the closest affected caller as well as the new fixture. Use the
[interpreted fixture path](../../CONTRIBUTING.md#focused-local-fixture-generation)
when the check needs compiler outputs and has no native executable dependency.
When placing a compiler ticket in the ready queue, note the source variants
that share its implementation. For example, check sealed and unsealed state
in one constructor slice when both use the same path. Keep separate slices
when the variants need different lowering or ledger behavior.

## Pull requests

Use issues for triage. Use a draft PR while implementation or verification
is incomplete. Record the remaining work on the draft. Mark a PR ready
once its issue acceptance checks pass on the recorded head revision.

The contributor and their agent follow the PR through review, applicable
checks and merge. Merge when the contributor has authorized the change and
GitHub permits the merge. Record any remaining review, check or permission
gate on the PR and track it to resolution. If someone else takes over, name
the owner and pending work in the handoff.

Use `Closes #123` in the PR description when the change fulfills the issue, so GitHub closes it on merge into `main`. For partial work, link the issue and leave it open. This keeps downstream work blocked until the prerequisite lands.

Keep parallel implementation in separate worktrees. Sequence merges that touch
the same compiler path or change the same evidence. Reuse the recorded check
at integration when the diff and its relevant inputs still match. Combine
dependent proof steps in one PR when they share a ticket and only their
composed result satisfies its next checkpoint.

Let a running compiler CI check on `main` finish. GitHub keeps one pending run
for the newer changes while agents continue working. Check the failure on the
revision that ran and prioritize a shared regression over merging more changes
through the affected compiler path.
