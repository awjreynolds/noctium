# PrivateClaim reachability regression

`tests/PrivateClaimReachability.lean` defines an unregistered mutant of the
actual `PrivateClaim.claim` policy. The mutant changes only `enabled`, setting
it to `False`.

The test proves two separate facts. The universal progress implication holds
vacuously because no invocation is enabled. The full `FunctionalObligation`
fails because its nonvacuity field still requires an initial, preconditioned,
enabled invocation. A false `enabled` predicate cannot supply one.

The baseline policy remains unchanged. The test extracts its admitted abstract
fixture from the existing functional proof, runs the actual source claim, and
checks that replay fails with `state map key already present`. The fixture
uses the source proof's explicit hash trace and does not establish a real
target hash implementation.

The mutant has no source-proof registration. The existing source audit path
continues to check only the registered baseline policy.

The local replay exported `disabled_policy_not_functional` and
`baseline_admitted_claim_and_replay` with `leanexport` and re-checked both with
`leanchecker --from-export`. The export loaded the freshly built test module
from the first directory on `LEAN_PATH`.
