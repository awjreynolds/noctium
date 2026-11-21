import copy
import importlib.util
from pathlib import Path
import unittest


CHECKER = Path(__file__).resolve().parents[1] / "scripts/proofs/check-private-claim-audit.py"
SPEC = importlib.util.spec_from_file_location("private_claim_audit", CHECKER)
AUDIT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(AUDIT)


def role(name):
    return {"role": name, "status": "covered", "duplicateRegistrationCount": 0,
            "registrations": [{"policy": "Fixture.policy", "proof": f"Fixture.{name}"}]}


def row(name, index):
    return {"entrypoint": name, "index": index, "status": "covered", "policyPairing": "matched",
            "roles": [role("functional"), role("privacy")]}


def report(rows):
    return {"schemaVersion": 1, "kind": "source-proof-coverage", "contract": "PrivateClaim",
            "status": "covered", "sourceProofsRechecked": True, "entrypoints": rows}


class PrivateClaimOperationCoverageTests(unittest.TestCase):
    def setUp(self):
        self.metadata = {"contracts": [{"name": "PrivateClaim", "entrypoints": [
            {"name": "claim"}, {"name": "verify"}]}]}
        self.operations = AUDIT.expected_source_operations(self.metadata)
        self.coverage = [report([row("claim", 0), row("verify", 1)])]

    def test_accepts_both_compiler_selected_operations(self):
        self.assertEqual(AUDIT.validate_source_coverage(self.operations, self.coverage),
                         ["PrivateClaim.claim", "PrivateClaim.verify"])

    def test_rejects_missing_or_extra_entrypoints(self):
        with self.assertRaisesRegex(ValueError, r"missing=\['verify'\]"):
            AUDIT.validate_source_coverage(self.operations, [report([row("claim", 0)])])
        with self.assertRaisesRegex(ValueError, r"extra=\['other'\]"):
            AUDIT.validate_source_coverage(self.operations, [report([row("claim", 0), row("other", 1)])])

    def test_rejects_duplicate_entrypoint_rows(self):
        rows = [row("claim", 0), row("verify", 1), row("verify", 1)]
        with self.assertRaisesRegex(ValueError, "duplicate_source_proof_entrypoint"):
            AUDIT.validate_source_coverage(self.operations, [report(rows)])

    def test_rejects_missing_and_duplicate_roles(self):
        missing = copy.deepcopy(self.coverage)
        missing[0]["entrypoints"][1]["roles"].pop()
        with self.assertRaisesRegex(ValueError, "missing_source_proof_role: PrivateClaim.verify.privacy"):
            AUDIT.validate_source_coverage(self.operations, missing)
        duplicate = copy.deepcopy(self.coverage)
        duplicate[0]["entrypoints"][1]["roles"][1]["duplicateRegistrationCount"] = 1
        with self.assertRaisesRegex(ValueError, "source_proof_role_not_unique_and_covered"):
            AUDIT.validate_source_coverage(self.operations, duplicate)

    def test_rejects_duplicate_compiler_operations(self):
        duplicate = copy.deepcopy(self.metadata)
        duplicate["contracts"][0]["entrypoints"][1]["name"] = "claim"
        with self.assertRaisesRegex(ValueError, "duplicate_compiler_entrypoint"):
            AUDIT.expected_source_operations(duplicate)


if __name__ == "__main__":
    unittest.main()
