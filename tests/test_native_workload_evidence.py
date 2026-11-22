"""Focused offline mutations for retained native workload evidence."""

from copy import deepcopy
import json
from pathlib import Path
import runpy
import unittest


ROOT = Path(__file__).resolve().parents[1]
CHECK = runpy.run_path(str(ROOT / "scripts/proofs/check-native-workload-evidence.py"))


def inputs():
    matrix = json.loads(CHECK["MATRIX_PATH"].read_bytes())
    _history_bytes, history = CHECK["pinned_json"](
        CHECK["HISTORY_PATH"], CHECK["HISTORY_SHA256"], "historical_qualification_record")
    _profile_bytes, profile = CHECK["pinned_json"](
        CHECK["PROFILE_PATH"], CHECK["PROFILE_SHA256"], "target_profile")
    return matrix, history, profile


class NativeWorkloadEvidenceTests(unittest.TestCase):
    def test_pinned_inventory_and_historical_fixtures(self):
        report = CHECK["build_report"]()
        self.assertEqual(report["status"], "passed")
        self.assertEqual(report["inventory"]["sourceEntityRows"], 62)
        self.assertEqual(report["inventory"]["globalSourceOnlyNotes"], ["E-UPSTREAM-TEST-DEFINITIONS"])
        self.assertEqual(report["inventory"]["workloadEvidence"]["checker"],
                         {"instructionVariants": 15, "valueTypeVariants": 3})
        self.assertEqual(report["inventory"]["copyObservation"]["copyOpcodeCount"], 36)
        self.assertEqual(report["historicalFixtures"]["boolean"]["positiveCases"], 4)
        self.assertEqual(report["historicalFixtures"]["boolean"]["negativeCases"], 6)
        self.assertFalse(report["historicalFixtures"]["boolean"]["proof"])
        self.assertFalse(report["historicalFixtures"]["jubjub"]["ledger"])
        self.assertIn("does not qualify current source", report["scope"])

    def test_stale_summary_count_is_rejected(self):
        matrix, _, _ = inputs()
        matrix["counts"]["workloadEvidence"]["checker"]["instructionVariants"] = 14
        with self.assertRaisesRegex(ValueError, "matrix_workload_counts_stale"):
            CHECK["validate_matrix"](matrix, ROOT)

    def test_orphan_and_duplicate_matrix_evidence_links_are_rejected(self):
        matrix, _, _ = inputs()
        copy = next(row for row in matrix["entries"] if row["id"] == "ZKIR-OP-COPY")
        copy["evidence"]["ids"] = ["E-NOT-REGISTERED"]
        with self.assertRaisesRegex(ValueError, "orphan_matrix_evidence_link"):
            CHECK["validate_citations"](matrix, ROOT)

        matrix, _, _ = inputs()
        copy = next(row for row in matrix["entries"] if row["id"] == "ZKIR-OP-COPY")
        copy["evidence"]["ids"].append("E-NOCTIUM321-COPY")
        with self.assertRaisesRegex(ValueError, "duplicate_matrix_evidence_link"):
            CHECK["validate_citations"](matrix, ROOT)

    def test_unresolved_registry_citation_is_rejected(self):
        matrix, _, _ = inputs()
        matrix["evidenceRegister"]["E-NOCTIUM321-COPY"]["refs"].append("../../missing-copy-evidence.txt")
        with self.assertRaisesRegex(ValueError, "evidence_citation_unresolved"):
            CHECK["validate_citations"](matrix, ROOT)

    def test_copy_observation_count_and_scope_are_checked(self):
        matrix, _, _ = inputs()
        matrix["evidenceRegister"]["E-NOCTIUM321-COPY"]["checkerObservation"]["copyOpcodeCount"] = 35
        with self.assertRaisesRegex(ValueError, "copy_checker_observation_count_mismatch"):
            CHECK["validate_copy_evidence"](matrix, ROOT)

        matrix, _, _ = inputs()
        matrix["evidenceRegister"]["E-NOCTIUM321-COPY"]["ledger"] = True
        with self.assertRaisesRegex(ValueError, "evidence_stage_mismatch: E-NOCTIUM321-COPY.ledger"):
            CHECK["validate_citations"](matrix, ROOT)

    def test_changed_historical_boolean_fixture_is_rejected(self):
        matrix, history, _ = inputs()
        changed = CHECK["evidence_file"](
            ROOT, CHECK["BOOLEAN_ZKIR"], CHECK["BOOLEAN_ZKIR_SHA256"], "boolean_zkir") + b" "
        with self.assertRaisesRegex(ValueError, "boolean_zkir_digest_mismatch"):
            CHECK["validate_historical_fixtures"](
                matrix, history, ROOT, {CHECK["BOOLEAN_ZKIR"]: changed})

        matrix, history, _ = inputs()
        changed = CHECK["evidence_file"](
            ROOT, CHECK["JUBJUB_ZKIR"], CHECK["JUBJUB_ZKIR_SHA256"], "jubjub_zkir") + b" "
        with self.assertRaisesRegex(ValueError, "jubjub_zkir_digest_mismatch"):
            CHECK["validate_historical_fixtures"](
                matrix, history, ROOT, {CHECK["JUBJUB_ZKIR"]: changed})

    def test_fixture_opcode_and_case_counts_are_rechecked(self):
        matrix, history, _ = inputs()
        matrix["evidenceRegister"]["E-RAW321-BOOL"]["opcodes"].remove("less_than")
        with self.assertRaisesRegex(ValueError, "boolean_fixture_opcode_coverage_mismatch"):
            CHECK["validate_historical_fixtures"](matrix, history, ROOT)

        matrix, history, _ = inputs()
        cases = json.loads((ROOT / "tests/zkir321/boolean-cases.json").read_bytes())
        cases.pop()
        changed = json.dumps(cases, separators=(",", ":")).encode()
        with self.assertRaisesRegex(ValueError, "boolean_cases_digest_mismatch"):
            CHECK["validate_historical_fixtures"](
                matrix, history, ROOT, {CHECK["BOOLEAN_CASES"]: changed})

    def test_full_qualification_promotion_is_rejected(self):
        _, history, _ = inputs()
        promoted = deepcopy(history)
        promoted["currentSourceQualified"] = True
        with self.assertRaisesRegex(ValueError, "historical_evidence_scope_promoted"):
            CHECK["validate_historical_scope"](promoted)

        matrix, _, _ = inputs()
        copy = next(row for row in matrix["entries"] if row["id"] == "ZKIR-OP-COPY")
        copy["evidence"]["completeOverloadQualification"] = True
        with self.assertRaisesRegex(ValueError, "unsupported_complete_qualification: ZKIR-OP-COPY"):
            CHECK["validate_citations"](matrix, ROOT)

    def test_profile_mismatch_is_rejected(self):
        matrix, history, profile = inputs()
        profile["nativeSource"]["revision"] = "0" * 40
        with self.assertRaisesRegex(ValueError, "pinned_profile_identity_mismatch"):
            CHECK["validate_profile"](profile, matrix, history)


if __name__ == "__main__":
    unittest.main()
