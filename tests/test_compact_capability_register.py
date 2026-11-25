"""CLI mutation checks for the Compact capability register."""

from copy import deepcopy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
MATRIX = ROOT / "docs/compatibility/compact-feature-matrix.json"
CHECKER = ROOT / "scripts/check-compact-capability-register.py"


class CompactCapabilityRegisterTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.original = json.loads(MATRIX.read_text())

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.matrix_path = Path(self.temp.name) / "matrix.json"

    def write_matrix(self, matrix):
        self.matrix_path.write_text(json.dumps(matrix, sort_keys=True))

    def run_checker(self, matrix_path=None):
        command = [sys.executable, str(CHECKER)]
        if matrix_path is not None:
            command.extend(["--matrix", str(matrix_path)])
        return subprocess.run(command, cwd=ROOT, capture_output=True, text=True, check=False)

    def test_default_matrix_passes(self):
        result = self.run_checker()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_changed_compact_version_pin_is_rejected(self):
        matrix = deepcopy(self.original)
        matrix["baseline"]["featureToolchain"] = "0.36.2"
        self.write_matrix(matrix)

        result = self.run_checker(self.matrix_path)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("baseline pin mismatch: featureToolchain", result.stdout + result.stderr)

    def test_duplicate_case_id_is_rejected(self):
        matrix = deepcopy(self.original)
        case_id = matrix["features"][0]["id"]
        matrix["features"].append(deepcopy(matrix["features"][0]))
        self.write_matrix(matrix)

        result = self.run_checker(self.matrix_path)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(f"duplicate case ID: {case_id}", result.stdout + result.stderr)

    def test_missing_observed_evidence_file_is_rejected(self):
        matrix = deepcopy(self.original)
        case = next(row for row in matrix["features"] if row["observedEvidence"])
        reference = "tests/compact/__missing_compact_capability_register_evidence__.compact"
        self.assertFalse((ROOT / reference).exists())
        case["observedEvidence"][0] = reference
        self.write_matrix(matrix)

        result = self.run_checker(self.matrix_path)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(f"missing evidence file for {case['id']}: {reference}",
                      result.stdout + result.stderr)


    def list_head_case(self, matrix, case_id):
        row = next(row for row in matrix["features"] if row["id"] == "C-ADT-LIST-HEAD")
        return next(case for case in row["conformanceCases"] if case["id"] == case_id)

    def test_missing_required_case_evidence_is_rejected(self):
        matrix = deepcopy(self.original)
        case = self.list_head_case(matrix, "LIST-HEAD-UINT8-EMPTY")
        del case["evidenceByKind"]["ZK"]
        self.write_matrix(matrix)

        result = self.run_checker(self.matrix_path)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(
            f"missing case evidence for {case['id']}: ZK",
            result.stdout + result.stderr,
        )

    def test_upstream_compiler_assertion_cannot_be_promoted(self):
        matrix = deepcopy(self.original)
        case = self.list_head_case(matrix, "LIST-HEAD-SECP256K1-SCALAR")
        case["status"] = "executed-pinned-compact-and-noctium"
        self.write_matrix(matrix)

        result = self.run_checker(self.matrix_path)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(
            f"case status contradicts oracle outcome for {case['id']}",
            result.stdout + result.stderr,
        )


    def test_open_oracle_case_blocks_promoting_its_feature_row(self):
        matrix = deepcopy(self.original)
        row = next(row for row in matrix["features"] if row["id"] == "C-ADT-LIST-HEAD")
        row["noctiumStatus"] = "equivalent"
        row["equivalence"] = "verified"
        self.write_matrix(matrix)

        result = self.run_checker(self.matrix_path)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(
            "upstream-open case under verified row: LIST-HEAD-SECP256K1-SCALAR",
            result.stdout + result.stderr,
        )


if __name__ == "__main__":
    unittest.main()
