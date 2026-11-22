"""Synthetic mutation checks for the Foundation opcode join, not pilot evidence."""

import hashlib
import json
from copy import deepcopy
import runpy
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
JOIN = runpy.run_path(str(ROOT / "scripts/proofs/check-foundation-opcode-matrix.py"))


def write_json(path: Path, value: object) -> bytes:
    contents = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    path.write_bytes(contents)
    return contents


def operation_report(operation: str, zkir_bytes: bytes) -> dict:
    return {
        "schemaVersion": 1,
        "operation": operation,
        "files": [
            {"role": "manifest", "path": "noctium.json", "bytes": 10,
             "sha256": "1" * 64},
            {"role": "zkir", "path": JOIN["OPERATION_FILES"][operation],
             "bytes": len(zkir_bytes), "sha256": hashlib.sha256(zkir_bytes).hexdigest()},
            {"role": "impact", "path": operation + ".impact.json", "bytes": 10,
             "sha256": "2" * 64},
        ],
    }


class FoundationOpcodeMatrixTests(unittest.TestCase):
    """Only synthetic inputs are used here. No generated result is retained."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        profile = json.loads(JOIN["PROFILE_PATH"].read_bytes())
        target = JOIN["target_identity"](profile)
        self.artifacts = {}
        rows = []
        for operation, opcodes in [
            ("PrivateClaim.claim", ["assert", "impact", "assert"]),
            ("BoundedScalars.apply", ["add", "less_than"]),
        ]:
            directory = self.root / operation.replace(".", "-")
            directory.mkdir()
            zkir = {
                "version": {"major": 3, "minor": 2},
                "inputs": [],
                "outputs": [],
                "instructions": [{"op": opcode} for opcode in opcodes],
            }
            contents = write_json(directory / JOIN["OPERATION_FILES"][operation], zkir)
            self.artifacts[operation] = directory
            rows.append({"operation": operation, "operationArtifacts": operation_report(operation, contents)})
        self.foundation = {
            "schemaVersion": 1,
            "profile": JOIN["PROFILE_NAME"],
            "status": "source-evidence-checked",
            "targetProfile": target,
            "scope": {"operations": list(JOIN["OPERATIONS"]), "constructors": "not covered"},
            "openRequirements": [
                {"operation": operation, "profile": JOIN["PROFILE_NAME"],
                 "requirement": requirement, "status": "open", "requiredEvidence": "still open"}
                for operation in JOIN["OPERATIONS"]
                for requirement in JOIN["OPEN_REQUIREMENTS"]
            ],
            "operations": rows,
        }
        self.foundation_bytes = json.dumps(self.foundation, sort_keys=True, separators=(",", ":")).encode()

    def tearDown(self):
        self.temp.cleanup()

    def join(self):
        return JOIN["build_evidence"](self.foundation_bytes, self.artifacts)

    def test_histogram_is_deterministic_and_labels_prior_stages(self):
        result = self.join()
        self.assertEqual(result["status"], "joined")
        self.assertEqual(result["scope"]["constructors"], "not covered")
        self.assertEqual([operation["operation"] for operation in result["operations"]],
                         ["PrivateClaim.claim", "BoundedScalars.apply"])
        claim = result["operations"][0]
        self.assertEqual(claim["rawZkir"]["instructionCount"], 3)
        self.assertEqual([(row["opcode"], row["count"]) for row in claim["opcodeHistogram"]],
                         [("assert", 2), ("impact", 1)])
        matrix_row = claim["opcodeHistogram"][0]
        self.assertEqual(matrix_row["matrixRowId"], "ZKIR-OP-ASSERT")
        self.assertEqual(matrix_row["stageEvidenceScope"], "historical matrix workload observations only")
        self.assertIn("do not claim keygen, checker, proof, or ledger execution", result["interpretation"])
        self.assertEqual(json.dumps(result, sort_keys=True), json.dumps(self.join(), sort_keys=True))

    def test_crossed_artifact_directories_are_rejected(self):
        crossed = {
            "PrivateClaim.claim": self.artifacts["BoundedScalars.apply"],
            "BoundedScalars.apply": self.artifacts["PrivateClaim.claim"],
        }
        with self.assertRaisesRegex(ValueError, "foundation_zkir_missing: PrivateClaim.claim"):
            JOIN["build_evidence"](self.foundation_bytes, crossed)

    def test_changed_raw_zkir_bytes_are_rejected(self):
        path = self.artifacts["PrivateClaim.claim"] / JOIN["OPERATION_FILES"]["PrivateClaim.claim"]
        path.write_bytes(path.read_bytes() + b" ")
        with self.assertRaisesRegex(ValueError, "foundation_zkir_digest_mismatch: PrivateClaim.claim"):
            self.join()

    def test_report_target_must_match_the_pinned_profile(self):
        report = deepcopy(self.foundation)
        report["targetProfile"]["zkir"] = "3.2.2"
        contents = json.dumps(report, sort_keys=True, separators=(",", ":")).encode()
        with self.assertRaisesRegex(ValueError, "foundation_target_profile_pin_mismatch"):
            JOIN["build_evidence"](contents, self.artifacts)

    def test_unknown_zkir_opcode_is_rejected(self):
        operation = "PrivateClaim.claim"
        directory = self.artifacts[operation]
        zkir_path = directory / JOIN["OPERATION_FILES"][operation]
        zkir = json.loads(zkir_path.read_bytes())
        zkir["instructions"][0]["op"] = "unmapped_opcode"
        contents = write_json(zkir_path, zkir)
        report = deepcopy(self.foundation)
        row = next(item for item in report["operations"] if item["operation"] == operation)
        row["operationArtifacts"] = operation_report(operation, contents)
        self.foundation_bytes = json.dumps(report, sort_keys=True, separators=(",", ":")).encode()
        with self.assertRaisesRegex(ValueError, "unknown_matrix_opcode: unmapped_opcode"):
            self.join()

    def test_duplicate_opcode_mapping_is_rejected(self):
        matrix = json.loads(JOIN["MATRIX_PATH"].read_bytes())
        impact = next(row for row in matrix["entries"] if row.get("id") == "ZKIR-OP-IMPACT")
        impact["jsonOpcode"] = "add"
        with self.assertRaisesRegex(ValueError, "duplicate_matrix_json_opcode: add"):
            JOIN["matrix_opcode_rows"](matrix)

    def test_required_open_gap_cannot_be_dropped(self):
        report = deepcopy(self.foundation)
        report["openRequirements"] = [
            item for item in report["openRequirements"]
            if not (item["operation"] == "PrivateClaim.claim" and item["requirement"] == "native-soundness")
        ]
        contents = json.dumps(report, sort_keys=True, separators=(",", ":")).encode()
        with self.assertRaisesRegex(ValueError, "foundation_open_requirements_incomplete: PrivateClaim.claim"):
            JOIN["build_evidence"](contents, self.artifacts)


if __name__ == "__main__":
    unittest.main()
