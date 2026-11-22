import importlib.util
import hashlib
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch


SCRIPT = Path(__file__).resolve().parents[1] / "scripts/proofs/benchmark-source-report.py"
SPEC = importlib.util.spec_from_file_location("source_proof_performance", SCRIPT)
BENCHMARK = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BENCHMARK)


class SourceProofPerformanceTests(unittest.TestCase):
    def test_report_requires_exact_private_claim_roles_and_replay_identity(self):
        report = {
            "operation": "PrivateClaim.claim",
            "status": "source-functional-and-scoped-privacy-checked",
            "sourceFunctionalChecked": True,
            "sourcePrivacyChecked": True,
            "compiledContractVerified": False,
            "policy": "Noctium.PrivateClaimVerification.policy",
            "functionalProof": "Noctium.PrivateClaimVerification.functional",
            "privacyProof": "Noctium.PrivateClaimVerification.privacy",
            "selectedOperations": ["PrivateClaim.claim"],
        }
        BENCHMARK.validate_report(report)
        report["privacyProof"] = "Noctium.PrivateClaimVerification.functional"
        with self.assertRaisesRegex(ValueError, "pinned PrivateClaim.claim"):
            BENCHMARK.validate_report(report)

    def test_command_failure_does_not_return_success_output(self):
        with patch.object(BENCHMARK.subprocess, "run", return_value=subprocess.CompletedProcess(
                args=["checker"], returncode=1, stdout=b"", stderr=b"PrivateClaim.claim: failed")):
            with self.assertRaisesRegex(RuntimeError, "PrivateClaim.claim: failed"):
                BENCHMARK.run_bytes(["checker"])

    def test_exports_must_match_checked_pin_and_report_proof_digest(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            model = b"reviewed model"
            proofs = b"functional and privacy proof data"
            pin = hashlib.sha256(model).hexdigest()
            (output / "trusted-model.ndjson").write_bytes(model)
            (output / "proofs.ndjson").write_bytes(proofs)
            (output / "trusted-model.sha256").write_text(pin + "\n")
            report = {"trustedModelSha256": pin, "proofExportSha256": hashlib.sha256(proofs).hexdigest()}
            with patch.object(BENCHMARK, "MODEL_PIN", output / "checked-in-pin"):
                (output / "checked-in-pin").write_text(pin + "\n")
                BENCHMARK.validate_export_identities(report, output)
                report["proofExportSha256"] = "0" * 64
                with self.assertRaisesRegex(ValueError, "proof digest"):
                    BENCHMARK.validate_export_identities(report, output)
                (output / "trusted-model.sha256").write_text("f" * 64)
                with self.assertRaisesRegex(ValueError, "checked-in model pin"):
                    BENCHMARK.validate_export_identities(report, output)


if __name__ == "__main__":
    unittest.main()
