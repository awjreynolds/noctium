#!/usr/bin/env python3
"""Exercise trusted model pins, typed obligations and fresh export auditing."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[2]
MODEL_ROOTS = [
    "Noctium.Verification.FunctionalObligation",
    "Noctium.Verification.PrivacyObligation",
    "VerificationFixture.policy",
    "VerificationFixture.wrongContractPolicy", "VerificationFixture.wrongSpecPolicy",
    "VerificationFixture.releasingPolicy",
    "propext", "Classical.choice", "Quot.sound",
]


def run(args: list[str], env: dict[str, str] | None = None) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(args, cwd=ROOT, env=env, capture_output=True, text=True, timeout=180)
    if result.returncode:
        raise AssertionError(f"command failed: {args}\n{result.stdout}\n{result.stderr}")
    return result


def main() -> int:
    run(["lake", "build", "Noctium.Verification.ExportAudit"])
    source = (ROOT / "tests/Verification.lean").read_text()
    with tempfile.TemporaryDirectory(prefix="noctium-registration-test-") as directory:
        scratch = Path(directory)
        sources, objects = scratch / "source", scratch / "objects"
        (sources / "tests").mkdir(parents=True)
        (objects / "tests").mkdir(parents=True)
        candidate = sources / "tests/Verification.lean"
        environment = os.environ.copy()
        environment["LEAN_PATH"] = str(objects)

        def build(text: str) -> None:
            candidate.write_text(text)
            run(["lake", "env", "lean", "-D", "Elab.async=false", "--root", str(sources),
                 "-o", str(objects / "tests/Verification.olean"), str(candidate)], environment)

        def export(name: str, roots: list[str]) -> Path:
            result = run(["lake", "env", "leanexport", "tests.Verification", "--", *roots], environment)
            path = scratch / name
            path.write_text(result.stdout)
            return path

        def audit(model: Path, proof: Path, pin: str, name: str = "functional",
                  privacy: bool = False, expected_error: str | None = None,
                  policy_name: str = "policy", privacy_name: str = "privacy") -> dict:
            args = ["python3", "scripts/proofs/audit-source-proof.py", "--model-export", str(model),
                    "--proof-export", str(proof), "--trusted-model-sha256", pin,
                    "--policy", f"VerificationFixture.{policy_name}", "--functional-proof", f"VerificationFixture.{name}"]
            if privacy:
                args += ["--privacy-proof", f"VerificationFixture.{privacy_name}"]
            checked = subprocess.run(args, cwd=ROOT, capture_output=True, text=True, timeout=180)
            result = json.loads(checked.stdout)
            if expected_error:
                assert checked.returncode != 0, result
                assert expected_error in result["error"], result
            else:
                assert checked.returncode == 0, result
                assert result["compiledContractVerified"] is False
                assert result["sourceFunctionalChecked"] is True
                assert result["sourcePrivacyChecked"] is privacy
                assert "precondition" in result["specification"]
                assert "enabled" in result["specification"]
                assert "releaseDefinition" in result["specification"]
            return result

        build(source)
        model = export("trusted-model.ndjson", MODEL_ROOTS)
        pin = hashlib.sha256(model.read_bytes()).hexdigest()
        proofs = export("legitimate.ndjson", ["VerificationFixture.functional", "VerificationFixture.privacy",
                                               "VerificationFixture.releasingFunctional"])
        accepted = audit(model, proofs, pin, privacy=True)
        missing_privacy = audit(model, proofs, pin)
        assert missing_privacy["status"] == "source-functional-only"
        paired_roles = accepted["roleRecords"]
        assert [record["role"] for record in paired_roles] == ["functional", "privacy"]
        for record, obligation in zip(paired_roles, ("FunctionalObligation", "PrivacyObligation"), strict=True):
            declaration = f"Noctium.Verification.{obligation}"
            assert record["schemaVersion"] == 1
            assert record["obligationDeclaration"] == declaration
            assert record["policyDeclaration"] == "VerificationFixture.policy"
            assert record["proofDeclaration"] == f"VerificationFixture.{record['role']}"
            assert record["proposition"] == f"{declaration} VerificationFixture.policy"
            assert record["axioms"] == ["propext", "Classical.choice", "Quot.sound"]
        assert missing_privacy["roleRecords"] == paired_roles[:1]
        assert missing_privacy["axioms"] == paired_roles[0]["axioms"]
        assert set(accepted["axioms"]) == {axiom for record in paired_roles for axiom in record["axioms"]}
        audit(model, proofs, pin, policy_name="wrongContractPolicy", expected_error="wrong_obligation")
        audit(model, proofs, pin, policy_name="wrongSpecPolicy", expected_error="wrong_obligation")
        release_only = audit(model, proofs, pin, name="releasingFunctional", policy_name="releasingPolicy")
        assert release_only["sourcePrivacyChecked"] is False
        audit(model, proofs, pin, name="releasingFunctional", policy_name="releasingPolicy",
              privacy=True, privacy_name="releasingFunctional", expected_error="wrong_obligation")
        run(["lake", "env", "leanchecker", "--from-export", str(proofs)])
        counterexample = export("privacy-counterexample.ndjson", ["VerificationFixture.releasingNotPrivate"])
        run(["lake", "env", "leanchecker", "--from-export", str(counterexample)])

        # Keep the original model roots/pin stable. This separate UInt model
        # exercises fresh-environment numeral reporting and failure-channel scope.
        failure_model = export("failure-model.ndjson", [
            "Noctium.Verification.FunctionalObligation",
            "Noctium.Verification.PrivacyObligation",
            "VerificationFixture.failurePolicy", "VerificationFixture.failureAllOutcomesPolicy",
            "propext", "Classical.choice", "Quot.sound",
        ])
        failure_pin = hashlib.sha256(failure_model.read_bytes()).hexdigest()
        failure_proofs = export("failure-proofs.ndjson", [
            "VerificationFixture.failureFunctional", "VerificationFixture.failureSuccessfulPrivacy",
            "VerificationFixture.failureNotAllOutcomesPrivate",
        ])
        failure_accepted = audit(failure_model, failure_proofs, failure_pin, name="failureFunctional",
                                 privacy=True, policy_name="failurePolicy", privacy_name="failureSuccessfulPrivacy")
        assert failure_accepted["specification"]["privacyScope"] == "successful-only-under-pinned-precondition"
        assert failure_accepted["specification"]["releasePolicy"] == "none"
        audit(failure_model, failure_proofs, failure_pin, name="failureFunctional", privacy=True,
              policy_name="failureAllOutcomesPolicy", privacy_name="failureSuccessfulPrivacy",
              expected_error="wrong_obligation")
        run(["lake", "env", "leanchecker", "--from-export", str(failure_proofs)])

        for name in ["fromUserAxiom", "admitted", "alsoAdmitted", "fromNativeComputation"]:
            bad = export(f"{name}.ndjson", [f"VerificationFixture.{name}"])
            # Replay alone accepts these valid derivations relative to bad axioms.
            run(["lake", "env", "leanchecker", "--from-export", str(bad)])
            audit(model, bad, pin, name=name, expected_error="forbidden_axiom:")
        irrelevant = export("irrelevant.ndjson", ["VerificationFixture.irrelevant"])
        audit(model, irrelevant, pin, name="irrelevant", expected_error="wrong_obligation")
        audit(model, proofs, "0" * 64, expected_error="model_pin_mismatch")

        # Same module and declaration names, valid changed specification/proofs.
        original_postcondition = "outputs = [] ∧ after = withoutSettlementEffects before"
        changed_postcondition = "after = withoutSettlementEffects before ∧ outputs = []"
        assert source.count(original_postcondition) == 1, "registration fixture postcondition mutation target changed"
        build(source.replace(original_postcondition, changed_postcondition))
        changed_model = export("changed-model.ndjson", MODEL_ROOTS)
        changed_proofs = export("changed-proofs.ndjson", ["VerificationFixture.functional", "VerificationFixture.privacy"])
        audit(changed_model, changed_proofs, pin, privacy=True, expected_error="model_pin_mismatch")
        audit(model, changed_proofs, pin, privacy=True, expected_error="model_declaration_mismatch:")

        print(json.dumps({"status": "passed", "scope": "PA01 source proof and scoped privacy registration",
                          "trustedModelSha256": pin, "modelBytes": model.stat().st_size,
                          "proofBytes": proofs.stat().st_size, "axioms": accepted["axioms"],
                          "failurePrivacyScope": failure_accepted["specification"]["privacyScope"],
                          "compiledContractVerified": False}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
