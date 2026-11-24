#!/usr/bin/env python3
"""Check the reviewed BoundedScalars source policy and both proof roles offline.

The trusted model export is fixed at SHA-256
f570ba99a309ae2dd26d532a01ed38e98e2336c910e0fe634398cab0ae33c25e, reviewed
from source revision 5e843ebdfcfcc3b5656d842d7ccafa0eb375a2e7. To reproduce its
bytes after compiling the policy module, run:

  lake env leanexport proofs.BoundedScalarsVerification -- Noctium.Verification.FunctionalObligation Noctium.Verification.PrivacyObligation Noctium.BoundedScalarsVerification.policy propext Classical.choice Quot.sound

Supply those bytes with --trusted-model-export. The checker does not claim
compiled-contract or native verification.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[2]
PROOF_SOURCE = "proofs/BoundedScalarsVerification.lean"
PROOF_MODULE = "proofs.BoundedScalarsVerification"
POLICY = "Noctium.BoundedScalarsVerification.policy"
FUNCTIONAL_PROOF = "Noctium.BoundedScalarsVerification.functional"
PRIVACY_PROOF = "Noctium.BoundedScalarsVerification.privacy"
OPERATION = "BoundedScalars.apply"
TARGET_PROFILE = "profiles/midnight-ledger-9-zkir-3.2.1-target.json"
TARGET_PROFILE_SHA256 = "02b4242c2561232daea1d7d1d29bde68f3157eb9eed8cfb037254a0013f40093"
REVIEWED_MODEL_REVISION = "5e843ebdfcfcc3b5656d842d7ccafa0eb375a2e7"
TRUSTED_MODEL_SHA256 = "f570ba99a309ae2dd26d532a01ed38e98e2336c910e0fe634398cab0ae33c25e"
MODEL_ROOTS = [
    "Noctium.Verification.FunctionalObligation",
    "Noctium.Verification.PrivacyObligation",
    POLICY,
    "propext",
    "Classical.choice",
    "Quot.sound",
]


def run(args: list[str], environment: dict[str, str] | None = None) -> str:
    result = subprocess.run(args, cwd=ROOT, env=environment, capture_output=True,
                            text=True, timeout=300, check=False)
    if result.returncode:
        raise RuntimeError(f"command failed: {args}\n{result.stdout}\n{result.stderr}")
    return result.stdout


def export(module: str, roots: list[str], environment: dict[str, str]) -> bytes:
    result = subprocess.run(["lake", "env", "leanexport", module, "--", *roots],
                            cwd=ROOT, env=environment, capture_output=True,
                            timeout=300, check=False)
    if result.returncode or result.stderr or not result.stdout:
        raise RuntimeError(
            f"leanexport failed for {module} {roots}: "
            f"exit={result.returncode}, stderr={result.stderr.decode(errors='replace')}"
        )
    return result.stdout


def audit(model: Path, proofs: Path, functional: str = FUNCTIONAL_PROOF,
          privacy: str = PRIVACY_PROOF) -> tuple[subprocess.CompletedProcess[bytes], dict]:
    result = subprocess.run([
        "python3", "scripts/proofs/audit-source-proof.py",
        "--model-export", str(model),
        "--proof-export", str(proofs),
        "--trusted-model-sha256", TRUSTED_MODEL_SHA256,
        "--policy", POLICY,
        "--functional-proof", functional,
        "--privacy-proof", privacy,
    ], cwd=ROOT, capture_output=True, timeout=300, check=False)
    try:
        report = json.loads(result.stdout)
    except (json.JSONDecodeError, UnicodeDecodeError) as error:
        raise AssertionError(
            f"audit helper returned non-JSON output: {result.stdout!r} {result.stderr!r}"
        ) from error
    return result, report


def require_rejection(result: subprocess.CompletedProcess[bytes], report: dict,
                      expected_error: str) -> None:
    if result.returncode == 0 or expected_error not in str(report.get("error", "")):
        raise AssertionError(f"expected {expected_error!r}, got {result.returncode}: {report}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--trusted-model-export", type=Path, required=True,
                        help="reviewed model export containing the exact BoundedScalars policy")
    args = parser.parse_args()

    model = args.trusted_model_export.resolve()
    if not model.is_file():
        parser.error("--trusted-model-export must name a regular file")
    with model.open("rb") as handle:
        actual_pin = hashlib.file_digest(handle, "sha256").hexdigest()
    if actual_pin != TRUSTED_MODEL_SHA256:
        parser.error("trusted model export does not match the reviewed BoundedScalars model pin")

    run(["lake", "build", "Noctium", "Noctium.Cli", "Noctium.Compiler", "Noctium.Frontend",
         "Noctium.Verification.ExportAudit",
         "Noctium.Verification.ScalarNormalization", "Noctium.Verification.SourceEffects"])
    with tempfile.TemporaryDirectory(prefix="noctium-bounded-scalars-audit-") as directory:
        scratch = Path(directory)
        imports = scratch / "imports"
        (imports / "examples").mkdir(parents=True)
        (imports / "proofs").mkdir(parents=True)
        environment = os.environ.copy()
        environment["LEAN_PATH"] = str(imports)

        run(["lake", "env", "lean", "-D", "Elab.async=false", "-o",
             str(imports / "examples/BoundedScalars.olean"), "examples/BoundedScalars.lean"],
            environment)
        run(["lake", "env", "lean", "-D", "Elab.async=false", "-o",
             str(imports / "proofs/BoundedScalarsVerification.olean"), PROOF_SOURCE],
            environment)
        target_source = scratch / "source" / "BoundedScalarsTarget.lean"
        target_source.parent.mkdir(parents=True)
        target_source.write_text(f'''import {PROOF_MODULE}
example : Noctium.BoundedScalarsVerification.subject.contract.name = "BoundedScalars" := by rfl
example : Noctium.BoundedScalarsVerification.subject.entry.name = "apply" := by rfl
''')
        run(["lake", "env", "lean", "-D", "Elab.async=false", "--root",
             str(target_source.parent), "-o", str(imports / "BoundedScalarsTarget.olean"),
             str(target_source)], environment)

        functional = FUNCTIONAL_PROOF
        privacy = PRIVACY_PROOF
        positive_roots = [functional, privacy]
        positive = scratch / "proofs.ndjson"
        positive.write_bytes(export(PROOF_MODULE, positive_roots, environment))
        first, accepted = audit(model, positive)
        second, repeated = audit(model, positive)
        if first.returncode or second.returncode:
            raise AssertionError(f"positive audit rejected: {accepted}")
        if first.stdout != second.stdout:
            raise AssertionError("repeated source-proof audit reports are not byte-stable")
        if accepted.get("sourceFunctionalChecked") is not True or \
                accepted.get("sourcePrivacyChecked") is not True:
            raise AssertionError(f"both proof roles are required: {accepted}")
        if accepted.get("compiledContractVerified") is not False:
            raise AssertionError(f"unexpected compiled-contract status: {accepted}")
        if accepted.get("status") != "source-functional-and-scoped-privacy-checked" or \
                accepted.get("trustedModelSha256") != TRUSTED_MODEL_SHA256 or \
                accepted.get("externalModelPinChecked") is not True:
            raise AssertionError(f"unexpected report identity or role status: {accepted}")
        if accepted.get("specificationReviewVerified") is not False or \
                accepted.get("sourceAuthorizationCorrespondenceProved") is not False:
            raise AssertionError(f"unexpected specification or authorization status: {accepted}")
        if set(accepted.get("axioms", [])) - {"propext", "Classical.choice", "Quot.sound"}:
            raise AssertionError(f"unexpected proof axioms: {accepted}")

        missing = scratch / "missing-privacy.ndjson"
        missing.write_bytes(export(PROOF_MODULE, [functional], environment))
        missing_result, missing_report = audit(model, missing)
        require_rejection(missing_result, missing_report, "unknown_proof")

        substituted_result, substituted_report = audit(
            model, positive, functional=privacy, privacy=functional)
        require_rejection(substituted_result, substituted_report, "wrong_obligation")

        specification = accepted["specification"]
        profile_path = ROOT / TARGET_PROFILE
        profile = json.loads(profile_path.read_text())
        if (profile.get("name"), profile.get("ledger"), profile.get("zkir")) != \
                ("midnight-ledger-9-zkir-3.2.1", "9.1.0.1", "3.2.1"):
            raise AssertionError(f"unexpected target profile identity: {profile}")
        artifacts = scratch / "ledger"
        run(["lake", "env", "lean", "--run", "NoctiumMain.lean", "compile",
             "examples/BoundedScalars.lean", "--target", TARGET_PROFILE, "--emit", "ledger",
             "--output", str(artifacts)])
        contract, entrypoint = OPERATION.split(".")
        association = json.loads(run([
            "python3", "scripts/proofs/check-source-operation-artifacts.py",
            "--artifacts", str(artifacts), "--profile", TARGET_PROFILE,
            "--profile-sha256", TARGET_PROFILE_SHA256,
            "--contract", contract, "--entrypoint", entrypoint,
        ]))
        report = {
            "status": "passed",
            "reviewedModelRevision": REVIEWED_MODEL_REVISION,
            "externalModelRoots": MODEL_ROOTS,
            "scope": OPERATION,
            "policy": POLICY,
            "functionalProof": functional,
            "privacyProof": privacy,
            "operation": OPERATION,
            "operationSubjectCheckedByKernel": True,
            "targetProfile": {
                "path": TARGET_PROFILE,
                "name": profile["name"],
                "ledger": profile["ledger"],
                "zkir": profile["zkir"],
                "sha256": TARGET_PROFILE_SHA256,
            },
            "operationArtifacts": association,
            "trustedModelSha256": TRUSTED_MODEL_SHA256,
            "proofExportSha256": hashlib.sha256(positive.read_bytes()).hexdigest(),
            "byteStableAuditReport": True,
            "roleRecords": accepted["roleRecords"],
            "axioms": accepted["axioms"],
            "privacyObservation": {
                key: specification[key]
                for key in ["releasePolicy", "privacyScope", "publicObserver",
                            "publicEquivalence", "privacyDomain"]
            },
            "rejections": {
                "missingRequestedPrivacyProof": missing_report["error"],
                "substitutedProofRole": substituted_report["error"],
            },
            "specificationReviewVerified": accepted["specificationReviewVerified"],
            "sourceAuthorizationCorrespondenceProved": accepted["sourceAuthorizationCorrespondenceProved"],
            "remainingGates": accepted["remainingGates"],
            "compiledContractVerified": False,
        }
        print(json.dumps(report, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
