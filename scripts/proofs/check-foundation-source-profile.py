#!/usr/bin/env python3
"""Gate the two pinned Foundation source reports and their exact ledger artifacts.

Produce each report with its existing source audit driver. Pass the report JSON
and the corresponding fresh compiler output directory to this gate. This profile
checks source proof identities, model pins, the successful-only observer, and the
manifest association with the emitted ZKIR and Impact bytes.

The reports must come from check-private-claim-audit.py --report and
check-bounded-scalars-audit.py --trusted-model-export. This gate checks report
content and artifact binding. It does not authenticate report authorship or
establish native semantics, deployment identity, or independent review.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import runpy
import sys
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
PROFILE_PATH = ROOT / "profiles/foundation-source-v1.json"
ARTIFACT_CHECKER = runpy.run_path(str(ROOT / "scripts/proofs/check-source-operation-artifacts.py"))
PRIVATE_CHECKER = runpy.run_path(str(ROOT / "scripts/proofs/check-private-claim-audit.py"))
BOUNDED_CHECKER = runpy.run_path(str(ROOT / "scripts/proofs/check-bounded-scalars-audit.py"))
APPROVED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
EXPECTED_OPERATIONS = ["PrivateClaim.claim", "BoundedScalars.apply"]


def fail(operation: str, reason: str) -> ValueError:
    return ValueError(f"{operation}: foundation-source-v1: {reason}")


def strict_object(path: Path, label: str) -> tuple[dict[str, Any], bytes]:
    if path.is_symlink() or not path.is_file():
        raise ValueError(f"{label}_file_missing_or_symlinked")
    contents = path.read_bytes()
    return ARTIFACT_CHECKER["strict_json"](contents, label), contents


def stable_json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=True, sort_keys=True, separators=(",", ":"))


def profile_data() -> tuple[dict[str, Any], bytes, dict[str, Any]]:
    profile, profile_bytes = strict_object(PROFILE_PATH, "foundation_profile")
    if type(profile.get("schemaVersion")) is not int or profile.get("schemaVersion") != 1:
        raise ValueError("unsupported_foundation_profile_schema")
    if profile.get("name") != "foundation-source-v1":
        raise ValueError("foundation_profile_name_mismatch")
    operations = profile.get("operations")
    if (not isinstance(operations, list)
            or [item.get("operation") if isinstance(item, dict) else None for item in operations]
            != EXPECTED_OPERATIONS):
        raise ValueError("foundation_profile_operation_set_mismatch")
    private, bounded = operations
    if (private.get("contract"), private.get("entrypoint"), private.get("policy"),
            private.get("functionalProof"), private.get("privacyProof"),
            private.get("modelPinPath")) != (
            PRIVATE_CHECKER["OPERATION"].split(".", 1)[0],
            PRIVATE_CHECKER["OPERATION"].split(".", 1)[1],
            PRIVATE_CHECKER["NS"] + ".policy",
            PRIVATE_CHECKER["NS"] + ".functional",
            PRIVATE_CHECKER["NS"] + ".privacy",
            PRIVATE_CHECKER["MODEL_PIN"].relative_to(ROOT).as_posix()):
        raise ValueError("foundation_profile_private_claim_identity_mismatch")
    if (private.get("circuit") != "claimRelation"
            or (ROOT / PRIVATE_CHECKER["TARGET"]).relative_to(ROOT).as_posix()
            != profile.get("targetProfile", {}).get("path")):
        raise ValueError("foundation_profile_private_claim_source_mismatch")
    if (bounded.get("contract"), bounded.get("entrypoint"), bounded.get("policy"),
            bounded.get("functionalProof"), bounded.get("privacyProof"),
            bounded.get("modelPinSha256")) != (
            BOUNDED_CHECKER["OPERATION"].split(".", 1)[0],
            BOUNDED_CHECKER["OPERATION"].split(".", 1)[1],
            BOUNDED_CHECKER["POLICY"],
            BOUNDED_CHECKER["FUNCTIONAL_PROOF"],
            BOUNDED_CHECKER["PRIVACY_PROOF"],
            BOUNDED_CHECKER["TRUSTED_MODEL_SHA256"]):
        raise ValueError("foundation_profile_bounded_scalars_identity_mismatch")
    if (bounded.get("circuit") != "boundedRelation"
            or Path(BOUNDED_CHECKER["TARGET_PROFILE"]).as_posix()
            != profile.get("targetProfile", {}).get("path")):
        raise ValueError("foundation_profile_bounded_scalars_source_mismatch")

    target = profile.get("targetProfile")
    if not isinstance(target, dict):
        raise ValueError("foundation_profile_target_missing")
    target_path = ROOT / target.get("path", "")
    target_data, target_bytes = strict_object(target_path, "target_profile")
    target_sha256 = hashlib.sha256(target_bytes).hexdigest()
    expected_target = {
        "name": target_data.get("name"),
        "ledger": target_data.get("ledger"),
        "zkir": target_data.get("zkir"),
        "sha256": target_sha256,
    }
    if (target.get("sha256") != PRIVATE_CHECKER["TARGET_PROFILE_SHA256"]
            or target.get("sha256") != BOUNDED_CHECKER["TARGET_PROFILE_SHA256"]
            or target.get("sha256") != target_sha256
            or any(target.get(key) != value for key, value in expected_target.items() if key != "sha256")):
        raise ValueError("foundation_profile_target_pin_mismatch")
    return profile, profile_bytes, expected_target


def model_pin(operation: dict[str, Any]) -> str:
    name = operation["operation"]
    if name == "PrivateClaim.claim":
        pin_path = ROOT / operation["modelPinPath"]
        if pin_path.is_symlink() or not pin_path.is_file():
            raise fail(name, "fixture_model_pin_file_missing_or_symlinked")
        try:
            pin = pin_path.read_text(encoding="ascii").strip()
        except (OSError, UnicodeDecodeError) as error:
            raise fail(name, "fixture_model_pin_unreadable") from error
    else:
        pin = operation.get("modelPinSha256")
        if pin != BOUNDED_CHECKER["TRUSTED_MODEL_SHA256"]:
            raise fail(name, "profile_model_pin_differs_from_source_report_driver")
    if not isinstance(pin, str) or re.fullmatch(r"[0-9a-f]{64}", pin) is None:
        raise fail(name, "invalid_fixture_model_pin")
    return pin


def expected_roles(operation: dict[str, Any]) -> list[dict[str, str]]:
    policy = operation["policy"]
    return [
        {"role": "functional", "obligation": "Noctium.Verification.FunctionalObligation",
         "proof": operation["functionalProof"], "policy": policy},
        {"role": "privacy", "obligation": "Noctium.Verification.PrivacyObligation",
         "proof": operation["privacyProof"], "policy": policy},
    ]


def validate_role_records(operation: str, report: dict[str, Any],
                          expected: list[dict[str, str]]) -> list[dict[str, Any]]:
    records = report.get("roleRecords")
    if not isinstance(records, list) or len(records) != 2:
        raise fail(operation, "required_role_records_missing_or_duplicated")
    all_axioms: set[str] = set()
    normalized = []
    for record, identity in zip(records, expected, strict=True):
        role = identity["role"]
        if not isinstance(record, dict):
            raise fail(operation, f"{role}_role_record_malformed")
        fields = {
            "role": role,
            "obligationDeclaration": identity["obligation"],
            "policyDeclaration": identity["policy"],
            "proofDeclaration": identity["proof"],
            "proposition": f"{identity['obligation']} {identity['policy']}",
        }
        if (type(record.get("schemaVersion")) is not int or record.get("schemaVersion") != 1
                or any(record.get(key) != value for key, value in fields.items())):
            raise fail(operation, f"{role}_role_identity_mismatch")
        normalized_proposition = record.get("policyNormalizedProposition")
        if not isinstance(normalized_proposition, str) or identity["policy"] not in normalized_proposition:
            raise fail(operation, f"{role}_normalized_policy_missing")
        axioms = record.get("axioms")
        if (not isinstance(axioms, list) or any(not isinstance(item, str) for item in axioms)
                or len(axioms) != len(set(axioms)) or set(axioms) - set(APPROVED_AXIOMS)
                or axioms != [item for item in APPROVED_AXIOMS if item in axioms]):
            raise fail(operation, f"{role}_axiom_provenance_mismatch")
        all_axioms.update(axioms)
        normalized.append({"schemaVersion": 1, **fields, "axioms": axioms})

    aggregate = report.get("axioms")
    expected_aggregate = [item for item in APPROVED_AXIOMS if item in all_axioms]
    if aggregate != expected_aggregate:
        raise fail(operation, "aggregate_axiom_provenance_mismatch")
    return normalized


def validate_private_registration(operation: dict[str, Any], report: dict[str, Any]) -> None:
    name = operation["operation"]
    if report.get("selectedOperations") != [name]:
        raise fail(name, "selected_operation_mismatch")
    coverage = report.get("sourceProofCoverage")
    if not isinstance(coverage, list) or len(coverage) != 1 or not isinstance(coverage[0], dict):
        raise fail(name, "source_registration_report_missing_or_duplicated")
    contract = coverage[0]
    if (type(contract.get("schemaVersion")) is not int or contract.get("schemaVersion") != 1
            or contract.get("kind") != "source-proof-coverage"
            or contract.get("contract") != operation["contract"]
            or contract.get("status") != "covered"
            or contract.get("sourceProofsRechecked") is not True):
        raise fail(name, "source_registration_report_mismatch")
    rows = contract.get("entrypoints")
    if not isinstance(rows, list) or len(rows) != 1 or not isinstance(rows[0], dict):
        raise fail(name, "source_entrypoint_registration_missing_or_duplicated")
    row = rows[0]
    if (type(row.get("index")) is not int or row.get("index") != 0
            or row.get("entrypoint") != operation["entrypoint"]
            or row.get("status") != "covered" or row.get("policyPairing") != "matched"):
        raise fail(name, "source_entrypoint_registration_mismatch")
    roles = row.get("roles")
    if not isinstance(roles, list) or len(roles) != 2:
        raise fail(name, "source_role_registration_missing_or_duplicated")
    records = {item.get("role"): item for item in roles if isinstance(item, dict)}
    if len(records) != 2 or set(records) != {"functional", "privacy"}:
        raise fail(name, "source_role_registration_identity_mismatch")
    for identity in expected_roles(operation):
        role = identity["role"]
        registration = records[role]
        registrations = registration.get("registrations")
        if (registration.get("status") != "covered"
                or type(registration.get("duplicateRegistrationCount")) is not int
                or registration.get("duplicateRegistrationCount") != 0
                or not isinstance(registrations, list) or len(registrations) != 1
                or not isinstance(registrations[0], dict)
                or registrations[0].get("policy") != identity["policy"]
                or registrations[0].get("proof") != identity["proof"]):
            raise fail(name, f"{role}_source_registration_mismatch")


def validate_report(operation: dict[str, Any], report: dict[str, Any], report_bytes: bytes,
                    artifacts: Path, target: dict[str, Any], profile: dict[str, Any]) -> dict[str, Any]:
    name = operation["operation"]
    if report.get("operation") != name:
        raise fail(name, "crossed_source_operation")
    pin = model_pin(operation)
    if report.get("trustedModelSha256") != pin:
        raise fail(name, "fixture_model_pin_mismatch")
    if (report.get("policy") != operation["policy"]
            or report.get("functionalProof") != operation["functionalProof"]
            or report.get("privacyProof") != operation["privacyProof"]):
        raise fail(name, "source_report_proof_identity_mismatch")
    report_target = report.get("targetProfile")
    if not isinstance(report_target, dict) or report_target.get("name") != target["name"]:
        raise fail(name, "target_profile_name_mismatch")
    for key in ("ledger", "zkir", "sha256"):
        if report_target.get(key) != target[key]:
            raise fail(name, "target_profile_mismatch")
    if name == "BoundedScalars.apply" and report_target.get("path") != profile["targetProfile"]["path"]:
        raise fail(name, "target_profile_path_mismatch")

    if name == "PrivateClaim.claim":
        if (report.get("status") != "source-functional-and-scoped-privacy-checked"
                or report.get("sourceFunctionalChecked") is not True
                or report.get("sourcePrivacyChecked") is not True):
            raise fail(name, "source_proof_report_incomplete")
        validate_private_registration(operation, report)
        observation = report.get("specification")
        if not isinstance(observation, dict):
            raise fail(name, "privacy_observation_missing")
    else:
        if (report.get("status") != "passed" or report.get("scope") != name
                or report.get("operationSubjectCheckedByKernel") is not True):
            raise fail(name, "source_proof_report_incomplete")
        observation = report.get("privacyObservation")
        if not isinstance(observation, dict):
            raise fail(name, "privacy_observation_missing")

    for key, expected in profile["privacyObservation"].items():
        if observation.get(key) != expected:
            raise fail(name, f"privacy_observation_mismatch:{key}")
    if (report.get("compiledContractVerified") is not False
            or report.get("specificationReviewVerified") is not False
            or report.get("sourceAuthorizationCorrespondenceProved") is not False):
        raise fail(name, "source_report_overstates_qualification")
    if name == "PrivateClaim.claim" and report.get("externalModelPinChecked") is not True:
        raise fail(name, "private_claim_external_model_pin_not_checked")

    expected = expected_roles(operation)
    role_records = validate_role_records(name, report, expected)
    actual_artifacts = report.get("operationArtifacts")
    try:
        checked_artifacts = ARTIFACT_CHECKER["bind_operation"](
            artifacts, ROOT / profile["targetProfile"]["path"], profile["targetProfile"]["sha256"],
            operation["contract"], operation["entrypoint"],
        )
    except (OSError, ValueError) as error:
        raise fail(name, f"operation_artifact_check_failed:{error}") from error
    if stable_json(actual_artifacts) != stable_json(checked_artifacts):
        raise fail(name, "reported_operation_artifact_identity_mismatch")
    if checked_artifacts.get("operation", {}).get("circuit") != operation["circuit"]:
        raise fail(name, "selected_circuit_identity_mismatch")

    return {
        "operation": name,
        "reportKind": operation["reportKind"],
        "sourceReportSha256": hashlib.sha256(report_bytes).hexdigest(),
        "modelSha256": pin,
        "proofRoles": role_records,
        "privacyObservation": {key: observation[key] for key in profile["privacyObservation"]},
        "operationArtifacts": checked_artifacts,
        "compiledContractVerified": False,
        "specificationReviewVerified": False,
    }


def run_profile(reports: dict[str, Path], artifact_dirs: dict[str, Path]) -> dict[str, Any]:
    profile, profile_bytes, target = profile_data()
    operations = []
    for operation in profile["operations"]:
        name = operation["operation"]
        report, report_bytes = strict_object(reports[name], f"{name}_source_report")
        operations.append(validate_report(operation, report, report_bytes,
                                          artifact_dirs[name], target, profile))
    requirements = [
        {"operation": operation["operation"], "name": requirement["name"], "status": "open",
         "requiredEvidence": requirement["requiredEvidence"]}
        for operation in profile["operations"]
        for requirement in profile["openRequirements"]
    ]
    return {
        "schemaVersion": 1,
        "profile": profile["name"],
        "profileSha256": hashlib.sha256(profile_bytes).hexdigest(),
        "status": "source-evidence-checked",
        "targetProfile": target,
        "scope": {
            "operations": EXPECTED_OPERATIONS,
            "evidence": "Pinned Lean functional and successful-only privacy roles plus exact emitted operation artifacts.",
            "excluded": profile["excludedScope"],
        },
        "operations": operations,
        "openRequirements": requirements,
    }


def render_text(evidence: dict[str, Any]) -> str:
    target = evidence["targetProfile"]
    lines = [f"{evidence['profile']}: {evidence['status']}",
             f"Profile SHA-256: {evidence['profileSha256']}",
             f"Target: {target['name']} (Ledger {target['ledger']}, ZKIR {target['zkir']})",
             "Scope: source proof roles and exact emitted operation artifacts."]
    for operation in evidence["operations"]:
        lines.extend(["", operation["operation"],
                      f"  Source report SHA-256: {operation['sourceReportSha256']}",
                      f"  Fixture model SHA-256: {operation['modelSha256']}"])
        for role in operation["proofRoles"]:
            lines.append(f"  {role['role']}: {role['proofDeclaration']} proves {role['proposition']}")
            lines.append(f"    Axioms: {', '.join(role['axioms']) or 'none'}")
        observer = operation["privacyObservation"]
        lines.append(f"  Privacy scope: {observer['privacyScope']}, release policy {observer['releasePolicy']}")
        lines.append(f"  Public observer: {observer['publicObserver']}")
        for artifact in operation["operationArtifacts"]["artifacts"]:
            lines.append(f"  {artifact['role']}: {artifact['file']} ({artifact['bytes']} bytes, SHA-256 {artifact['sha256']})")
    lines.extend(["", f"Open requirements: {len(evidence['openRequirements'])}"])
    for requirement in evidence["openRequirements"]:
        lines.append(f"  {requirement['operation']} [{requirement['name']}]: {requirement['requiredEvidence']}")
    lines.append("Native execution, deployment, and independent review require separate evidence.")
    return "\n".join(lines) + "\n"


def render_json(evidence: dict[str, Any]) -> str:
    return json.dumps(evidence, ensure_ascii=False, indent=2, sort_keys=True) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--private-claim-report", type=Path, required=True,
                        help="JSON output from check-private-claim-audit.py --report")
    parser.add_argument("--private-claim-artifacts", type=Path, required=True,
                        help="fresh ledger compile output for examples/PrivateClaim.lean")
    parser.add_argument("--bounded-scalars-report", type=Path, required=True,
                        help="JSON output from check-bounded-scalars-audit.py --trusted-model-export")
    parser.add_argument("--bounded-scalars-artifacts", type=Path, required=True,
                        help="fresh ledger compile output for examples/BoundedScalars.lean")
    parser.add_argument("--format", choices=["text", "json"], default="text")
    args = parser.parse_args()
    reports = {
        "PrivateClaim.claim": args.private_claim_report,
        "BoundedScalars.apply": args.bounded_scalars_report,
    }
    artifact_dirs = {
        "PrivateClaim.claim": args.private_claim_artifacts,
        "BoundedScalars.apply": args.bounded_scalars_artifacts,
    }
    try:
        evidence = run_profile(reports, artifact_dirs)
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(str(error), file=sys.stderr)
        return 1
    if args.format == "json":
        print(render_json(evidence), end="")
    else:
        print(render_text(evidence), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
