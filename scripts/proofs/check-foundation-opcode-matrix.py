#!/usr/bin/env python3
"""Join exact Foundation pilot ZKIR bytes to pinned historical opcode evidence.

This offline check reads a retained Foundation report and two generated artifact
directories. It verifies each selected raw ZKIR digest and the pinned target,
then joins each observed instruction to one row in the pinned opcode matrix.
Matrix workload stages and evidence IDs describe prior workloads only. They do
not establish stage execution for either Foundation pilot artifact.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import sys
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
PROFILE_PATH = ROOT / "profiles/midnight-ledger-9-zkir-3.2.1-target.json"
MATRIX_PATH = ROOT / "docs/compatibility/zkir-feature-matrix.json"
HISTORY_PATH = ROOT / "tests/zkir321/qualification-evidence.json"
PROFILE_SHA256 = "02b4242c2561232daea1d7d1d29bde68f3157eb9eed8cfb037254a0013f40093"
MATRIX_SHA256 = "445b30297dc6d4181b9c49d57c03cb24e448b8dcb861351a10fac3649a6c3d9e"
HISTORY_SHA256 = "80ab92eb45777b6c0c6880d7b908bc4e6c3b82c11459f2d237b3bc6c36716293"
PROFILE_NAME = "foundation-source-v1"
OPERATIONS = ("PrivateClaim.claim", "BoundedScalars.apply")
OPERATION_FILES = {
    "PrivateClaim.claim": "PrivateClaim.claim.zkir",
    "BoundedScalars.apply": "BoundedScalars.apply.zkir",
}
STAGES = ("keygen", "checker", "proof", "ledger")
OPEN_REQUIREMENTS = (
    "source-elaboration",
    "native-soundness",
    "native-completeness",
    "native-observation-correspondence",
    "abi-witness-conformance",
    "artifact-certificate",
    "deployed-identity",
    "independent-specification-review",
)
OPCODE_PATTERN = re.compile(r"[a-z][a-z0-9_]*\Z")
MATRIX_ID_PATTERN = re.compile(r"ZKIR-OP-[A-Z0-9-]+\Z")
SHA256_PATTERN = re.compile(r"[0-9a-f]{64}\Z")


def require(condition: bool, code: str) -> None:
    if not condition:
        raise ValueError(code)


def digest(contents: bytes) -> str:
    return hashlib.sha256(contents).hexdigest()


def strict_json(contents: bytes, subject: str) -> Any:
    def object_without_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"duplicate_json_key: {subject}.{key}")
            result[key] = value
        return result

    def reject_constant(value: str) -> None:
        raise ValueError(f"invalid_json_constant: {subject}.{value}")

    try:
        return json.loads(contents, object_pairs_hook=object_without_duplicates,
                          parse_constant=reject_constant)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ValueError(f"invalid_json: {subject}") from error


def strict_json_object(contents: bytes, subject: str) -> dict[str, Any]:
    value = strict_json(contents, subject)
    require(isinstance(value, dict), f"invalid_json_object: {subject}")
    return value


def load_pinned(path: Path, expected_sha256: str, subject: str) -> tuple[bytes, dict[str, Any]]:
    contents = path.read_bytes()
    require(digest(contents) == expected_sha256, f"{subject}_pin_mismatch")
    return contents, strict_json_object(contents, subject)


def target_identity(profile: dict[str, Any]) -> dict[str, Any]:
    native_source = profile.get("nativeSource")
    require(isinstance(native_source, dict), "target_profile_native_source_missing")
    require(profile.get("name") == "midnight-ledger-9-zkir-3.2.1"
            and profile.get("ledger") == "9.1.0.1"
            and profile.get("zkir") == "3.2.1"
            and native_source.get("revision") == "7a51b3385bbf4bce3604df87a7c70867c9ab43c0",
            "target_profile_identity_mismatch")
    return {
        "ledger": profile["ledger"],
        "name": profile["name"],
        "sha256": PROFILE_SHA256,
        "zkir": profile["zkir"],
    }


def validate_matrix_target(matrix: dict[str, Any], profile: dict[str, Any]) -> None:
    target = matrix.get("target")
    require(isinstance(target, dict)
            and target.get("zkirRelease") == profile.get("zkir")
            and target.get("zkirRevision") == profile.get("nativeSource", {}).get("revision")
            and target.get("ledgerRelease") == profile.get("ledger"),
            "matrix_target_profile_mismatch")


def matrix_opcode_rows(matrix: dict[str, Any]) -> dict[str, dict[str, Any]]:
    entries = matrix.get("entries")
    require(isinstance(entries, list), "matrix_entries_missing")
    by_opcode: dict[str, dict[str, Any]] = {}
    ids: set[str] = set()
    for entry in entries:
        if not isinstance(entry, dict) or entry.get("kind") != "instruction":
            continue
        row_id = entry.get("id")
        opcode = entry.get("jsonOpcode")
        require(isinstance(row_id, str) and MATRIX_ID_PATTERN.fullmatch(row_id) is not None,
                "invalid_matrix_opcode_row_id")
        require(isinstance(opcode, str) and OPCODE_PATTERN.fullmatch(opcode) is not None,
                f"invalid_matrix_json_opcode: {row_id}")
        require(row_id not in ids, f"duplicate_matrix_opcode_row_id: {row_id}")
        require(opcode not in by_opcode, f"duplicate_matrix_json_opcode: {opcode}")
        evidence = entry.get("evidence")
        require(isinstance(evidence, dict), f"matrix_opcode_evidence_missing: {row_id}")
        evidence_ids = evidence.get("ids")
        require(isinstance(evidence_ids, list)
                and all(isinstance(item, str) and item for item in evidence_ids),
                f"matrix_opcode_evidence_ids_invalid: {row_id}")
        require(len(set(evidence_ids)) == len(evidence_ids),
                f"duplicate_matrix_evidence_id: {row_id}")
        stages = {}
        for stage in STAGES:
            value = evidence.get(f"{stage}WorkloadObserved")
            require(type(value) is bool, f"matrix_opcode_stage_invalid: {row_id}.{stage}")
            stages[stage] = value
        ids.add(row_id)
        by_opcode[opcode] = {
            "matrixRowId": row_id,
            "evidenceIds": sorted(evidence_ids),
            "workloadStages": stages,
        }
    require(bool(by_opcode), "matrix_instruction_rows_missing")
    return by_opcode


def pinned_matrix(profile: dict[str, Any]) -> tuple[dict[str, dict[str, Any]], dict[str, str]]:
    matrix_bytes, matrix = load_pinned(MATRIX_PATH, MATRIX_SHA256, "native_feature_matrix")
    history_bytes, _history = load_pinned(HISTORY_PATH, HISTORY_SHA256, "native_feature_history")
    validate_matrix_target(matrix, profile)
    return matrix_opcode_rows(matrix), {
        "matrixContentSha256": digest(matrix_bytes),
        "matrixHistoryContentSha256": digest(history_bytes),
    }


def foundation_operations(report: dict[str, Any], expected_target: dict[str, Any]) -> tuple[dict[str, dict[str, Any]], list[dict[str, Any]]]:
    require(type(report.get("schemaVersion")) is int and report.get("schemaVersion") == 1,
            "unsupported_foundation_report_schema")
    require(report.get("profile") == PROFILE_NAME, "foundation_profile_mismatch")
    require(report.get("status") == "source-evidence-checked", "foundation_report_not_checked")
    require(report.get("targetProfile") == expected_target, "foundation_target_profile_pin_mismatch")
    scope = report.get("scope")
    require(isinstance(scope, dict) and scope.get("operations") == list(OPERATIONS),
            "foundation_scope_operation_mismatch")

    gaps = report.get("openRequirements")
    require(isinstance(gaps, list), "foundation_open_requirements_missing")
    gap_keys: set[tuple[str, str]] = set()
    for item in gaps:
        require(isinstance(item, dict), "foundation_open_requirement_malformed")
        operation = item.get("operation")
        requirement = item.get("requirement")
        require(operation in OPERATIONS and isinstance(requirement, str)
                and item.get("profile") == PROFILE_NAME and item.get("status") == "open",
                "foundation_open_requirement_invalid")
        key = (operation, requirement)
        require(key not in gap_keys, f"duplicate_foundation_open_requirement: {operation}.{requirement}")
        gap_keys.add(key)
    for operation in OPERATIONS:
        missing = set(OPEN_REQUIREMENTS) - {req for op, req in gap_keys if op == operation}
        require(not missing, f"foundation_open_requirements_incomplete: {operation}")

    rows = report.get("operations")
    require(isinstance(rows, list), "foundation_operations_missing")
    by_name: dict[str, dict[str, Any]] = {}
    for row in rows:
        require(isinstance(row, dict) and isinstance(row.get("operation"), str),
                "foundation_operation_malformed")
        name = row["operation"]
        require(name not in by_name, f"duplicate_foundation_operation: {name}")
        artifacts = row.get("operationArtifacts")
        require(isinstance(artifacts, dict)
                and type(artifacts.get("schemaVersion")) is int
                and artifacts.get("schemaVersion") == 1
                and artifacts.get("operation") == name,
                f"foundation_operation_artifact_identity_missing: {name}")
        by_name[name] = row
    require(set(by_name) == set(OPERATIONS), "foundation_operation_set_mismatch")
    return by_name, gaps


def reported_zkir(operation: str, artifact_directory: Path,
                  recorded_artifacts: dict[str, Any]) -> tuple[bytes, dict[str, Any]]:
    files = recorded_artifacts.get("files")
    require(isinstance(files, list), f"foundation_operation_files_missing: {operation}")
    by_role: dict[str, dict[str, Any]] = {}
    paths: set[str] = set()
    for item in files:
        require(isinstance(item, dict), f"foundation_operation_file_malformed: {operation}")
        role = item.get("role")
        path = item.get("path")
        size = item.get("bytes")
        sha256 = item.get("sha256")
        require(role in ("manifest", "zkir", "impact") and role not in by_role,
                f"foundation_operation_file_roles_invalid: {operation}")
        require(isinstance(path, str) and Path(path).name == path and path not in paths,
                f"foundation_operation_file_path_invalid: {operation}")
        require(type(size) is int and size > 0 and isinstance(sha256, str)
                and SHA256_PATTERN.fullmatch(sha256) is not None,
                f"foundation_operation_file_digest_invalid: {operation}")
        by_role[role] = item
        paths.add(path)
    require(set(by_role) == {"manifest", "zkir", "impact"},
            f"foundation_operation_file_roles_incomplete: {operation}")
    zkir_row = by_role["zkir"]
    expected_filename = OPERATION_FILES[operation]
    require(by_role["manifest"]["path"] == "noctium.json"
            and by_role["impact"]["path"] == operation + ".impact.json",
            f"foundation_operation_artifact_crossed: {operation}")
    require(zkir_row["path"] == expected_filename,
            f"foundation_operation_artifact_crossed: {operation}")
    zkir_path = artifact_directory / expected_filename
    require(not zkir_path.is_symlink() and zkir_path.is_file(),
            f"foundation_zkir_missing: {operation}")
    contents = zkir_path.read_bytes()
    require(len(contents) == zkir_row["bytes"] and digest(contents) == zkir_row["sha256"],
            f"foundation_zkir_digest_mismatch: {operation}")
    zkir = strict_json_object(contents, f"{operation}_zkir")
    version = zkir.get("version")
    require(isinstance(version, dict) and version.get("major") == 3 and version.get("minor") == 2,
            f"foundation_zkir_version_mismatch: {operation}")
    instructions = zkir.get("instructions")
    require(isinstance(instructions, list), f"foundation_zkir_instructions_missing: {operation}")
    return contents, zkir


def opcode_histogram(operation: str, zkir: dict[str, Any],
                     matrix_rows: dict[str, dict[str, Any]]) -> list[dict[str, Any]]:
    instructions = zkir.get("instructions")
    counts: Counter[str] = Counter()
    for instruction in instructions:
        require(isinstance(instruction, dict), f"foundation_zkir_instruction_malformed: {operation}")
        opcode = instruction.get("op")
        require(isinstance(opcode, str) and OPCODE_PATTERN.fullmatch(opcode) is not None,
                f"foundation_zkir_opcode_invalid: {operation}")
        require(opcode in matrix_rows, f"unknown_matrix_opcode: {opcode}")
        counts[opcode] += 1

    result = []
    for opcode in sorted(counts):
        matrix_row = matrix_rows[opcode]
        stages = matrix_row["workloadStages"]
        result.append({
            "opcode": opcode,
            "count": counts[opcode],
            "matrixRowId": matrix_row["matrixRowId"],
            "evidenceIds": matrix_row["evidenceIds"],
            "workloadStages": stages,
            "observedStages": [stage for stage in STAGES if stages[stage]],
            "unobservedStages": [stage for stage in STAGES if not stages[stage]],
            "stageEvidenceScope": "historical matrix workload observations only",
        })
    return result


def build_evidence(foundation_bytes: bytes, artifact_directories: dict[str, Path]) -> dict[str, Any]:
    _, profile = load_pinned(PROFILE_PATH, PROFILE_SHA256, "target_profile")
    target = target_identity(profile)
    foundation = strict_json_object(foundation_bytes, "foundation_report")
    foundation_by_operation, gaps = foundation_operations(foundation, target)
    require(set(artifact_directories) == set(OPERATIONS), "operation_artifact_directory_set_mismatch")
    matrix_rows, matrix_pins = pinned_matrix(profile)

    operations = []
    for operation in OPERATIONS:
        artifact_bytes, zkir = reported_zkir(
            operation, artifact_directories[operation],
            foundation_by_operation[operation]["operationArtifacts"])
        counts = opcode_histogram(operation, zkir, matrix_rows)
        operations.append({
            "operation": operation,
            "rawZkir": {
                "path": OPERATION_FILES[operation],
                "bytes": len(artifact_bytes),
                "sha256": digest(artifact_bytes),
                "instructionCount": len(zkir["instructions"]),
                "distinctOpcodeCount": len(counts),
            },
            "opcodeHistogram": counts,
        })

    return {
        "schemaVersion": 1,
        "kind": "foundation-pilot-opcode-matrix-join",
        "status": "joined",
        "profile": PROFILE_NAME,
        "targetProfile": target,
        "scope": foundation["scope"],
        "evidenceSources": {
            "foundationReportSha256": digest(foundation_bytes),
            **matrix_pins,
        },
        "operations": operations,
        "openRequirements": gaps,
        "interpretation": (
            "Raw ZKIR hashes and opcode counts describe these exact Foundation pilot artifacts. "
            "Matrix row IDs, evidence IDs, and workload-stage flags are copied from prior workload "
            "observations. They do not claim keygen, checker, proof, or ledger execution for this pilot."
        ),
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--foundation", type=Path, required=True)
    parser.add_argument("--private-claim-artifacts", type=Path, required=True)
    parser.add_argument("--bounded-scalars-artifacts", type=Path, required=True)
    args = parser.parse_args(argv)
    directories = {
        "PrivateClaim.claim": args.private_claim_artifacts,
        "BoundedScalars.apply": args.bounded_scalars_artifacts,
    }
    try:
        result = build_evidence(args.foundation.read_bytes(), directories)
    except (OSError, ValueError) as error:
        print(f"foundation opcode matrix check: {error}", file=sys.stderr)
        return 1
    print(json.dumps(result, ensure_ascii=True, sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
