#!/usr/bin/env python3
"""Validate retained native workload counts and pinned historical fixtures.

This offline inventory check does not execute the native checker, keygen,
prover, or ledger. It verifies the retained records, fixture bytes, citations,
and 62 matrix-row annotations without promoting historical evidence.
"""
from __future__ import annotations

from collections import Counter
import json
from pathlib import Path
import runpy
import sys
from typing import Any

FOUNDATION = runpy.run_path(str(Path(__file__).resolve().with_name("check-foundation-opcode-matrix.py")))
ROOT = FOUNDATION["ROOT"]
MATRIX_PATH = FOUNDATION["MATRIX_PATH"]
PROFILE_PATH = FOUNDATION["PROFILE_PATH"]
HISTORY_PATH = FOUNDATION["HISTORY_PATH"]
PROFILE_SHA256 = FOUNDATION["PROFILE_SHA256"]
HISTORY_SHA256 = FOUNDATION["HISTORY_SHA256"]
require = FOUNDATION["require"]
digest = FOUNDATION["digest"]
strict_json = FOUNDATION["strict_json"]
strict_object = FOUNDATION["strict_json_object"]
pinned_json = FOUNDATION["load_pinned"]
target_identity = FOUNDATION["target_identity"]
matrix_target = FOUNDATION["validate_matrix_target"]
instruction_rows = FOUNDATION["matrix_opcode_rows"]
INSTRUCTION_COUNT = 47
VALUE_TYPE_COUNT = 15
STAGES = ("keygen", "checker", "proof", "ledger")


def compatibility_reference(path: Path) -> str:
    return (Path("..") / ".." / path.relative_to(ROOT)).as_posix()


HISTORICAL_DIR = compatibility_reference(HISTORY_PATH.parent) + "/"
COPY_FIXTURE_DIR = compatibility_reference(ROOT / "runtime/tests/fixtures/native-copy/321") + "/"
COPY_TEST = compatibility_reference(ROOT / "runtime/tests/native_copy.rs")
COPY_CARGO_TOML = compatibility_reference(ROOT / "runtime/Cargo.toml")
COPY_CARGO_LOCK = compatibility_reference(ROOT / "runtime/Cargo.lock")
EXPECTED_REGISTRY_IDS = {
    "E-NOCTIUM321-COPY",
    "E-NATIVE321-CLAIM",
    "E-RAW321-BOOL",
    "E-RAW321-JUBJUB",
    "E-LOCAL-SOURCE",
    "E-UPSTREAM-TEST-DEFINITIONS",
}
EVIDENCE_STAGES = {
    "E-NOCTIUM321-COPY": {"keygen": False, "checker": True, "proof": False, "ledger": False},
    "E-NATIVE321-CLAIM": {"keygen": True, "checker": True, "proof": True, "ledger": True},
    "E-RAW321-BOOL": {"keygen": True, "checker": True, "proof": False, "ledger": False},
    "E-RAW321-JUBJUB": {"keygen": True, "checker": True, "proof": True, "ledger": False},
    "E-LOCAL-SOURCE": {"keygen": False, "checker": False, "proof": False, "ledger": False},
    "E-UPSTREAM-TEST-DEFINITIONS": {"keygen": False, "checker": False, "proof": False, "ledger": False},
}


def evidence_file(root: Path, relative: str, expected_sha: str | None, subject: str,
                  overrides: dict[str, bytes] | None = None) -> bytes:
    if overrides is not None and relative in overrides:
        contents = overrides[relative]
    else:
        contents = compatibility_file_path(root, relative, subject).read_bytes()
    if expected_sha is not None:
        require(digest(contents) == expected_sha, f"{subject}_digest_mismatch")
    return contents


def compatibility_file_path(root: Path, relative: str, subject: str,
                            citation: bool = False) -> Path:
    unresolved = root / "docs/compatibility" / relative
    prefix = "evidence_citation" if citation else "evidence_file"
    require(not unresolved.is_symlink(), f"{prefix}_symlink: {subject}")
    path = unresolved.resolve()
    try:
        path.relative_to(root.resolve())
    except ValueError as error:
        raise ValueError(f"evidence_path_escapes_repository: {subject}") from error
    missing_code = "evidence_citation_unresolved" if citation else "evidence_file_missing"
    require(path.is_file() and not path.is_symlink(), f"{missing_code}: {subject}")
    return path


def fixture_opcode_counts(zkir: dict[str, Any], subject: str) -> Counter[str]:
    instructions = zkir.get("instructions")
    require(isinstance(instructions, list), f"{subject}_fixture_instructions_missing")
    result: Counter[str] = Counter()
    for instruction in instructions:
        require(isinstance(instruction, dict) and isinstance(instruction.get("op"), str),
                f"{subject}_fixture_instruction_malformed")
        result[instruction["op"]] += 1
    return result


def validate_profile(profile: dict[str, Any], matrix: dict[str, Any], history: dict[str, Any]) -> dict[str, Any]:
    identity = target_identity(profile)
    revision = profile["nativeSource"]["revision"]
    matrix_target(matrix, profile)
    build = history.get("build")
    official = history.get("officialChecker")
    require(isinstance(build, dict) and isinstance(official, dict)
            and build.get("revision") == revision
            and build.get("requestedVersion") == "3.2.1"
            and build.get("releaseLabel") == "3.2.1"
            and official.get("version") == "3.2.1",
            "historical_profile_mismatch")
    return {
        "name": identity["name"],
        "ledger": identity["ledger"],
        "zkir": identity["zkir"],
        "zkirRevision": revision,
        "profileSha256": identity["sha256"],
        "historicalRecordSha256": HISTORY_SHA256,
    }


def validate_citations(matrix: dict[str, Any], root: Path) -> dict[str, list[str]]:
    instruction_rows(matrix)
    registry = matrix.get("evidenceRegister")
    require(isinstance(registry, dict), "evidence_registry_missing")
    require(set(registry) == EXPECTED_REGISTRY_IDS, "evidence_registry_id_set_mismatch")
    source_ids = matrix.get("sources")
    require(isinstance(source_ids, dict), "matrix_sources_missing")
    uses: dict[str, list[str]] = {evidence_id: [] for evidence_id in registry}

    for evidence_id, record in registry.items():
        require(isinstance(record, dict), f"evidence_record_malformed: {evidence_id}")
        refs = record.get("refs", [])
        sources = record.get("sources", [])
        require(isinstance(refs, list) and all(isinstance(ref, str) and ref for ref in refs),
                f"evidence_refs_malformed: {evidence_id}")
        require(isinstance(sources, list) and all(isinstance(source, str) for source in sources),
                f"evidence_sources_malformed: {evidence_id}")
        require(refs or sources, f"evidence_citations_missing: {evidence_id}")
        require(len(set(refs)) == len(refs), f"duplicate_evidence_citation: {evidence_id}")
        require(all(source in source_ids for source in sources),
                f"unresolved_evidence_source: {evidence_id}")
        for ref in refs:
            compatibility_file_path(root, ref, f"{evidence_id}:{ref}", citation=True)
        flags = EVIDENCE_STAGES[evidence_id]
        if evidence_id in ("E-LOCAL-SOURCE", "E-UPSTREAM-TEST-DEFINITIONS"):
            require(record.get("kind") in ("source-and-test-definition-inspection-only", "source-inspection-only"),
                    f"source_evidence_promoted: {evidence_id}")
            require(not any(stage in record for stage in STAGES),
                    f"source_evidence_has_workload_stage: {evidence_id}")
        else:
            require(record.get("kind") in (
                "executed-workload", "executed-raw-fixture", "executed-native-checker-test"),
                f"execution_evidence_kind_invalid: {evidence_id}")
            for stage in STAGES:
                require(type(record.get(stage)) is bool and record[stage] == flags[stage],
                        f"evidence_stage_mismatch: {evidence_id}.{stage}")

    entries = matrix.get("entries")
    require(isinstance(entries, list), "matrix_entries_missing")
    seen_rows: set[str] = set()
    for entry in entries:
        require(isinstance(entry, dict), "matrix_entry_malformed")
        row_id = entry.get("id")
        require(isinstance(row_id, str) and row_id not in seen_rows,
                f"duplicate_or_invalid_matrix_row_id: {row_id}")
        seen_rows.add(row_id)
        kind = entry.get("kind")
        require(kind in ("instruction", "value-type"), f"matrix_entry_kind_invalid: {row_id}")
        safe_support = entry.get("safeLeanSourceSupport")
        require(isinstance(safe_support, dict) and safe_support.get("fullyVerified") is False,
                f"unsupported_source_qualification: {row_id}")

        evidence = entry.get("evidence")
        require(isinstance(evidence, dict), f"matrix_row_evidence_missing: {row_id}")
        evidence_ids = evidence.get("ids")
        if kind == "value-type":
            require(isinstance(evidence_ids, list)
                    and all(isinstance(evidence_id, str) for evidence_id in evidence_ids),
                    f"matrix_row_evidence_ids_malformed: {row_id}")
            require(len(set(evidence_ids)) == len(evidence_ids),
                    f"duplicate_matrix_evidence_link: {row_id}")
        expected_flags = {stage: False for stage in STAGES}
        for evidence_id in evidence_ids:
            require(evidence_id in registry, f"orphan_matrix_evidence_link: {row_id}:{evidence_id}")
            uses[evidence_id].append(row_id)
            for stage in STAGES:
                expected_flags[stage] |= EVIDENCE_STAGES[evidence_id][stage]
        for stage in STAGES:
            key = stage + "WorkloadObserved"
            if kind == "value-type":
                require(type(evidence.get(key)) is bool,
                        f"matrix_row_stage_malformed: {row_id}.{stage}")
            require(evidence[key] == expected_flags[stage], f"matrix_row_stage_mismatch: {row_id}.{stage}")
        complete_key = "completeOverloadQualification" if kind == "instruction" else "completeTypeQualification"
        require(evidence.get(complete_key) is False,
                f"unsupported_complete_qualification: {row_id}")

    for evidence_id, rows in uses.items():
        if not rows:
            require(evidence_id == "E-UPSTREAM-TEST-DEFINITIONS",
                    f"orphan_evidence_record: {evidence_id}")
    return uses


def validate_copy_evidence(matrix: dict[str, Any], root: Path, profile: dict[str, Any]) -> dict[str, Any]:
    registry = matrix["evidenceRegister"]
    record = registry["E-NOCTIUM321-COPY"]
    revision = profile["nativeSource"]["revision"]
    require(record.get("zkirPin") == revision
            and record.get("keygen") is False and record.get("checker") is True
            and record.get("proof") is False and record.get("ledger") is False,
            "copy_checker_scope_mismatch")
    require(isinstance(record.get("scope"), str)
            and "Checker-only" in record["scope"]
            and "does not establish key generation, proof, ledger execution" in record["scope"],
            "copy_checker_scope_overstated")
    artifacts = record.get("artifacts")
    require(isinstance(artifacts, dict) and set(artifacts) == {"zkir", "impact"},
            "copy_artifact_record_missing")
    expected_names = {"zkir": "NativeCopy.store.zkir", "impact": "NativeCopy.store.impact.json"}
    contents: dict[str, bytes] = {}
    for role, filename in expected_names.items():
        item = artifacts[role]
        expected_path = COPY_FIXTURE_DIR + filename
        require(isinstance(item, dict) and item.get("path") == expected_path
                and isinstance(item.get("sha256"), str) and len(item["sha256"]) == 64
                and all(char in "0123456789abcdef" for char in item["sha256"]),
                f"copy_artifact_pin_mismatch: {role}")
        contents[role] = evidence_file(root, expected_path, item["sha256"], f"copy_{role}")
        require(type(item.get("bytes")) is int and len(contents[role]) == item["bytes"],
                f"copy_artifact_length_mismatch: {role}")
    require(set(record.get("refs", [])) >= {
        *(COPY_FIXTURE_DIR + filename for filename in expected_names.values()),
        COPY_TEST, COPY_CARGO_TOML, COPY_CARGO_LOCK,
    }, "copy_checker_citation_mismatch")

    zkir = strict_object(contents["zkir"], "copy_zkir")
    version = zkir.get("version")
    require(isinstance(version, dict) and version.get("major") == 3 and version.get("minor") == 2,
            "copy_zkir_version_mismatch")
    copy_opcode_counts = fixture_opcode_counts(zkir, "copy")
    instructions = zkir["instructions"]
    copy_count = copy_opcode_counts["copy"]
    impact = strict_object(contents["impact"], "copy_impact")
    require(impact.get("contractName") == "NativeCopy"
            and impact.get("entrypoint") == "store"
            and impact.get("nativeCircuitFile") == "NativeCopy.store.zkir",
            "copy_impact_operation_mismatch")
    require(impact.get("target") == profile.get("name")
            and impact.get("targetProfile") == profile,
            "copy_impact_profile_mismatch")
    cargo_toml = (root / "docs/compatibility" / COPY_CARGO_TOML).read_text()
    cargo_lock = (root / "docs/compatibility" / COPY_CARGO_LOCK).read_text()
    zkir_dependency = next((line for line in cargo_toml.splitlines()
                            if line.startswith("zkir-321 = { package = \"midnight-zkir\"")), "")
    require(revision in zkir_dependency
            and f"git+https://github.com/midnightntwrk/midnight-zkir?rev={revision}#{revision}" in cargo_lock,
            "copy_runtime_profile_mismatch")
    copy_test_path = root / "docs/compatibility" / COPY_TEST
    copy_test = copy_test_path.read_text()
    require("#![cfg(feature = \"zkir-321\")]" in copy_test
            and "NativeCopy.store.impact.json" in copy_test
            and "NativeCopy.store.zkir" in copy_test
            and copy_test.count("for enabled in [true, false] {") == 1
            and copy_test.count("check(&result, &ir).unwrap();") == 1
            and copy_test.count('check(&execute(true, "8"), &ir).is_err()') == 1,
            "copy_checker_test_scope_mismatch")
    accepted_loop = copy_test.split("for enabled in [", 1)[1].split("]", 1)[0].split(",")
    observation = {
        "fixtureInstructionCount": len(instructions),
        "copyOpcodeCount": copy_count,
        "acceptedChecks": len(accepted_loop),
        "rejectedChecks": copy_test.count('check(&execute(true, "8"), &ir).is_err()'),
    }
    require(record.get("checkerObservation") == observation,
            "copy_checker_observation_count_mismatch")
    copy_row = next((row for row in matrix["entries"] if row.get("id") == "ZKIR-OP-COPY"), None)
    require(isinstance(copy_row, dict)
            and copy_row.get("evidence", {}).get("ids") == ["E-NOCTIUM321-COPY"]
            and copy_row["evidence"].get("checkerWorkloadObserved") is True,
            "copy_matrix_checker_link_mismatch")
    return {
        "fixtureSha256": artifacts["zkir"]["sha256"],
        "fixtureInstructionCount": len(instructions),
        "copyOpcodeCount": copy_count,
        "acceptedChecks": observation["acceptedChecks"],
        "rejectedChecks": observation["rejectedChecks"],
        "stages": {stage: record[stage] for stage in STAGES},
    }


def historical_fixture_paths(history: dict[str, Any]) -> dict[str, str]:
    regressions = history.get("regressions")
    require(isinstance(regressions, dict), "historical_regressions_missing")
    boolean_history = regressions.get("booleanDeserialization")
    jubjub_history = regressions.get("jubjub")
    require(isinstance(boolean_history, dict) and isinstance(jubjub_history, dict),
            "historical_fixture_record_missing")
    names = {
        "booleanZkir": boolean_history.get("fixture"),
        "booleanCases": boolean_history.get("cases"),
        "jubjubZkir": jubjub_history.get("fixture"),
    }
    require(all(isinstance(name, str) and Path(name).name == name for name in names.values()),
            "historical_fixture_record_mismatch")
    return {key: HISTORICAL_DIR + name for key, name in names.items()}


def validate_historical_fixtures(matrix: dict[str, Any], history: dict[str, Any],
                                 root: Path, fixture_overrides: dict[str, bytes] | None = None) -> dict[str, Any]:
    registry = matrix["evidenceRegister"]
    regressions = history["regressions"]
    boolean_history = regressions["booleanDeserialization"]
    jubjub_history = regressions["jubjub"]
    paths = historical_fixture_paths(history)
    history_ref = HISTORICAL_DIR + HISTORY_PATH.name
    boolean_sha = boolean_history.get("fixtureSha256")
    jubjub_sha = jubjub_history.get("fixtureSha256")
    require(isinstance(boolean_sha, str) and isinstance(jubjub_sha, str),
            "historical_fixture_digest_missing")

    boolean_bytes = evidence_file(root, paths["booleanZkir"], boolean_sha,
                                  "boolean_zkir", fixture_overrides)
    case_bytes = evidence_file(root, paths["booleanCases"], None,
                               "boolean_cases", fixture_overrides)
    jubjub_bytes = evidence_file(root, paths["jubjubZkir"], jubjub_sha,
                                 "jubjub_zkir", fixture_overrides)
    bool_record = registry["E-RAW321-BOOL"]
    jubjub_record = registry["E-RAW321-JUBJUB"]
    require(set(bool_record.get("refs", [])) >= {paths["booleanZkir"], paths["booleanCases"], history_ref}
            and set(jubjub_record.get("refs", [])) >= {paths["jubjubZkir"], history_ref},
            "historical_fixture_citation_mismatch")
    bool_zkir = strict_object(boolean_bytes, "boolean_zkir")
    jubjub_zkir = strict_object(jubjub_bytes, "jubjub_zkir")
    for name, zkir in (("boolean", bool_zkir), ("jubjub", jubjub_zkir)):
        version = zkir.get("version")
        require(isinstance(version, dict) and version.get("major") == 3 and version.get("minor") == 2,
                f"{name}_fixture_version_mismatch")

    bool_opcodes = set(fixture_opcode_counts(bool_zkir, "boolean"))
    jubjub_opcodes = set(fixture_opcode_counts(jubjub_zkir, "jubjub"))
    for name, record, opcodes in (("boolean", bool_record, bool_opcodes), ("jubjub", jubjub_record, jubjub_opcodes)):
        listed = record.get("opcodes")
        require(isinstance(listed, list) and all(isinstance(op, str) for op in listed)
                and len(set(listed)) == len(listed) and set(listed) == opcodes,
                f"{name}_fixture_opcode_coverage_mismatch")
        require(record.get("kind") == "executed-raw-fixture",
                f"{name}_fixture_evidence_kind_mismatch")
        require(record.get("keygen") is True and record.get("checker") is True,
                f"{name}_fixture_execution_evidence_missing")

    bool_cases = strict_json(case_bytes, "boolean_cases")
    require(isinstance(bool_cases, list), "boolean_cases_not_array")
    case_names: set[str] = set()
    accepted = 0
    rejected = 0
    for case in bool_cases:
        require(isinstance(case, dict) and isinstance(case.get("name"), str)
                and case.get("name") not in case_names and type(case.get("accepted")) is bool,
                "boolean_case_malformed_or_duplicate")
        case_names.add(case["name"])
        for field in ("byte", "flag"):
            value = case.get(field)
            require(isinstance(value, str) and value.isdecimal(),
                    f"boolean_case_{field}_invalid: {case['name']}")
        if case["accepted"]:
            require(isinstance(case.get("result"), str) and case["result"].isdecimal(),
                    f"boolean_case_result_missing: {case['name']}")
            accepted += 1
        else:
            rejected += 1
    require(accepted == boolean_history.get("positiveCases")
            and boolean_history.get("negativeCases") == rejected,
            "boolean_case_count_mismatch")
    require(bool_record.get("proof") is False and bool_record.get("ledger") is False
            and boolean_history.get("official321CheckerPassed") is True
            and boolean_history.get("sourceFrontendSupported") is False,
            "boolean_fixture_qualification_promoted")

    require(jubjub_history.get("new321KeygenExit") == 0
            and jubjub_history.get("official321CheckerAccepted") is True
            and type(jubjub_history.get("official321WasmProofBytes")) is int
            and jubjub_history["official321WasmProofBytes"] > 0
            and jubjub_history.get("ledgerAcceptance") is False
            and jubjub_history.get("sourceFrontendSupported") is False
            and jubjub_record.get("proof") is True
            and jubjub_record.get("ledger") is False,
            "jubjub_fixture_qualification_promoted")

    return {
        "boolean": {
            "fixtureSha256": boolean_sha,
            "opcodes": sorted(bool_opcodes),
            "positiveCases": accepted,
            "negativeCases": rejected,
            "proof": False,
            "ledger": False,
            "sourceFrontendSupported": False,
        },
        "jubjub": {
            "fixtureSha256": jubjub_sha,
            "opcodes": sorted(jubjub_opcodes),
            "proof": True,
            "ledger": False,
            "sourceFrontendSupported": False,
            "old320KeygenExit": jubjub_history.get("old320KeygenExit"),
            "new321KeygenExit": jubjub_history["new321KeygenExit"],
        },
    }


def workload_counts(entries: list[dict[str, Any]]) -> dict[str, dict[str, int]]:
    result = {stage: {"instructionVariants": 0, "valueTypeVariants": 0} for stage in STAGES}
    for entry in entries:
        category = "instructionVariants" if entry["kind"] == "instruction" else "valueTypeVariants"
        for stage in STAGES:
            if entry["evidence"][stage + "WorkloadObserved"]:
                result[stage][category] += 1
    return result


def validate_historical_scope(history: dict[str, Any]) -> None:
    scope = history.get("scope")
    require(history.get("historicalDisplayOnly") is True
            and history.get("currentSourceQualified") is False
            and isinstance(scope, dict)
            and scope.get("publicNetworkQualified") is False
            and scope.get("wholeLanguageQualified") is False
            and scope.get("compactCompilerOrRuntimeInvoked") is False,
            "historical_evidence_scope_promoted")


def validate_matrix(matrix: dict[str, Any], root: Path = ROOT,
                    profile: dict[str, Any] | None = None) -> dict[str, Any]:
    if profile is None:
        _, profile = pinned_json(root / PROFILE_PATH.relative_to(ROOT), PROFILE_SHA256, "target_profile")
    entries = matrix.get("entries")
    require(isinstance(entries, list) and len(entries) == 62, "matrix_source_entity_row_count_mismatch")
    kinds = Counter(entry.get("kind") for entry in entries if isinstance(entry, dict))
    require(kinds == Counter({"instruction": INSTRUCTION_COUNT, "value-type": VALUE_TYPE_COUNT}),
            "matrix_instruction_or_type_count_mismatch")
    counts = matrix.get("counts")
    require(isinstance(counts, dict)
            and counts.get("sourceEntityRows") == 62
            and counts.get("instructionVariants") == INSTRUCTION_COUNT
            and counts.get("valueTypeVariants") == VALUE_TYPE_COUNT,
            "matrix_inventory_count_mismatch")
    require(counts.get("fullyQualifiedSourceEntities") == 0,
            "matrix_source_qualification_promoted")
    evidence_uses = validate_citations(matrix, root)
    computed_workloads = workload_counts(entries)
    require(counts.get("workloadEvidence") == computed_workloads,
            "matrix_workload_counts_stale")
    copy_observation = validate_copy_evidence(matrix, root, profile)
    return {
        "sourceEntityRows": len(entries),
        "instructionVariants": INSTRUCTION_COUNT,
        "valueTypeVariants": VALUE_TYPE_COUNT,
        "globalSourceOnlyNotes": [evidence_id for evidence_id, rows in evidence_uses.items() if not rows],
        "workloadEvidence": computed_workloads,
        "copyObservation": copy_observation,
    }


def build_report(root: Path = ROOT, fixture_overrides: dict[str, bytes] | None = None) -> dict[str, Any]:
    _, profile = pinned_json(root / PROFILE_PATH.relative_to(ROOT), PROFILE_SHA256, "target_profile")
    history_bytes, history = pinned_json(root / HISTORY_PATH.relative_to(ROOT),
                                         HISTORY_SHA256, "historical_qualification_record")
    matrix_bytes = (root / MATRIX_PATH.relative_to(ROOT)).read_bytes()
    matrix = strict_object(matrix_bytes, "native_feature_matrix")
    profile_summary = validate_profile(profile, matrix, history)
    matrix_summary = validate_matrix(matrix, root, profile)
    fixture_summary = validate_historical_fixtures(matrix, history, root, fixture_overrides)
    validate_historical_scope(history)
    return {
        "schemaVersion": 1,
        "kind": "retained-native-workload-evidence-check",
        "status": "passed",
        "targetProfile": profile_summary,
        "matrixSha256": digest(matrix_bytes),
        "historicalRecordSha256": digest(history_bytes),
        "inventory": matrix_summary,
        "historicalFixtures": fixture_summary,
        "scope": (
            "Retained native inventory and historical fixture validation only. This check does not rerun "
            "keygen, checker, proof, or ledger, and does not qualify current source or full overloads."
        ),
    }


def main() -> int:
    try:
        report = build_report()
    except (OSError, ValueError) as error:
        print(f"native workload evidence: {error}", file=sys.stderr)
        return 1
    print(json.dumps(report, ensure_ascii=True, sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
