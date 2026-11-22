#!/usr/bin/env python3
"""Validate retained native workload counts and pinned historical fixtures.

This offline inventory check does not execute the native checker, keygen,
prover, or ledger. It verifies the retained records, fixture bytes, citations,
and 62 matrix-row annotations without promoting historical evidence.
"""
from __future__ import annotations

from collections import Counter
import hashlib
import json
from pathlib import Path
import sys
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
MATRIX_PATH = ROOT / "docs/compatibility/zkir-feature-matrix.json"
PROFILE_PATH = ROOT / "profiles/midnight-ledger-9-zkir-3.2.1-target.json"
HISTORY_PATH = ROOT / "tests/zkir321/qualification-evidence.json"
PROFILE_SHA256 = "02b4242c2561232daea1d7d1d29bde68f3157eb9eed8cfb037254a0013f40093"
HISTORY_SHA256 = "80ab92eb45777b6c0c6880d7b908bc4e6c3b82c11459f2d237b3bc6c36716293"
ZKIR_REVISION = "7a51b3385bbf4bce3604df87a7c70867c9ab43c0"
BOOLEAN_ZKIR = "../../tests/zkir321/boolean-deserialization-contract.zkir"
BOOLEAN_ZKIR_SHA256 = "f0a86633c404f306ce66f04f165c636cf8af2928d31dd856fc93293ec288b299"
BOOLEAN_CASES = "../../tests/zkir321/boolean-cases.json"
BOOLEAN_CASES_SHA256 = "570cf6414fffa3605a74274927f5763825f1d79452ddf763e04eadd4e679bbed"
JUBJUB_ZKIR = "../../tests/zkir321/jubjub-intermediate.zkir"
JUBJUB_ZKIR_SHA256 = "c5ab67161a1e98f9839079992c233e851264018c26f815b0a02c0a22ea216c19"
COPY_ZKIR = "../../runtime/tests/fixtures/native-copy/321/NativeCopy.store.zkir"
COPY_ZKIR_SHA256 = "d0ac701d3e5c4c1d25f9a2250a952f617ddc6edcd0e639ad3d881e8bdc76a5ff"
COPY_IMPACT = "../../runtime/tests/fixtures/native-copy/321/NativeCopy.store.impact.json"
COPY_IMPACT_SHA256 = "b89a7ab4cdc7a39bad7dee5545f9e651061c13fbcae86251aa15b8f3a17fbbf5"
COPY_TEST = "../../runtime/tests/native_copy.rs"
INSTRUCTION_COUNT = 47
VALUE_TYPE_COUNT = 15
STAGES = ("keygen", "checker", "proof", "ledger")
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


def require(condition: bool, code: str) -> None:
    if not condition:
        raise ValueError(code)


def sha256(contents: bytes) -> str:
    return hashlib.sha256(contents).hexdigest()


def strict_json(contents: bytes, subject: str) -> Any:
    def pairs_without_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"duplicate_json_key: {subject}.{key}")
            result[key] = value
        return result

    def reject_constant(value: str) -> None:
        raise ValueError(f"invalid_json_constant: {subject}.{value}")

    try:
        return json.loads(contents, object_pairs_hook=pairs_without_duplicates,
                          parse_constant=reject_constant)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ValueError(f"invalid_json: {subject}") from error


def strict_object(contents: bytes, subject: str) -> dict[str, Any]:
    value = strict_json(contents, subject)
    require(isinstance(value, dict), f"invalid_json_object: {subject}")
    return value


def pinned_json(path: Path, expected_sha: str, subject: str) -> tuple[bytes, dict[str, Any]]:
    contents = path.read_bytes()
    require(sha256(contents) == expected_sha, f"{subject}_digest_mismatch")
    return contents, strict_object(contents, subject)


def evidence_file(root: Path, relative: str, expected_sha: str, subject: str,
                  overrides: dict[str, bytes] | None = None) -> bytes:
    if overrides is not None and relative in overrides:
        contents = overrides[relative]
    else:
        unresolved = root / "docs/compatibility" / relative
        require(not unresolved.is_symlink(), f"evidence_file_symlink: {subject}")
        path = unresolved.resolve()
        try:
            path.relative_to(root.resolve())
        except ValueError as error:
            raise ValueError(f"evidence_path_escapes_repository: {subject}") from error
        require(path.is_file() and not path.is_symlink(), f"evidence_file_missing: {subject}")
        contents = path.read_bytes()
    require(sha256(contents) == expected_sha, f"{subject}_digest_mismatch")
    return contents


def validate_profile(profile: dict[str, Any], matrix: dict[str, Any], history: dict[str, Any]) -> dict[str, Any]:
    native = profile.get("nativeSource")
    require(isinstance(native, dict)
            and profile.get("name") == "midnight-ledger-9-zkir-3.2.1"
            and profile.get("ledger") == "9.1.0.1"
            and profile.get("zkir") == "3.2.1"
            and native.get("revision") == ZKIR_REVISION,
            "pinned_profile_identity_mismatch")
    target = matrix.get("target")
    require(isinstance(target, dict)
            and target.get("zkirRelease") == profile["zkir"]
            and target.get("zkirRevision") == ZKIR_REVISION
            and target.get("ledgerRelease") == profile["ledger"],
            "matrix_target_profile_mismatch")
    build = history.get("build")
    official = history.get("officialChecker")
    require(isinstance(build, dict) and isinstance(official, dict)
            and build.get("revision") == ZKIR_REVISION
            and build.get("requestedVersion") == "3.2.1"
            and build.get("releaseLabel") == "3.2.1"
            and official.get("version") == "3.2.1",
            "historical_profile_mismatch")
    return {
        "name": profile["name"],
        "ledger": profile["ledger"],
        "zkir": profile["zkir"],
        "zkirRevision": ZKIR_REVISION,
        "profileSha256": PROFILE_SHA256,
        "historicalRecordSha256": HISTORY_SHA256,
    }


def validate_citations(matrix: dict[str, Any], root: Path) -> dict[str, list[str]]:
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
            unresolved = root / "docs/compatibility" / ref
            require(not unresolved.is_symlink(), f"evidence_citation_symlink: {evidence_id}:{ref}")
            path = unresolved.resolve()
            try:
                path.relative_to(root.resolve())
            except ValueError as error:
                raise ValueError(f"evidence_path_escapes_repository: {evidence_id}:{ref}") from error
            require(path.is_file() and not path.is_symlink(),
                    f"evidence_citation_unresolved: {evidence_id}:{ref}")
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
    seen_opcodes: set[str] = set()
    for entry in entries:
        require(isinstance(entry, dict), "matrix_entry_malformed")
        row_id = entry.get("id")
        require(isinstance(row_id, str) and row_id not in seen_rows,
                f"duplicate_or_invalid_matrix_row_id: {row_id}")
        seen_rows.add(row_id)
        kind = entry.get("kind")
        require(kind in ("instruction", "value-type"), f"matrix_entry_kind_invalid: {row_id}")
        if kind == "instruction":
            opcode = entry.get("jsonOpcode")
            require(isinstance(opcode, str) and opcode not in seen_opcodes,
                    f"duplicate_or_invalid_matrix_opcode: {opcode}")
            seen_opcodes.add(opcode)
        safe_support = entry.get("safeLeanSourceSupport")
        require(isinstance(safe_support, dict) and safe_support.get("fullyVerified") is False,
                f"unsupported_source_qualification: {row_id}")

        evidence = entry.get("evidence")
        require(isinstance(evidence, dict), f"matrix_row_evidence_missing: {row_id}")
        evidence_ids = evidence.get("ids")
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
            require(type(evidence.get(key)) is bool and evidence[key] == expected_flags[stage],
                    f"matrix_row_stage_mismatch: {row_id}.{stage}")
        complete_key = "completeOverloadQualification" if kind == "instruction" else "completeTypeQualification"
        require(evidence.get(complete_key) is False,
                f"unsupported_complete_qualification: {row_id}")

    for evidence_id, rows in uses.items():
        if not rows:
            require(evidence_id == "E-UPSTREAM-TEST-DEFINITIONS",
                    f"orphan_evidence_record: {evidence_id}")
    return uses


def validate_copy_evidence(matrix: dict[str, Any], root: Path) -> dict[str, Any]:
    registry = matrix["evidenceRegister"]
    record = registry["E-NOCTIUM321-COPY"]
    require(record.get("zkirPin") == ZKIR_REVISION
            and record.get("keygen") is False and record.get("checker") is True
            and record.get("proof") is False and record.get("ledger") is False,
            "copy_checker_scope_mismatch")
    require(isinstance(record.get("scope"), str)
            and "Checker-only" in record["scope"]
            and "does not establish key generation, proof, ledger execution" in record["scope"],
            "copy_checker_scope_overstated")
    expected_observation = {
        "fixtureInstructionCount": 118,
        "copyOpcodeCount": 36,
        "acceptedChecks": 2,
        "rejectedChecks": 1,
    }
    require(record.get("checkerObservation") == expected_observation,
            "copy_checker_observation_count_mismatch")
    artifacts = record.get("artifacts")
    require(isinstance(artifacts, dict) and set(artifacts) == {"zkir", "impact"},
            "copy_artifact_record_missing")
    expected_artifacts = {
        "zkir": (COPY_ZKIR, COPY_ZKIR_SHA256),
        "impact": (COPY_IMPACT, COPY_IMPACT_SHA256),
    }
    contents: dict[str, bytes] = {}
    for role, (expected_path, expected_sha) in expected_artifacts.items():
        item = artifacts[role]
        require(isinstance(item, dict) and item.get("path") == expected_path
                and item.get("sha256") == expected_sha,
                f"copy_artifact_pin_mismatch: {role}")
        contents[role] = evidence_file(root, expected_path, expected_sha, f"copy_{role}")
        require(type(item.get("bytes")) is int and len(contents[role]) == item["bytes"],
                f"copy_artifact_length_mismatch: {role}")
    require(set(record.get("refs", [])) >= {
        expected_artifacts["zkir"][0], expected_artifacts["impact"][0],
        COPY_TEST, "../../runtime/Cargo.toml", "../../runtime/Cargo.lock",
    }, "copy_checker_citation_mismatch")

    zkir = strict_object(contents["zkir"], "copy_zkir")
    version = zkir.get("version")
    instructions = zkir.get("instructions")
    require(isinstance(version, dict) and version.get("major") == 3 and version.get("minor") == 2,
            "copy_zkir_version_mismatch")
    require(isinstance(instructions, list) and len(instructions) == expected_observation["fixtureInstructionCount"],
            "copy_fixture_instruction_count_mismatch")
    counts = Counter()
    for instruction in instructions:
        require(isinstance(instruction, dict) and isinstance(instruction.get("op"), str),
                "copy_fixture_instruction_malformed")
        counts[instruction["op"]] += 1
    require(counts["copy"] == expected_observation["copyOpcodeCount"],
            "copy_fixture_opcode_count_mismatch")
    impact = strict_object(contents["impact"], "copy_impact")
    require(impact.get("contractName") == "NativeCopy"
            and impact.get("entrypoint") == "store"
            and impact.get("nativeCircuitFile") == "NativeCopy.store.zkir",
            "copy_impact_operation_mismatch")
    _profile_bytes, profile = pinned_json(root / "profiles/midnight-ledger-9-zkir-3.2.1-target.json",
                                          PROFILE_SHA256, "target_profile")
    require(impact.get("target") == profile.get("name")
            and impact.get("targetProfile") == profile,
            "copy_impact_profile_mismatch")
    cargo_toml = (root / "runtime/Cargo.toml").read_text()
    cargo_lock = (root / "runtime/Cargo.lock").read_text()
    zkir_dependency = next((line for line in cargo_toml.splitlines()
                            if line.startswith("zkir-321 = { package = \"midnight-zkir\"")), "")
    require(ZKIR_REVISION in zkir_dependency
            and f"git+https://github.com/midnightntwrk/midnight-zkir?rev={ZKIR_REVISION}#{ZKIR_REVISION}" in cargo_lock,
            "copy_runtime_profile_mismatch")
    copy_test_path = root / "runtime/tests/native_copy.rs"
    copy_test = copy_test_path.read_text()
    require("#![cfg(feature = \"zkir-321\")]" in copy_test
            and "NativeCopy.store.impact.json" in copy_test
            and "NativeCopy.store.zkir" in copy_test
            and copy_test.count("for enabled in [true, false] {") == 1
            and copy_test.count("check(&result, &ir).unwrap();") == 1
            and copy_test.count('check(&execute(true, "8"), &ir).is_err()') == 1,
            "copy_checker_test_scope_mismatch")
    copy_row = next((row for row in matrix["entries"] if row.get("id") == "ZKIR-OP-COPY"), None)
    require(isinstance(copy_row, dict)
            and copy_row.get("evidence", {}).get("ids") == ["E-NOCTIUM321-COPY"]
            and copy_row["evidence"].get("checkerWorkloadObserved") is True,
            "copy_matrix_checker_link_mismatch")
    return {
        "fixtureSha256": COPY_ZKIR_SHA256,
        "fixtureInstructionCount": len(instructions),
        "copyOpcodeCount": counts["copy"],
        "acceptedChecks": expected_observation["acceptedChecks"],
        "rejectedChecks": expected_observation["rejectedChecks"],
        "stages": {stage: record[stage] for stage in STAGES},
    }


def validate_historical_fixtures(matrix: dict[str, Any], history: dict[str, Any],
                                 root: Path, fixture_overrides: dict[str, bytes] | None = None) -> dict[str, Any]:
    registry = matrix["evidenceRegister"]
    regressions = history.get("regressions")
    require(isinstance(regressions, dict), "historical_regressions_missing")
    boolean_history = regressions.get("booleanDeserialization")
    jubjub_history = regressions.get("jubjub")
    require(isinstance(boolean_history, dict) and isinstance(jubjub_history, dict),
            "historical_fixture_record_missing")
    require(boolean_history.get("fixture") == Path(BOOLEAN_ZKIR).name
            and boolean_history.get("fixtureSha256") == BOOLEAN_ZKIR_SHA256
            and boolean_history.get("cases") == Path(BOOLEAN_CASES).name
            and jubjub_history.get("fixture") == Path(JUBJUB_ZKIR).name
            and jubjub_history.get("fixtureSha256") == JUBJUB_ZKIR_SHA256,
            "historical_fixture_record_mismatch")

    boolean_bytes = evidence_file(root, BOOLEAN_ZKIR, BOOLEAN_ZKIR_SHA256,
                                  "boolean_zkir", fixture_overrides)
    case_bytes = evidence_file(root, BOOLEAN_CASES, BOOLEAN_CASES_SHA256,
                               "boolean_cases", fixture_overrides)
    jubjub_bytes = evidence_file(root, JUBJUB_ZKIR, JUBJUB_ZKIR_SHA256,
                                 "jubjub_zkir", fixture_overrides)
    bool_record = registry["E-RAW321-BOOL"]
    jubjub_record = registry["E-RAW321-JUBJUB"]
    history_ref = "../../tests/zkir321/qualification-evidence.json"
    require(set(bool_record.get("refs", [])) >= {BOOLEAN_ZKIR, BOOLEAN_CASES, history_ref}
            and set(jubjub_record.get("refs", [])) >= {JUBJUB_ZKIR, history_ref},
            "historical_fixture_citation_mismatch")
    bool_zkir = strict_object(boolean_bytes, "boolean_zkir")
    jubjub_zkir = strict_object(jubjub_bytes, "jubjub_zkir")
    for name, zkir in (("boolean", bool_zkir), ("jubjub", jubjub_zkir)):
        version = zkir.get("version")
        require(isinstance(version, dict) and version.get("major") == 3 and version.get("minor") == 2,
                f"{name}_fixture_version_mismatch")

    def fixture_opcodes(zkir: dict[str, Any], subject: str) -> set[str]:
        instructions = zkir.get("instructions")
        require(isinstance(instructions, list), f"{subject}_fixture_instructions_missing")
        result = set()
        for instruction in instructions:
            require(isinstance(instruction, dict) and isinstance(instruction.get("op"), str),
                    f"{subject}_fixture_instruction_malformed")
            result.add(instruction["op"])
        return result

    bool_opcodes = fixture_opcodes(bool_zkir, "boolean")
    jubjub_opcodes = fixture_opcodes(jubjub_zkir, "jubjub")
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
    require(accepted == 4 and rejected == 6 and len(bool_cases) == 10
            and boolean_history.get("positiveCases") == accepted
            and boolean_history.get("negativeCases") == rejected,
            "boolean_case_count_mismatch")
    require(bool_record.get("proof") is False and bool_record.get("ledger") is False
            and boolean_history.get("official321CheckerPassed") is True
            and boolean_history.get("sourceFrontendSupported") is False,
            "boolean_fixture_qualification_promoted")

    require(jubjub_history.get("old320KeygenExit") == 101
            and jubjub_history.get("new321KeygenExit") == 0
            and jubjub_history.get("official321CheckerAccepted") is True
            and jubjub_history.get("ledgerAcceptance") is False
            and jubjub_history.get("sourceFrontendSupported") is False
            and jubjub_record.get("proof") is True
            and jubjub_record.get("ledger") is False,
            "jubjub_fixture_qualification_promoted")

    return {
        "boolean": {
            "fixtureSha256": BOOLEAN_ZKIR_SHA256,
            "caseFileSha256": BOOLEAN_CASES_SHA256,
            "opcodes": sorted(bool_opcodes),
            "positiveCases": accepted,
            "negativeCases": rejected,
            "proof": False,
            "ledger": False,
            "sourceFrontendSupported": False,
        },
        "jubjub": {
            "fixtureSha256": JUBJUB_ZKIR_SHA256,
            "opcodes": sorted(jubjub_opcodes),
            "proof": True,
            "ledger": False,
            "sourceFrontendSupported": False,
            "old320KeygenExit": 101,
            "new321KeygenExit": 0,
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


def validate_matrix(matrix: dict[str, Any], root: Path = ROOT) -> dict[str, Any]:
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
    copy_observation = validate_copy_evidence(matrix, root)
    return {
        "sourceEntityRows": len(entries),
        "instructionVariants": INSTRUCTION_COUNT,
        "valueTypeVariants": VALUE_TYPE_COUNT,
        "globalSourceOnlyNotes": [evidence_id for evidence_id, rows in evidence_uses.items() if not rows],
        "workloadEvidence": computed_workloads,
        "copyObservation": copy_observation,
    }


def build_report(root: Path = ROOT, fixture_overrides: dict[str, bytes] | None = None) -> dict[str, Any]:
    _, profile = pinned_json(root / "profiles/midnight-ledger-9-zkir-3.2.1-target.json",
                             PROFILE_SHA256, "target_profile")
    history_bytes, history = pinned_json(root / "tests/zkir321/qualification-evidence.json",
                                         HISTORY_SHA256, "historical_qualification_record")
    matrix_bytes = (root / "docs/compatibility/zkir-feature-matrix.json").read_bytes()
    matrix = strict_object(matrix_bytes, "native_feature_matrix")
    profile_summary = validate_profile(profile, matrix, history)
    matrix_summary = validate_matrix(matrix, root)
    fixture_summary = validate_historical_fixtures(matrix, history, root, fixture_overrides)
    validate_historical_scope(history)
    return {
        "schemaVersion": 1,
        "kind": "retained-native-workload-evidence-check",
        "status": "passed",
        "targetProfile": profile_summary,
        "matrixSha256": sha256(matrix_bytes),
        "historicalRecordSha256": sha256(history_bytes),
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
