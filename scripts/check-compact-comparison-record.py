#!/usr/bin/env python3
"""Verify the retained Compact List-head comparison record offline."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_RECORD = ROOT / "tests/compact/list-head-comparison-v1/record.json"

INPUT_PATHS = (
    "docs/compatibility/compact-feature-matrix.json",
    "profiles/foundation-source-v1.json",
    "profiles/midnight-ledger-9-zkir-3.2.1-target.json",
    "lean-toolchain",
    "tests/NativeScalarListMaybe.lean",
    "tests/compact/ListHeadMaybe.compact",
    "tests/compact/list-head-maybe.mjs",
)
OUTPUT_PATHS = (
    "tests/compact/list-head-comparison-v1/compact.json",
    "tests/compact/list-head-comparison-v1/NativeScalarListMaybe.head.zkir",
)

EXPECTED_COMPACT = {
    "compiler": "0.36.1",
    "sourceCommit": "7fa3a117c5e7efe9d2c51da04263e5f0b3509144",
    "runtime": "0.21.0",
    "compilerArchiveSha256": "96ee68a59d9e8b093f05c97479a4cf08c79760015dcc26ecc797ec0160ca27f9",
    "compilerSha256": "15646793d3ff7f36cd81aa63419163e29d9893538bb4a6911a21012e8735b537",
}
EXPECTED_CASES = ["LIST-HEAD-UINT8-EMPTY", "LIST-HEAD-UINT8-POPULATED"]
EXPECTED_SCOPE = "root-uint8-list-head-source-compact-runtime-and-native-relation-emission"
SHA1 = re.compile(r"[0-9a-f]{40}\Z")
SHA256 = re.compile(r"[0-9a-f]{64}\Z")


class VerificationError(ValueError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise VerificationError(message)


def json_object(data: bytes, label: str) -> dict[str, Any]:
    try:
        value = json.loads(data.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise VerificationError(f"invalid JSON: {label}") from error
    require(isinstance(value, dict), f"invalid JSON object: {label}")
    return value


def read_json_file(path: Path, label: str) -> dict[str, Any]:
    try:
        data = path.read_bytes()
    except OSError as error:
        raise VerificationError(f"unable to read {label}: {path}") from error
    return json_object(data, label)


def historical_bytes(commit: str, path: str) -> bytes:
    result = subprocess.run(
        ["git", "--no-replace-objects", "show", f"{commit}:{path}"],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if result.returncode != 0:
        raise VerificationError(f"historical input missing or unavailable: {path}")
    return result.stdout


def validate_commit(commit: Any) -> str:
    require(isinstance(commit, str) and SHA1.fullmatch(commit) is not None,
            "noctiumCommit must be a full lowercase SHA1")
    result = subprocess.run(
        ["git", "rev-parse", "--verify", f"{commit}^{{commit}}"],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        check=False,
    )
    resolved = result.stdout.strip()
    require(result.returncode == 0 and resolved == commit,
            "noctiumCommit is not an available full commit")
    return commit


def verify_record_shape(record: dict[str, Any]) -> str:
    expected_keys = {
        "schemaVersion", "noctiumCommit", "feature", "cases", "scope",
        "compact", "inputs", "outputs",
    }
    require(set(record) == expected_keys, "record fields mismatch")
    require(type(record.get("schemaVersion")) is int and record["schemaVersion"] == 1,
            "schemaVersion mismatch")
    commit = validate_commit(record.get("noctiumCommit"))
    require(record.get("feature") == "C-ADT-LIST-HEAD", "feature mismatch")
    require(record.get("cases") == EXPECTED_CASES, "case IDs mismatch")
    require(record.get("scope") == EXPECTED_SCOPE, "scope mismatch")
    require(record.get("compact") == EXPECTED_COMPACT, "Compact release pin mismatch")

    for label, expected_paths in (("inputs", INPUT_PATHS), ("outputs", OUTPUT_PATHS)):
        values = record.get(label)
        require(isinstance(values, dict), f"{label} must be an object")
        require(set(values) == set(expected_paths), f"{label} paths mismatch")
        for path in expected_paths:
            digest = values[path]
            require(isinstance(digest, str) and SHA256.fullmatch(digest) is not None,
                    f"invalid {label} digest: {path}")
    return commit


def verify_historical_inputs(record: dict[str, Any], commit: str) -> dict[str, bytes]:
    historical: dict[str, bytes] = {}
    for path in INPUT_PATHS:
        data = historical_bytes(commit, path)
        historical[path] = data
        actual = hashlib.sha256(data).hexdigest()
        if record["inputs"][path] != actual:
            raise VerificationError(f"input digest mismatch: {path}")
    return historical


def verify_pinned_sources(historical: dict[str, bytes]) -> None:
    matrix = json_object(
        historical["docs/compatibility/compact-feature-matrix.json"],
        "historical Compact feature matrix",
    )
    baseline = matrix.get("baseline")
    require(isinstance(baseline, dict), "historical Compact release baseline missing")
    for key, expected in (
        ("featureToolchain", EXPECTED_COMPACT["compiler"]),
        ("compactRuntimeReferenceOnly", EXPECTED_COMPACT["runtime"]),
        ("sourceCommit", EXPECTED_COMPACT["sourceCommit"]),
        ("bundledZkir", "3.2.1"),
    ):
        require(baseline.get(key) == expected, f"historical Compact release pin mismatch: {key}")

    features = matrix.get("features")
    require(isinstance(features, list), "historical Compact feature list missing")
    feature = next((item for item in features
                    if isinstance(item, dict) and item.get("id") == "C-ADT-LIST-HEAD"), None)
    require(isinstance(feature, dict), "historical List.head feature missing")
    cases = feature.get("conformanceCases")
    require(isinstance(cases, list), "historical List.head cases missing")
    for case_id in EXPECTED_CASES:
        case = next((item for item in cases
                     if isinstance(item, dict) and item.get("id") == case_id), None)
        require(isinstance(case, dict), f"historical conformance case missing: {case_id}")
        oracle = case.get("oracle")
        require(isinstance(oracle, dict)
                and oracle.get("outcome") == "executed"
                and oracle.get("compiler") == EXPECTED_COMPACT["compiler"]
                and oracle.get("runtime") == EXPECTED_COMPACT["runtime"],
                f"historical conformance pin mismatch: {case_id}")

    foundation = json_object(
        historical["profiles/foundation-source-v1.json"],
        "historical foundation profile",
    )
    target_bytes = historical["profiles/midnight-ledger-9-zkir-3.2.1-target.json"]
    target = json_object(target_bytes, "historical target profile")
    target_pin = foundation.get("targetProfile")
    require(type(foundation.get("schemaVersion")) is int
            and foundation.get("schemaVersion") == 1
            and foundation.get("name") == "foundation-source-v1"
            and isinstance(target_pin, dict),
            "historical foundation target pin missing")
    target_digest = hashlib.sha256(target_bytes).hexdigest()
    require(target_pin.get("path") == "profiles/midnight-ledger-9-zkir-3.2.1-target.json"
            and target_pin.get("sha256") == target_digest
            and target_pin.get("name") == "midnight-ledger-9-zkir-3.2.1"
            and target_pin.get("ledger") == "9.1.0.1"
            and target_pin.get("zkir") == "3.2.1",
            "historical foundation target digest mismatch")
    native_source = target.get("nativeSource")
    require(type(target.get("schemaVersion")) is int
            and target.get("schemaVersion") == 1
            and target.get("name") == "midnight-ledger-9-zkir-3.2.1"
            and target.get("ledger") == "9.1.0.1"
            and target.get("zkir") == "3.2.1"
            and isinstance(native_source, dict)
            and native_source.get("revision") == "7a51b3385bbf4bce3604df87a7c70867c9ab43c0",
            "historical native target profile mismatch")


def verify_retained_outputs(record: dict[str, Any]) -> None:
    output_data: dict[str, bytes] = {}
    for path in OUTPUT_PATHS:
        artifact = ROOT / path
        require(artifact.resolve().is_relative_to(ROOT) and artifact.is_file(),
                f"missing retained output: {path}")
        data = artifact.read_bytes()
        output_data[path] = data
        actual = hashlib.sha256(data).hexdigest()
        require(record["outputs"][path] == actual, f"output digest mismatch: {path}")

    compact_path = OUTPUT_PATHS[0]
    compact_result = json_object(output_data[compact_path], compact_path)
    empty = compact_result.get("empty")
    populated = compact_result.get("oneElement")
    require(isinstance(empty, dict)
            and type(empty.get("is_some")) is bool
            and empty.get("is_some") is False
            and empty.get("value") == "0"
            and empty.get("encoding") == [[], []],
            "Compact empty List.head result mismatch")
    require(isinstance(populated, dict)
            and type(populated.get("is_some")) is bool
            and populated.get("is_some") is True
            and populated.get("value") == "37"
            and populated.get("encoding") == [[1], [37]],
            "Compact populated List.head result mismatch")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", type=Path, default=DEFAULT_RECORD,
                        help="record JSON path (default: tests/compact/list-head-comparison-v1/record.json)")
    args = parser.parse_args()

    try:
        record = read_json_file(args.record, "comparison record")
        commit = verify_record_shape(record)
        historical = verify_historical_inputs(record, commit)
        verify_pinned_sources(historical)
        verify_retained_outputs(record)
    except (OSError, VerificationError) as error:
        print(str(error), file=sys.stderr)
        return 1

    print("Compact List.head comparison record verified")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
