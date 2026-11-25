#!/usr/bin/env python3
"""Validate the offline Compact capability register."""
from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path, PurePosixPath, PureWindowsPath
import re
import sys
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MATRIX = ROOT / "docs/compatibility/compact-feature-matrix.json"
TARGET_PROFILE = ROOT / "profiles/midnight-ledger-9-zkir-3.2.1-target.json"

CASE_ID = re.compile(r"C-[A-Z0-9]+(?:-[A-Z0-9]+)*\Z")
COMPACT_BASELINE = {
    "featureToolchain": "0.36.1",
    "language": "0.28.0",
    "compactRuntimeReferenceOnly": "0.21.0",
    "sourceRepository": "LFDT-Minokawa/compact",
    "sourceCommit": "7fa3a117c5e7efe9d2c51da04263e5f0b3509144",
    "sourceTag": "compactc-v0.36.1",
    "ledger": "9.1.0.1",
    "ledgerCommit": "a2b30128ca4b660b73a068e29b56b48ede8c9a74",
    "bundledZkir": "3.2.1",
    "bundledZkirCommit": "7a51b3385bbf4bce3604df87a7c70867c9ab43c0",
}
TARGET_NAME = "midnight-ledger-9-zkir-3.2.1"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def read_json_object(path: Path, subject: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ValueError(f"unable to read {subject}: {path}") from error
    require(isinstance(value, dict), f"invalid {subject}: expected a JSON object")
    return value


def validate_baseline(matrix: dict[str, Any]) -> None:
    baseline = matrix.get("baseline")
    require(isinstance(baseline, dict), "baseline missing or invalid")
    for key, expected in COMPACT_BASELINE.items():
        require(baseline.get(key) == expected, f"baseline pin mismatch: {key}")

    profile = read_json_object(TARGET_PROFILE, "target profile")
    require(type(profile.get("schemaVersion")) is int and profile["schemaVersion"] == 1,
            "target profile schema mismatch")
    native_source = profile.get("nativeSource")
    require(isinstance(native_source, dict), "target profile native source missing")
    require(profile.get("name") == TARGET_NAME
            and profile.get("ledger") == COMPACT_BASELINE["ledger"]
            and profile.get("zkir") == COMPACT_BASELINE["bundledZkir"],
            "target profile identity mismatch")
    require(native_source.get("revision") == COMPACT_BASELINE["bundledZkirCommit"],
            "target profile ZKIR revision mismatch")
    require(baseline.get("bundledZkirCommit") == native_source["revision"],
            "baseline pin mismatch: bundledZkirCommit")


def evidence_file_path(reference: str, case_id: str) -> Path:
    raw_path, marker, fragment = reference.partition("#")
    require(bool(raw_path), f"invalid evidence file for {case_id}: {reference}")
    if marker:
        require(bool(fragment) and Path(raw_path).suffix.lower() in {".md", ".mdx"},
                f"invalid evidence fragment for {case_id}: {reference}")

    windows_path = PureWindowsPath(raw_path)
    posix_path = PurePosixPath(raw_path)
    require(not Path(raw_path).is_absolute()
            and not windows_path.is_absolute()
            and not windows_path.drive
            and not raw_path.startswith("/")
            and "\\" not in raw_path,
            f"invalid evidence file for {case_id}: {reference}")
    require(".." not in posix_path.parts,
            f"invalid evidence file for {case_id}: {reference}")

    path = ROOT / Path(*posix_path.parts)
    resolved = path.resolve()
    require(resolved.is_relative_to(ROOT),
            f"invalid evidence file for {case_id}: {reference}")
    if not resolved.is_file():
        raise ValueError(f"missing evidence file for {case_id}: {reference}")
    return resolved


def validate_features(matrix: dict[str, Any]) -> list[dict[str, Any]]:
    sources = matrix.get("sources")
    require(isinstance(sources, dict) and bool(sources), "sources missing or invalid")
    source_keys = set(sources)

    evidence_kinds = matrix.get("evidenceKinds")
    require(isinstance(evidence_kinds, dict) and bool(evidence_kinds),
            "evidenceKinds missing or invalid")
    evidence_tokens = set(evidence_kinds)

    status_meaning = matrix.get("statusMeaning")
    require(isinstance(status_meaning, dict), "statusMeaning missing or invalid")
    valid_statuses = set(status_meaning) | {"equivalent"}

    features = matrix.get("features")
    require(isinstance(features, list) and bool(features), "features missing or empty")
    seen_ids: set[str] = set()
    for feature in features:
        require(isinstance(feature, dict), "invalid feature entry")
        case_id = feature.get("id")
        require(isinstance(case_id, str) and CASE_ID.fullmatch(case_id) is not None,
                f"invalid case ID: {case_id}")
        if case_id in seen_ids:
            raise ValueError(f"duplicate case ID: {case_id}")
        seen_ids.add(case_id)

        feature_sources = feature.get("source")
        require(isinstance(feature_sources, list) and bool(feature_sources)
                and all(isinstance(item, str) and item for item in feature_sources),
                f"source keys missing or invalid for {case_id}")
        require(len(set(feature_sources)) == len(feature_sources),
                f"duplicate source key for {case_id}")
        for source in feature_sources:
            require(source in source_keys, f"undefined source for {case_id}: {source}")

        required = feature.get("requiredEvidence")
        require(isinstance(required, list) and bool(required)
                and all(isinstance(item, str) and item in evidence_tokens for item in required),
                f"required evidence invalid for {case_id}")

        observed = feature.get("observedEvidence")
        require(isinstance(observed, list),
                f"observed evidence missing or invalid for {case_id}")
        for item in observed:
            require(isinstance(item, str) and bool(item),
                    f"observed evidence invalid for {case_id}")
            if item not in evidence_tokens:
                evidence_file_path(item, case_id)

        status = feature.get("noctiumStatus")
        require(isinstance(status, str) and status in valid_statuses,
                f"invalid status for {case_id}: {status}")
        equivalence = feature.get("equivalence")
        require(isinstance(equivalence, str)
                and equivalence in {"verified", "unverified"},
                f"invalid equivalence for {case_id}: {equivalence}")
        require(isinstance(feature.get("layer"), str) and bool(feature["layer"]),
                f"layer missing or invalid for {case_id}")
    return features


def summarize(features: list[dict[str, Any]]) -> None:
    extensions = [feature for feature in features
                  if feature["layer"] == "noctium-extension"]
    compact_cases = [feature for feature in features
                     if feature["layer"] != "noctium-extension"]
    joint = Counter((feature["noctiumStatus"], feature["equivalence"])
                    for feature in features)
    verification = Counter(feature["equivalence"] for feature in features)
    compact_verification = Counter(feature["equivalence"] for feature in compact_cases)

    print(f"Validated Compact capability register: {len(features)} cases")
    print(f"Verification: {verification['verified']} verified, "
          f"{verification['unverified']} unverified")
    for status, equivalence in sorted(joint):
        print(f"{status} + {equivalence}: {joint[(status, equivalence)]}")
    print(f"Compact cases: {len(compact_cases)} "
          f"({compact_verification['verified']} verified, "
          f"{compact_verification['unverified']} unverified)")
    if extensions:
        extension_summary = ", ".join(
            f"{feature['id']} ({feature['noctiumStatus']}, {feature['equivalence']})"
            for feature in extensions
        )
        print(f"Noctium extensions: {extension_summary}")
    else:
        print("Noctium extensions: 0")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--matrix", type=Path, default=DEFAULT_MATRIX,
                        help="register JSON path (default: repository Compact register)")
    args = parser.parse_args()
    matrix_path = args.matrix if args.matrix.is_absolute() else Path.cwd() / args.matrix
    try:
        matrix = read_json_object(matrix_path, "Compact capability register")
        require(type(matrix.get("schemaVersion")) is int
                and matrix["schemaVersion"] == 1,
                "unsupported Compact capability register schema")
        validate_baseline(matrix)
        features = validate_features(matrix)
        summarize(features)
    except (OSError, ValueError) as error:
        print(f"Compact capability register check failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
