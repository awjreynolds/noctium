#!/usr/bin/env python3
"""Bind one compiler-emitted source operation to its exact public artifacts.

This checks operation selection and artifact identity in a fresh Noctium
compiler output directory. It records bytes and digests, but does not certify
source-to-native preservation or authenticate the compiler build.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys
from typing import Any


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def strict_json(data: bytes, filename: str) -> dict[str, Any]:
    def pairs(items: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in items:
            if key in result:
                raise ValueError(f"duplicate_json_key:{filename}:{key}")
            result[key] = value
        return result

    try:
        value = json.loads(data, object_pairs_hook=pairs)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ValueError(f"invalid_json:{filename}") from error
    require(isinstance(value, dict), f"invalid_json_object:{filename}")
    return value


def require(condition: bool, code: str) -> None:
    if not condition:
        raise ValueError(code)


def safe_artifact(root: Path, relative: Any, expected_name: str) -> tuple[Path, bytes]:
    require(isinstance(relative, str) and bool(relative), f"missing_{expected_name}_path")
    posix = PurePosixPath(relative)
    require(not posix.is_absolute() and all(part not in ("", ".", "..") for part in posix.parts),
            f"unsafe_{expected_name}_path")
    require(posix.as_posix() == relative, f"noncanonical_{expected_name}_path")
    path = root
    for part in posix.parts:
        path = path / part
        require(not path.is_symlink(), f"symlink_{expected_name}_path")
    require(path.is_file(), f"missing_{expected_name}_file")
    return path, path.read_bytes()


def named_inventory(values: Any, key: str, label: str) -> dict[str, dict[str, Any]]:
    require(isinstance(values, list), f"invalid_{label}_inventory")
    records = {}
    for item in values:
        require(isinstance(item, dict), f"invalid_{label}_record")
        name = item.get(key)
        require(isinstance(name, str) and bool(name), f"invalid_{label}_{key}")
        require(name not in records, f"duplicate_{label}_{key}")
        records[name] = item
    return records


def select_operation(manifest: dict[str, Any], contract: str, entrypoint: str) -> dict[str, Any]:
    require(manifest.get("schemaVersion") == 3, "manifest_requires_plan_digest_schema")
    contracts = named_inventory(manifest.get("contracts"), "name", "contract")
    require(contract in contracts, "contract_selection_mismatch")
    files = named_inventory(manifest.get("artifacts"), "file", "artifact")
    used_paths = set()
    selected = None
    for contract_name, declaration in contracts.items():
        entries = named_inventory(declaration.get("entrypoints"), "name", "entrypoint")
        for entry_name, operation in entries.items():
            for field in ("nativeCircuitFile", "nativePlanFile"):
                value = operation.get(field)
                require(isinstance(value, str) and value in files, f"unlisted_{field}")
                require(files[value].get("role") == "ledger", f"wrong_{field}_role")
                require(value not in used_paths, "reused_operation_artifact")
                used_paths.add(value)
            if (contract_name, entry_name) == (contract, entrypoint):
                selected = operation
    require(selected is not None, "entrypoint_selection_mismatch")
    expected_circuit = f"{contract}.{entrypoint}.zkir"
    expected_plan = f"{contract}.{entrypoint}.impact.json"
    require(selected.get("nativeCircuitFile") == expected_circuit, "entrypoint_circuit_filename_mismatch")
    require(selected.get("nativePlanFile") == expected_plan, "entrypoint_plan_filename_mismatch")
    circuit_name = selected.get("circuit")
    require(isinstance(circuit_name, str) and bool(circuit_name), "missing_circuit_name")
    return selected


def bind_operation(directory: Path, profile_path: Path, profile_pin: str,
                   contract: str, entrypoint: str) -> dict[str, Any]:
    require(re.fullmatch(r"[0-9a-f]{64}", profile_pin) is not None, "invalid_profile_sha256")
    directory = directory.resolve(strict=True)
    require(not profile_path.is_symlink(), "invalid_profile_file")
    profile_path = profile_path.resolve(strict=True)
    require(profile_path.is_file(), "invalid_profile_file")

    manifest_path = directory / "noctium.json"
    require(not manifest_path.is_symlink() and manifest_path.is_file(), "missing_noctium_manifest")
    manifest_bytes = manifest_path.read_bytes()
    manifest = strict_json(manifest_bytes, manifest_path.name)
    operation = select_operation(manifest, contract, entrypoint)

    profile_bytes = profile_path.read_bytes()
    profile = strict_json(profile_bytes, profile_path.name)
    measured_profile_pin = sha256(profile_bytes)
    require(measured_profile_pin == profile_pin, "profile_pin_mismatch")
    profile_name = profile.get("name")
    require(isinstance(profile_name, str) and bool(profile_name), "missing_profile_name")
    require(manifest.get("target") == profile_name, "manifest_target_profile_name_mismatch")
    require(manifest.get("targetProfile") == profile, "manifest_target_profile_mismatch")

    call_path, call_bytes = safe_artifact(directory, operation["nativeCircuitFile"], "zkir")
    plan_path, plan_bytes = safe_artifact(directory, operation["nativePlanFile"], "impact")
    relation = strict_json(call_bytes, call_path.name)
    require(isinstance(relation.get("instructions"), list), "missing_zkir_instructions")
    plan = strict_json(plan_bytes, plan_path.name)
    require(plan.get("contractName") == contract, "impact_contract_mismatch")
    require(plan.get("entrypoint") == entrypoint, "impact_entrypoint_mismatch")
    require(plan.get("nativeCircuitFile") == operation["nativeCircuitFile"], "impact_circuit_filename_mismatch")
    require(isinstance(plan.get("circuit"), dict) and
            plan["circuit"].get("name") == operation["circuit"], "impact_source_circuit_mismatch")
    require(plan.get("target") == profile_name, "impact_target_mismatch")
    require(plan.get("targetProfile") == profile, "impact_target_profile_mismatch")
    plan_digest = sha256(plan_bytes)
    require(operation.get("nativePlanSha256") == plan_digest, "impact_manifest_digest_mismatch")

    return {
        "schemaVersion": 1,
        "status": "operation-artifacts-associated",
        "operation": {"contract": contract, "entrypoint": entrypoint, "circuit": operation["circuit"],
                      "circuitFile": call_path.name, "planFile": plan_path.name},
        "targetProfile": {"name": profile_name, "bytes": len(profile_bytes), "sha256": measured_profile_pin},
        "manifest": {"file": "noctium.json", "bytes": len(manifest_bytes), "sha256": sha256(manifest_bytes)},
        "artifacts": [
            {"role": "impact", "file": plan_path.relative_to(directory).as_posix(),
             "bytes": len(plan_bytes), "sha256": plan_digest},
            {"role": "zkir", "file": call_path.relative_to(directory).as_posix(),
             "bytes": len(call_bytes), "sha256": sha256(call_bytes)},
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifacts", type=Path, required=True, help="fresh compiler output directory")
    parser.add_argument("--profile", type=Path, required=True, help="externally selected target-profile JSON")
    parser.add_argument("--profile-sha256", required=True, help="trusted SHA-256 of the profile bytes")
    parser.add_argument("--contract", required=True)
    parser.add_argument("--entrypoint", required=True)
    args = parser.parse_args()
    try:
        result = bind_operation(args.artifacts, args.profile, args.profile_sha256,
                                args.contract, args.entrypoint)
        print(json.dumps(result, sort_keys=True, separators=(",", ":")))
        return 0
    except (OSError, ValueError) as error:
        print(json.dumps({"status": "rejected", "error": str(error)}, sort_keys=True, separators=(",", ":")))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
