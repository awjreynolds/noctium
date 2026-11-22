#!/usr/bin/env python3
"""Check receipt-pinned composition artifact selection without keys or proofs."""
from __future__ import annotations

import argparse
from pathlib import Path
import runpy
import shutil
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
HELPERS = runpy.run_path(str(ROOT / "scripts/proofs/check-private-claim-artifacts.py"))
sha = HELPERS["sha"]
strict_json_bytes = runpy.run_path(
    str(ROOT / "scripts/proofs/check-private-claim-lowering.py")
)["strict_json_bytes"]

SLOTS = {
    "caller": ("IndependentCaller.claim.impact.json", "IndependentCaller.claim.zkir"),
    "callee": ("IndependentCallee.advance.impact.json", "IndependentCallee.advance.zkir"),
}
RECEIPTS = [
    ROOT / "docs/development/independent-composition-receipt.json",
    ROOT / "docs/development/composition-transport-receipt.json",
]


def receipt_pins() -> dict[str, str]:
    receipts = [strict_json_bytes(path.read_bytes()) for path in RECEIPTS]
    pins: dict[str, str] = {}
    for slot, (plan_name, relation_name) in SLOTS.items():
        values = [
            (receipt[slot]["artifactSha256"]["plan"], receipt[slot]["artifactSha256"]["circuit"])
            for receipt in receipts
        ]
        if values[0] != values[1]:
            raise ValueError(f"receipt_pin_disagreement:{slot}")
        pins[plan_name], pins[relation_name] = values[0]
    return pins


def metadata_pairs(metadata: dict) -> dict[str, tuple[str, str]]:
    pairs: dict[str, tuple[str, str]] = {}
    for contract in metadata["contracts"]:
        if len(contract["entrypoints"]) != 1:
            raise ValueError("unexpected_entrypoint_count")
        entry = contract["entrypoints"][0]
        if entry["nativeCircuitQualified"] is not False:
            raise ValueError("artifact_qualification_changed")
        if contract["name"] == "IndependentCaller" and entry["name"] == "claim":
            slot = "caller"
        elif contract["name"] == "IndependentCallee" and entry["name"] == "advance":
            slot = "callee"
        else:
            raise ValueError("unexpected_contract_entrypoint")
        pairs[slot] = (entry["nativePlanFile"], entry["nativeCircuitFile"])
    return pairs


def verify(output: Path, selection: dict[str, tuple[str, str]], pins: dict[str, str]) -> None:
    expected_files = {name for pair in SLOTS.values() for name in pair}
    present_files = {path.name for path in output.iterdir() if path.is_file()}
    if present_files != expected_files | {"noctium.json"}:
        raise ValueError("missing_or_extra_artifact_files")

    metadata = strict_json_bytes((output / "noctium.json").read_bytes())
    if metadata["deployable"] is not False:
        raise ValueError("unexpected_deployable_bundle")
    artifact_rows = metadata["artifacts"]
    if len(artifact_rows) != 4 or any(row["role"] != "ledger" for row in artifact_rows):
        raise ValueError("artifact_role_mismatch")
    if {row["file"] for row in artifact_rows} != expected_files:
        raise ValueError("artifact_manifest_mismatch")
    if selection != metadata_pairs(metadata):
        raise ValueError("ledger_plan_relation_mapping_mismatch")

    for slot, (plan_name, relation_name) in selection.items():
        for name in (plan_name, relation_name):
            path = output / name
            if not path.is_file():
                raise ValueError(f"missing_selected_artifact:{name}")
            data = path.read_bytes()
            parsed = strict_json_bytes(data)
            if sha(path) != pins[name]:
                raise ValueError(f"receipt_hash_mismatch:{name}")
            if name == plan_name and parsed["entrypoint"] != ("claim" if slot == "caller" else "advance"):
                raise ValueError(f"plan_entrypoint_mismatch:{name}")
            if name == relation_name and parsed["version"] != {"major": 3, "minor": 2}:
                raise ValueError(f"relation_version_mismatch:{name}")


def rejected(label: str, output: Path, selection: dict[str, tuple[str, str]], pins: dict[str, str]) -> None:
    try:
        verify(output, selection, pins)
    except (KeyError, OSError, ValueError) as error:
        print(f"rejected {label}: {error}")
        return
    raise AssertionError(f"accepted invalid selection: {label}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path, help="fresh ledger output from the 469 pinned source")
    args = parser.parse_args()
    output = args.output.resolve()
    pins = receipt_pins()

    verify(output, SLOTS, pins)
    print("accepted exact caller/callee ledger artifact pairs")

    rejected("wrong artifact selection", output, {"caller": SLOTS["callee"], "callee": SLOTS["callee"]}, pins)
    rejected("crossed artifacts", output, {"caller": (SLOTS["caller"][0], SLOTS["callee"][1]), "callee": (SLOTS["callee"][0], SLOTS["caller"][1])}, pins)
    with tempfile.TemporaryDirectory(prefix="noctium-469-missing-artifact-") as directory:
        missing_output = Path(directory)
        for path in output.iterdir():
            if path.name != SLOTS["callee"][1]:
                shutil.copyfile(path, missing_output / path.name)
        rejected("missing artifact", missing_output, SLOTS, pins)
    return 0


if __name__ == "__main__":
    sys.exit(main())
