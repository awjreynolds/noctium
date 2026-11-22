#!/usr/bin/env python3
"""Measure repeated, pinned PrivateClaim source-proof report checks."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
OPERATION = "PrivateClaim.claim"
POLICY = "Noctium.PrivateClaimVerification.policy"
FUNCTIONAL = "Noctium.PrivateClaimVerification.functional"
PRIVACY = "Noctium.PrivateClaimVerification.privacy"
MODEL_PIN = ROOT / "proofs/PrivateClaimVerification.model.sha256"


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def file_record(path: Path) -> dict:
    contents = path.read_bytes()
    return {"bytes": len(contents), "sha256": sha256(contents)}


def validate_report(report: dict) -> None:
    if (report.get("operation") != OPERATION
            or report.get("status") != "source-functional-and-scoped-privacy-checked"
            or report.get("sourceFunctionalChecked") is not True
            or report.get("sourcePrivacyChecked") is not True
            or report.get("compiledContractVerified") is not False
            or report.get("policy") != POLICY
            or report.get("functionalProof") != FUNCTIONAL
            or report.get("privacyProof") != PRIVACY
            or report.get("selectedOperations") != [OPERATION]):
        raise ValueError("report does not confirm the pinned PrivateClaim.claim source obligations")


def validate_export_identities(report: dict, output: Path) -> str:
    pin = MODEL_PIN.read_text().strip()
    retained_pin = (output / "trusted-model.sha256").read_text().strip()
    model_digest = file_record(output / "trusted-model.ndjson")["sha256"]
    proof_digest = file_record(output / "proofs.ndjson")["sha256"]
    if retained_pin != pin or model_digest != pin or report.get("trustedModelSha256") != pin:
        raise ValueError("report and retained model do not match the checked-in model pin")
    if report.get("proofExportSha256") != proof_digest:
        raise ValueError("report proof digest does not match the retained proof export")
    return pin


def run_bytes(command: list[str], timeout: int = 900) -> tuple[bytes, float]:
    started = time.monotonic()
    try:
        result = subprocess.run(command, cwd=ROOT, capture_output=True, timeout=timeout)
    except (OSError, subprocess.TimeoutExpired) as error:
        raise RuntimeError(f"command failed: {command[0]}: {error}") from error
    elapsed = time.monotonic() - started
    if result.returncode:
        detail = result.stderr.decode(errors="replace").strip() or result.stdout.decode(errors="replace").strip() or f"exit {result.returncode}"
        raise RuntimeError(f"command failed: {command[0]}: {detail}")
    return result.stdout, elapsed


def run_command(command: list[str], timeout: int = 900) -> tuple[str, float]:
    stdout, elapsed = run_bytes(command, timeout)
    return stdout.decode(), elapsed


def report_run(output: Path) -> tuple[bytes, float]:
    command = [sys.executable, "scripts/proofs/check-private-claim-audit.py", "--report",
               "--output-dir", str(output)]
    stdout, elapsed = run_bytes(command)
    try:
        report = json.loads(stdout)
        validate_report(report)
        validate_export_identities(report, output)
    except (ValueError, TypeError, AttributeError) as error:
        raise RuntimeError(f"invalid {OPERATION} report: {error}") from error
    return stdout, elapsed


def replay(output: Path, report: dict) -> tuple[float, dict]:
    command = [sys.executable, "scripts/proofs/audit-source-proof.py",
               "--model-export", str(output / "trusted-model.ndjson"),
               "--proof-export", str(output / "proofs.ndjson"),
               "--trusted-model-sha256", MODEL_PIN.read_text().strip(),
               "--policy", POLICY, "--functional-proof", FUNCTIONAL, "--privacy-proof", PRIVACY]
    stdout, elapsed = run_command(command)
    try:
        result = json.loads(stdout)
    except ValueError as error:
        raise RuntimeError(f"invalid data-only replay result: {error}") from error
    if result != json.loads((output / "audit.json").read_text()):
        raise RuntimeError("data-only replay differs from the checked report audit")
    if (result.get("operation") != OPERATION or result.get("sourceFunctionalChecked") is not True
            or result.get("sourcePrivacyChecked") is not True or result.get("compiledContractVerified") is not False):
        raise RuntimeError("data-only replay did not confirm both source-proof roles")
    try:
        pin = validate_export_identities(report, output)
    except (OSError, ValueError) as error:
        raise RuntimeError(str(error)) from error
    if (result.get("trustedModelSha256") != pin
            or result.get("proofExportSha256") != file_record(output / "proofs.ndjson")["sha256"]):
        raise RuntimeError("data-only replay digests differ from the pinned report exports")
    return elapsed, result


def provenance() -> dict:
    revision, _ = run_command(["git", "rev-parse", "HEAD"])
    dirty, _ = run_command(["git", "status", "--porcelain"])
    files = ["lean-toolchain", "lake-manifest.json", "profiles/midnight-ledger-9-zkir-3.2.1-target.json",
             "examples/PrivateClaim.lean", "proofs/PrivateClaim.lean", "proofs/PrivateClaimVerification.lean",
             "proofs/PrivateClaimVerification.model.sha256", "scripts/proofs/check-private-claim-audit.py",
             "scripts/proofs/audit-source-proof.py", "scripts/proofs/benchmark-source-report.py"]
    return {
        "revision": revision.strip(),
        "worktreeDirty": bool(dirty.strip()),
        "checkedInputHashes": {name: file_record(ROOT / name) for name in files},
        "lean": run_command(["lean", "--version"])[0].strip(),
        "lake": run_command(["lake", "--version"])[0].strip(),
        "profile": "midnight-ledger-9-zkir-3.2.1",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, required=True,
                        help="new or empty directory for generated benchmark evidence")
    args = parser.parse_args()
    output = args.output_dir.resolve()
    if output.exists() and any(output.iterdir()):
        parser.error(f"output directory must be empty: {output}")
    output.mkdir(parents=True, exist_ok=True)
    run_dirs = [output / "report-1", output / "report-2"]
    for directory in run_dirs:
        directory.mkdir()

    first, first_seconds = report_run(run_dirs[0])
    second, second_seconds = report_run(run_dirs[1])
    if first != second:
        raise RuntimeError("equivalent report runs produced different JSON bytes")
    report = json.loads(first)
    replay_seconds, replay_result = replay(run_dirs[0], report)
    records = []
    for directory, elapsed, stdout in zip(run_dirs, (first_seconds, second_seconds), (first, second)):
        records.append({
            "elapsedSeconds": round(elapsed, 6),
            "report": {"bytes": len(stdout), "sha256": sha256(stdout)},
            "trustedModel": file_record(directory / "trusted-model.ndjson"),
            "proofs": file_record(directory / "proofs.ndjson"),
            "trustedModelPin": (directory / "trusted-model.sha256").read_text().strip(),
        })
    if (records[0]["trustedModel"] != records[1]["trustedModel"]
            or records[0]["proofs"] != records[1]["proofs"]
            or records[0]["trustedModelPin"] != records[1]["trustedModelPin"]):
        raise RuntimeError("equivalent report runs produced different model or proof data")
    result = {
        "schemaVersion": 1,
        "status": "passed",
        "scope": "PrivateClaim.claim functional and scoped privacy source-proof report",
        "timing": {"clock": "monotonic wall time", "reportRuns": records,
                   "dataOnlyReplaySeconds": round(replay_seconds, 6)},
        "equivalentReportsByteIdentical": True,
        "dataOnlyReplayMatchesReport": True,
        "replay": {"trustedModel": file_record(run_dirs[0] / "trusted-model.ndjson"),
                   "proofs": file_record(run_dirs[0] / "proofs.ndjson"),
                   "status": replay_result["status"]},
        "dependencies": "fresh processes with the existing .lake cache; each report includes the checker build step, no clean build",
        "provenance": provenance(),
    }
    (output / "benchmark.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError, ValueError) as error:
        print(f"source-proof benchmark failed: {error}", file=sys.stderr)
        raise SystemExit(1)
