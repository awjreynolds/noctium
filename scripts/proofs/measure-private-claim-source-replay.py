#!/usr/bin/env python3
"""Measure PrivateClaim source compilation and data-only proof replay separately."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import platform
import subprocess
import sys
import tempfile
import time
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
OPERATION = "PrivateClaim.claim"
POLICY = "Noctium.PrivateClaimVerification.policy"
FUNCTIONAL = "Noctium.PrivateClaimVerification.functional"
PRIVACY = "Noctium.PrivateClaimVerification.privacy"
MODEL_PIN = ROOT / "proofs/PrivateClaimVerification.model.sha256"
TARGET = ROOT / "profiles/midnight-ledger-9-zkir-3.2.1-target.json"
SOURCE_FILES = [
    "examples/PrivateClaim.lean",
    "proofs/PrivateClaim.lean",
    "proofs/PrivateClaimVerification.lean",
]
MIB = 1024 * 1024
PERFORMANCE_TARGETS = {
    "timeSeconds": {
        "dependencyBuild": 10.0,
        "sourceCompilation": 12.0,
        "sourceReportGeneration": 120.0,
        "dataOnlyReplay": 35.0,
    },
    "sizeBytes": {
        "sourceReport": 8 * 1024,
        "auditReport": 20 * 1024,
        "trustedModel": 32 * MIB,
        "proofExport": 56 * MIB,
    },
}
SAFETY_CEILINGS = {
    "timeSeconds": {
        "dependencyBuild": 300.0,
        "sourceCompilation": 240.0,
        "dataOnlyReplay": 180.0,
        "sourceReportGeneration": 900.0,
    },
    "sizeBytes": {
        "sourceReport": 64 * 1024,
        "auditReport": 64 * 1024,
        "trustedModel": 64 * MIB,
        "proofExport": 64 * MIB,
    },
}
MEASURED_BASELINE = {
    "revision": "e1bc5935d94d9c91049c944056be142273031058",
    "worktreeDirty": True,
    "measurementHelperSha256": "6b8a02b5d7c54a398107560051f2f9435fb0200afa0a0fbbd933c1ad6dd1ee6a",
    "deterministicEvidenceSha256": "2260de3cd423edf1003aa58906ba95986c0635d3d01a94a488293aac9c9607fd",
    "platform": "macOS-26.6.2-arm64-arm-64bit-Mach-O",
    "lean": "Lean (version 4.35.0, arm64-apple-darwin24.6.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)",
    "lake": "Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)",
    "timeSeconds": {
        "dependencyBuild": 0.409252,
        "sourceCompilation": 8.710147,
        "dataOnlyReplay": 30.532533,
    },
    "sizeBytes": {
        "sourceReport": 6539,
        "auditReport": 16686,
        "trustedModel": 33148293,
        "proofExport": 46622538,
    },
}


def sha256_bytes(contents: bytes) -> str:
    return hashlib.sha256(contents).hexdigest()


def file_record(path: Path, size_ceiling: int | None = None) -> dict[str, Any]:
    size = path.stat().st_size
    if size_ceiling is not None and size > size_ceiling:
        raise ValueError(f"safety_size_ceiling_exceeded:{path.name}:{size}")
    digest = hashlib.sha256()
    measured_size = 0
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            measured_size += len(chunk)
            digest.update(chunk)
    return {"bytes": measured_size, "sha256": digest.hexdigest()}


def files_equal(left: Path, right: Path) -> bool:
    if left.stat().st_size != right.stat().st_size:
        return False
    with left.open("rb") as left_stream, right.open("rb") as right_stream:
        while True:
            left_chunk = left_stream.read(1024 * 1024)
            right_chunk = right_stream.read(1024 * 1024)
            if left_chunk != right_chunk:
                return False
            if not left_chunk:
                return True


def run_bytes(command: list[str], env: dict[str, str] | None = None,
              timeout: int = 900) -> tuple[bytes, float]:
    started = time.monotonic()
    try:
        result = subprocess.run(command, cwd=ROOT, env=env, capture_output=True,
                                timeout=timeout, check=False)
    except (OSError, subprocess.TimeoutExpired) as error:
        raise RuntimeError(f"command failed: {command[0]}: {error}") from error
    elapsed = time.monotonic() - started
    if result.returncode:
        detail = (result.stderr.decode(errors="replace").strip()
                  or result.stdout.decode(errors="replace").strip()
                  or f"exit {result.returncode}")
        raise RuntimeError(f"command failed: {command[0]}: {detail}")
    return result.stdout, elapsed


def source_report(output: Path) -> tuple[bytes, dict[str, Any], float]:
    output.mkdir()
    stdout, elapsed = run_bytes([
        sys.executable, "scripts/proofs/check-private-claim-audit.py", "--report",
        "--output-dir", str(output),
    ], timeout=int(SAFETY_CEILINGS["timeSeconds"]["sourceReportGeneration"]))
    if elapsed > SAFETY_CEILINGS["timeSeconds"]["sourceReportGeneration"]:
        raise ValueError(f"safety_time_ceiling_exceeded:sourceReportGeneration:{elapsed:.6f}")
    if len(stdout) > SAFETY_CEILINGS["sizeBytes"]["sourceReport"]:
        raise ValueError(f"source_report_safety_size_ceiling_exceeded:{len(stdout)}")
    try:
        report = json.loads(stdout)
    except (json.JSONDecodeError, UnicodeDecodeError) as error:
        raise RuntimeError(f"{OPERATION}: source report was not JSON") from error
    if (not isinstance(report, dict)
            or report.get("operation") != OPERATION
            or report.get("status") != "source-functional-and-scoped-privacy-checked"):
        raise ValueError(f"{OPERATION}: existing source report checker returned no accepted report")
    file_record(output / "audit.json", SAFETY_CEILINGS["sizeBytes"]["auditReport"])
    file_record(output / "trusted-model.ndjson", SAFETY_CEILINGS["sizeBytes"]["trustedModel"])
    file_record(output / "proofs.ndjson", SAFETY_CEILINGS["sizeBytes"]["proofExport"])
    return stdout, report, elapsed


def data_only_replay(output: Path, pin: str) -> tuple[bytes, float]:
    stdout, elapsed = run_bytes([
        sys.executable, "scripts/proofs/audit-source-proof.py",
        "--model-export", str(output / "trusted-model.ndjson"),
        "--proof-export", str(output / "proofs.ndjson"),
        "--trusted-model-sha256", pin,
        "--policy", POLICY,
        "--functional-proof", FUNCTIONAL,
        "--privacy-proof", PRIVACY,
    ], timeout=int(SAFETY_CEILINGS["timeSeconds"]["dataOnlyReplay"]))
    try:
        result = json.loads(stdout)
    except (json.JSONDecodeError, UnicodeDecodeError) as error:
        raise RuntimeError(f"{OPERATION}: data-only replay was not JSON") from error
    retained = json.loads((output / "audit.json").read_bytes())
    if result != retained:
        raise ValueError(f"{OPERATION}: data-only replay differs from the source report audit")
    if (result.get("operation") != OPERATION
            or result.get("trustedModelSha256") != pin
            or result.get("sourceFunctionalChecked") is not True
            or result.get("sourcePrivacyChecked") is not True
            or result.get("compiledContractVerified") is not False):
        raise ValueError(f"{OPERATION}: data-only replay did not confirm both source roles")
    return stdout, elapsed


def provenance() -> dict[str, Any]:
    def command_output(command: list[str]) -> str:
        stdout, _ = run_bytes(command, timeout=60)
        return stdout.decode().strip()

    files = [
        "lean-toolchain", "lake-manifest.json", "profiles/midnight-ledger-9-zkir-3.2.1-target.json",
        *SOURCE_FILES, "proofs/PrivateClaimVerification.model.sha256",
        "tests/private-claim-source-coverage.sh",
        "scripts/proofs/check-private-claim-audit.py", "scripts/proofs/audit-source-proof.py",
        "scripts/proofs/measure-private-claim-source-replay.py",
    ]
    dirty = command_output(["git", "status", "--porcelain"])
    return {
        "revision": command_output(["git", "rev-parse", "HEAD"]),
        "worktreeDirty": bool(dirty),
        "platform": platform.platform(),
        "lean": command_output(["lean", "--version"]),
        "lake": command_output(["lake", "--version"]),
        "targetProfileSha256": file_record(TARGET)["sha256"],
        "inputs": {name: file_record(ROOT / name) for name in files},
    }


def run_measurement() -> dict[str, Any]:
    experiment_root = ROOT / "build/experiments"
    experiment_root.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="private-claim-replay-measurement-",
                                     dir=experiment_root) as temporary:
        scratch = Path(temporary)
        _, dependency_build_seconds = run_bytes([
            "lake", "build", "Noctium", "Noctium.Cli", "Noctium.Compiler", "Noctium.Frontend",
            "Noctium.Verification.ExportAudit",
        ], timeout=int(SAFETY_CEILINGS["timeSeconds"]["dependencyBuild"]))
        _, source_compile_seconds = run_bytes(
            ["bash", "tests/private-claim-source-coverage.sh"],
            timeout=int(SAFETY_CEILINGS["timeSeconds"]["sourceCompilation"]))
        measured_times = {
            "dependencyBuild": dependency_build_seconds,
            "sourceCompilation": source_compile_seconds,
        }
        for name, elapsed in measured_times.items():
            if elapsed > SAFETY_CEILINGS["timeSeconds"][name]:
                raise ValueError(f"safety_time_ceiling_exceeded:{name}:{elapsed:.6f}")

        first_dir, second_dir = scratch / "report-1", scratch / "report-2"
        first_bytes, first, source_report_generation_seconds = source_report(first_dir)
        second_bytes, second, _ = source_report(second_dir)
        if first_bytes != second_bytes:
            raise ValueError("repeated PrivateClaim source reports differ byte-for-byte")
        if not files_equal(first_dir / "trusted-model.ndjson", second_dir / "trusted-model.ndjson"):
            raise ValueError("repeated PrivateClaim model exports differ byte-for-byte")
        if not files_equal(first_dir / "proofs.ndjson", second_dir / "proofs.ndjson"):
            raise ValueError("repeated PrivateClaim proof exports differ byte-for-byte")
        if not files_equal(first_dir / "audit.json", second_dir / "audit.json"):
            raise ValueError("repeated PrivateClaim proof audits differ byte-for-byte")
        pin = MODEL_PIN.read_text(encoding="ascii").strip()

        replay_bytes, replay_seconds = data_only_replay(first_dir, pin)
        if replay_seconds > SAFETY_CEILINGS["timeSeconds"]["dataOnlyReplay"]:
            raise ValueError(f"safety_time_ceiling_exceeded:dataOnlyReplay:{replay_seconds:.6f}")

        model_record = file_record(first_dir / "trusted-model.ndjson",
                                   SAFETY_CEILINGS["sizeBytes"]["trustedModel"])
        proof_record = file_record(first_dir / "proofs.ndjson",
                                   SAFETY_CEILINGS["sizeBytes"]["proofExport"])
        audit_record = file_record(first_dir / "audit.json",
                                   SAFETY_CEILINGS["sizeBytes"]["auditReport"])
        size_measurements = {
            "sourceReport": len(first_bytes),
            "auditReport": audit_record["bytes"],
            "trustedModel": model_record["bytes"],
            "proofExport": proof_record["bytes"],
        }
        target_status = {
            "timeSeconds": {
                "dependencyBuild": dependency_build_seconds <= PERFORMANCE_TARGETS["timeSeconds"]["dependencyBuild"],
                "sourceCompilation": source_compile_seconds <= PERFORMANCE_TARGETS["timeSeconds"]["sourceCompilation"],
                "sourceReportGeneration": source_report_generation_seconds <= PERFORMANCE_TARGETS["timeSeconds"]["sourceReportGeneration"],
                "dataOnlyReplay": replay_seconds <= PERFORMANCE_TARGETS["timeSeconds"]["dataOnlyReplay"],
            },
            "sizeBytes": {
                name: size <= PERFORMANCE_TARGETS["sizeBytes"][name]
                for name, size in size_measurements.items()
            },
        }
        target_status["allMet"] = all(
            value for category in (target_status["timeSeconds"], target_status["sizeBytes"])
            for value in category.values())

        evidence = {
            "operation": OPERATION,
            "sourceReport": {"bytes": len(first_bytes), "sha256": sha256_bytes(first_bytes),
                             "status": first["status"]},
            "trustedModel": model_record,
            "trustedModelPin": pin,
            "proofExport": proof_record,
            "auditReport": audit_record,
            "operationArtifacts": first["operationArtifacts"],
            "repeatedReportBytesEqual": True,
            "repeatedModelBytesEqual": True,
            "repeatedProofBytesEqual": True,
            "repeatedAuditBytesEqual": True,
            "dataOnlyReplayMatchesReport": True,
            "dataOnlyReplaySha256": sha256_bytes(replay_bytes),
            "dataOnlyReplayStatus": json.loads(replay_bytes)["status"],
        }
        evidence_digest = sha256_bytes(json.dumps(
            evidence, ensure_ascii=True, sort_keys=True, separators=(",", ":")
        ).encode())
        return {
            "schemaVersion": 1,
            "status": "passed",
            "scope": {
                "dependencyBuild": "Wall time for lake build of the source-audit Lean dependencies. This is reported separately from entrypoint source compilation and proof replay.",
                "sourceCompilation": "Wall time for bash tests/private-claim-source-coverage.sh. It compiles the PrivateClaim example, support and verification modules, then elaborates source-role coverage using the shared Lake dependencies.",
                "sourceReportGeneration": "Wall time for the first fresh check-private-claim-audit.py --report command. It includes that command's dependency build, source compilation, proof exports, and built-in source checks. The second report run only confirms byte equality and is not timed here.",
                "dataOnlyReplay": "Wall time for one fresh audit-source-proof.py process over the retained pinned model and proof exports. It excludes source compilation and export generation.",
            },
            "measurements": {
                "dependencyBuildSeconds": round(dependency_build_seconds, 6),
                "sourceCompilationSeconds": round(source_compile_seconds, 6),
                "sourceReportGenerationSeconds": round(source_report_generation_seconds, 6),
                "dataOnlyReplaySeconds": round(replay_seconds, 6),
                "sourceReportBytes": len(first_bytes),
                "auditReportBytes": audit_record["bytes"],
                "trustedModelBytes": model_record["bytes"],
                "proofExportBytes": proof_record["bytes"],
            },
            "measuredBaseline": MEASURED_BASELINE,
            "performanceTargets": PERFORMANCE_TARGETS,
            "targetStatus": target_status,
            "safetyCeilings": SAFETY_CEILINGS,
            "deterministicEvidence": evidence,
            "deterministicEvidenceSha256": evidence_digest,
            "provenance": provenance(),
        }


def main() -> int:
    result = run_measurement()
    print(json.dumps(result, ensure_ascii=True, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError, ValueError, KeyError, TypeError) as error:
        print(f"PrivateClaim source replay measurement failed: {error}", file=sys.stderr)
        raise SystemExit(1)
