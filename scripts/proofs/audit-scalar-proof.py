#!/usr/bin/env python3
"""Replay scalar circuit proof exports against independently pinned role types."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
MAX_EXPORT_BYTES = 160 * 1024 * 1024


def retained_file(path: Path) -> bytes:
    descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    with os.fdopen(descriptor, "rb") as handle:
        metadata = os.fstat(handle.fileno())
        if not stat.S_ISREG(metadata.st_mode):
            raise ValueError("export_not_regular_file")
        if metadata.st_size > MAX_EXPORT_BYTES:
            raise ValueError("export_limit")
        data = handle.read(MAX_EXPORT_BYTES + 1)
    if len(data) > MAX_EXPORT_BYTES:
        raise ValueError("export_limit")
    return data


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--model-export", type=Path, required=True)
    parser.add_argument("--proof-export", type=Path, required=True)
    parser.add_argument("--trusted-model-sha256", required=True)
    parser.add_argument("--soundness-proof", required=True)
    parser.add_argument("--completeness-proof", required=True)
    args = parser.parse_args()
    try:
        if not re.fullmatch("[0-9a-f]{64}", args.trusted_model_sha256):
            raise ValueError("invalid_model_pin")
        model, proof = retained_file(args.model_export), retained_file(args.proof_export)
        model_digest = hashlib.sha256(model).hexdigest()
        if model_digest != args.trusted_model_sha256:
            raise ValueError("model_pin_mismatch")
        with tempfile.TemporaryDirectory(prefix="noctium-scalar-audit-") as directory:
            scratch = Path(directory)
            model_path, proof_path = scratch / "model.ndjson", scratch / "proof.ndjson"
            model_path.write_bytes(model)
            proof_path.write_bytes(proof)
            environment = os.environ.copy()
            environment.pop("LEAN_PATH", None)
            environment.pop("LEAN_SRC_PATH", None)
            checked = subprocess.run(
                ["lake", "env", "lean", "--run", "scripts/proofs/AuditScalarExport.lean",
                 str(model_path), str(proof_path), args.soundness_proof, args.completeness_proof],
                cwd=ROOT, env=environment, capture_output=True, text=True, timeout=180,
                check=False,
            )
        if checked.returncode:
            try:
                error = json.loads(checked.stderr)["error"]
            except (ValueError, KeyError, TypeError):
                error = "trusted_scalar_checker_failed"
            raise ValueError(error)
        result = json.loads(checked.stdout)
        if result.get("wholeCompilerVerified") is not False:
            raise ValueError("unexpected_checker_status")
        result.update({
            "trustedModelSha256": model_digest,
            "proofExportSha256": hashlib.sha256(proof).hexdigest(),
            "externalModelPinChecked": True,
            "freshKernelReplay": True,
            "compilerBuildAuthenticated": False,
        })
        result.pop("externalModelPinRequired", None)
        print(json.dumps(result, sort_keys=True))
        return 0
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print(json.dumps({"status": "rejected", "error": str(error)}))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
