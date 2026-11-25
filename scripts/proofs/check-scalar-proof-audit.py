#!/usr/bin/env python3
"""Exercise exact scalar proof roles, model pins and transitive axiom rejection."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
SOUNDNESS = "Noctium.Verification.ScalarTranslationSoundness.lowerCircuit_sound"
COMPLETENESS = "Noctium.Verification.ScalarWitnessConstruction.lowerCircuit_complete"
FIXTURE = "ScalarAuditFixtures"


def run(args: list[str], env: dict[str, str] | None = None) -> str:
    result = subprocess.run(args, cwd=ROOT, env=env, capture_output=True, text=True, timeout=240)
    if result.returncode:
        raise AssertionError(f"command failed: {args}\n{result.stdout}\n{result.stderr}")
    return result.stdout


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--trusted-model-export", type=Path)
    parser.add_argument("--trusted-model-sha256")
    args = parser.parse_args()
    if bool(args.trusted_model_export) != bool(args.trusted_model_sha256):
        parser.error("external model and digest must be supplied together")
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    run(["lake", "build", "Noctium.Verification.ScalarCircuitWitness", "Noctium.Verification.ScalarExportAudit"])
    with tempfile.TemporaryDirectory(prefix="noctium-scalar-role-tests-") as directory:
        scratch = Path(directory)
        source = scratch / "source" / "ScalarAuditFixtures.lean"
        imports = scratch / "imports"
        source.parent.mkdir(parents=True)
        imports.mkdir()
        source.write_text(f'''import Noctium.Verification.ScalarCircuitWitness
import Lean
namespace {FIXTURE}
open Lean Elab Command in
run_cmd do
  for (name, root) in [(`{FIXTURE}.soundness, `{SOUNDNESS}), (`{FIXTURE}.completeness, `{COMPLETENESS})] do
    let some info := (← getEnv).find? root | throwError "missing role"
    liftCoreM <| addDecl (.thmDecl {{name := name, levelParams := info.levelParams, type := info.type, value := mkConst root}})
  let some info := (← getEnv).find? `{SOUNDNESS} | throwError "missing soundness"
  let rec weaken (type : Lean.Expr) : Lean.Expr × Lean.Expr :=
    match type with
    | .forallE name domain body binder =>
      let (rest, proof) := weaken body
      (.forallE name domain rest binder, .lam name domain proof binder)
    | _ => (mkConst ``True, mkConst ``True.intro)
  let (weakType, weakProof) := weaken info.type
  liftCoreM <| addDecl (.thmDecl {{name := `{FIXTURE}.weakened, levelParams := info.levelParams, type := weakType, value := weakProof}})
  liftCoreM <| addDecl (.axiomDecl {{name := `{FIXTURE}.forbiddenAxiom, levelParams := info.levelParams, type := info.type, isUnsafe := false}})
  liftCoreM <| addDecl (.thmDecl {{name := `{FIXTURE}.forgedSoundness, levelParams := info.levelParams, type := info.type, value := mkConst `{FIXTURE}.forbiddenAxiom}})
end {FIXTURE}
''')
        environment = os.environ.copy()
        environment["LEAN_PATH"] = str(imports)
        run(["lake", "env", "lean", "-D", "Elab.async=false", "--root", str(source.parent),
             "-o", str(imports / "ScalarAuditFixtures.olean"), str(source)], environment)

        def export(filename: str, roots: list[str], module: str = "ScalarAuditFixtures") -> Path:
            path = output / filename
            path.write_text(run(["lake", "env", "leanexport", module, "--", *roots], environment))
            return path

        baseline = export("baseline-model.ndjson", [SOUNDNESS, COMPLETENESS,
            "propext", "Classical.choice", "Quot.sound"], "Noctium.Verification.ScalarCircuitWitness")
        trusted = output / "trusted-model.ndjson"
        trusted.write_bytes(args.trusted_model_export.read_bytes() if args.trusted_model_export else baseline.read_bytes())
        pin = args.trusted_model_sha256 or hashlib.sha256(trusted.read_bytes()).hexdigest()
        (output / "trusted-model.sha256").write_text(pin + "\n")
        positive = export("proofs.ndjson", [f"{FIXTURE}.soundness", f"{FIXTURE}.completeness"])

        def audit(path: Path, soundness: str = f"{FIXTURE}.soundness",
                  completeness: str = f"{FIXTURE}.completeness", expected_error: str | None = None,
                  digest: str = pin) -> dict:
            checked = subprocess.run(["python3", "scripts/proofs/audit-scalar-proof.py",
                "--model-export", str(trusted), "--proof-export", str(path),
                "--trusted-model-sha256", digest, "--soundness-proof", soundness,
                "--completeness-proof", completeness], cwd=ROOT, capture_output=True, text=True,
                timeout=240)
            result = json.loads(checked.stdout)
            if expected_error:
                assert checked.returncode != 0 and expected_error in result["error"], result
            else:
                assert checked.returncode == 0, result
                assert result["wholeCompilerVerified"] is False and result["compilerBuildAuthenticated"] is False
                assert set(result["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"}
            return result

        reports = {"accepted": audit(positive)}
        reports["swapped"] = audit(positive, f"{FIXTURE}.completeness", f"{FIXTURE}.soundness", "wrong_statement")
        missing = export("missing-completeness.ndjson", [f"{FIXTURE}.soundness"])
        reports["missing"] = audit(missing, expected_error="missing_proof: completeness")
        weak = export("weakened.ndjson", [f"{FIXTURE}.weakened", f"{FIXTURE}.completeness"])
        reports["weakened"] = audit(weak, f"{FIXTURE}.weakened", expected_error="wrong_statement: soundness")
        forged = export("forbidden-axiom.ndjson", [f"{FIXTURE}.forgedSoundness", f"{FIXTURE}.completeness"])
        reports["forbiddenAxiom"] = audit(forged, f"{FIXTURE}.forgedSoundness", expected_error="forbidden_axiom")
        reports["wrongPin"] = audit(positive, expected_error="model_pin_mismatch", digest="0" * 64)
        oversized = scratch / "oversized.ndjson"
        with oversized.open("wb") as handle:
            handle.truncate(161 * 1024 * 1024)
        reports["oversized"] = audit(oversized, expected_error="export_limit")
        fifo = scratch / "candidate.fifo"
        os.mkfifo(fifo)
        reports["fifo"] = audit(fifo, expected_error="export_not_regular_file")
        run(["lake", "env", "leanchecker", "--from-export", str(positive)])
        summary = {"status": "passed", "scope": "scalar circuit lowering proof roles and transitive axiom policy",
            "externalReviewedModelProvided": bool(args.trusted_model_export),
            "trustedModelSha256": pin, "soundnessRole": SOUNDNESS, "completenessRole": COMPLETENESS,
            "rejections": ["swapped", "missing", "weakened", "forbiddenAxiom", "wrongPin", "oversized", "fifo"],
            "compilerBuildAuthenticated": False, "wholeCompilerVerified": False, "reports": reports}
        (output / "summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
        print(json.dumps(summary, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
