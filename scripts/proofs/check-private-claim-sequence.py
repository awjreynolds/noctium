#!/usr/bin/env python3
"""Compare fresh PrivateClaim source execution with the 3.2.1 native state trace."""
from __future__ import annotations
import argparse
import base64
import hashlib
import json
import os
import re
import subprocess
import tarfile
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TARBALL_SHA256 = "f2f4d6c1aaa85e2d9cec1c9f204f4f47ae5c7650ef170a68b1675441ea037133"
CHECKER_WASM_SHA256 = "3568fafaf225469dbbd038b0236d1b6b76e0da19da565caba33efe2ceb682cfc"
NATIVE_ZKIR_SHA256 = "7396c9a368e70fb66cb91f39d1508c9f983cacc8d3bc27f7a94e12d9fe327c40"
SOURCE_PATHS = ["examples/PrivateClaim.lean", "proofs/PrivateClaim.lean"]
APPROVED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


class CheckFailure(Exception):
    def __init__(self, classification: str, boundary: str, step: int = 1, field: str = "check") -> None:
        super().__init__(classification)
        self.classification, self.boundary, self.step, self.field = classification, boundary, step, field


def digest(path: Path, algorithm: str = "sha256") -> str:
    h = hashlib.new(algorithm)
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def run(args: list[str], cwd: Path, *, timeout: int = 240, allow_failure: bool = False) -> subprocess.CompletedProcess[str]:
    try:
        result = subprocess.run(args, cwd=cwd, capture_output=True, text=True, timeout=timeout)
    except (OSError, subprocess.TimeoutExpired) as error:
        raise CheckFailure("infrastructure-failure", "command-start-or-timeout") from error
    if result.returncode and not allow_failure:
        raise CheckFailure("infrastructure-failure", "command-result")
    return result


def verify_tar_package(tarball: Path, package_dir: Path, boundary: str) -> None:
    try:
        with tarfile.open(tarball, "r:gz") as archive:
            expected: set[str] = set()
            for member in archive.getmembers():
                if not member.isfile() or not member.name.startswith("package/"):
                    continue
                relative = member.name.removeprefix("package/")
                parts = Path(relative).parts
                if not parts or ".." in parts:
                    raise CheckFailure("infrastructure-failure", boundary)
                expected.add(Path(*parts).as_posix())
                extracted = archive.extractfile(member)
                path = package_dir / Path(*parts)
                if extracted is None or not path.is_file() or path.read_bytes() != extracted.read():
                    raise CheckFailure("infrastructure-failure", boundary, field=relative)
            actual = {path.relative_to(package_dir).as_posix() for path in package_dir.rglob("*") if path.is_file()}
            if not expected or actual != expected:
                raise CheckFailure("infrastructure-failure", boundary, field="package-file-set")
    except (OSError, tarfile.TarError) as error:
        raise CheckFailure("infrastructure-failure", boundary) from error


def source_fixture(values: dict[str, object]) -> str:
    keys = ["secret", "campaign", "sibling0", "sibling1", "leaf", "node", "root", "nullifier", "unrelatedKey"]
    n = {key: int(values[key]) for key in keys}
    d0, d1 = int(values["direction0"]), int(values["direction1"])
    left0, right0 = ((n["sibling0"], n["leaf"]) if d0 else (n["leaf"], n["sibling0"]))
    left1, right1 = ((n["sibling1"], n["node"]) if d1 else (n["node"], n["sibling1"]))
    return f'''import proofs.PrivateClaim
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
open Noctium Noctium.PrivateClaimProofs
namespace PrivateClaimSequenceSourceCheck
def secret : Nat := {n["secret"]}
def campaign : Nat := {n["campaign"]}
def sibling0 : Nat := {n["sibling0"]}
def sibling1 : Nat := {n["sibling1"]}
def leaf : Nat := {n["leaf"]}
def node : Nat := {n["node"]}
def root : Nat := {n["root"]}
def nullifier : Nat := {n["nullifier"]}
def unrelatedKey : Nat := {n["unrelatedKey"]}
def fixtureContext : EvalContext := {{
  modulus := Field.modulus
  poseidon2 := fun domain left right =>
    if domain == 1 && left == secret && right == campaign then .ok leaf
    else if domain == 2 && left == {left0} && right == {right0} then .ok node
    else if domain == 2 && left == {left1} && right == {right1} then .ok root
    else if domain == 3 && left == secret && right == campaign then .ok nullifier
    else .error "unexpected synthetic fixture hash request"
}}
def fixtureInput : InputValues := {{
  root := root, campaign := campaign, nullifier := nullifier, secret := secret,
  sibling0 := sibling0, sibling1 := sibling1,
  direction0 := decide ({d0} = 1), direction1 := decide ({d1} = 1)
}}
def fixtureState : LedgerState := state root campaign [(unrelatedKey, Bool.true)]
def acceptedState : LedgerState := recorded root campaign nullifier [(unrelatedKey, Bool.true)]
theorem sourceEffectOrder : claimEntry.effects = [
    .readCell "acceptedRoot" "storedRoot" .native,
    .require (.eq (.ref "storedRoot" : Expr .native) (.ref "root")),
    .readCell "campaignId" "storedCampaign" .native,
    .require (.eq (.ref "storedCampaign" : Expr .native) (.ref "campaign")),
    .requireAbsent "spent" .native (.ref "nullifier"),
    .writeMap "spent" .native .bool (.ref "nullifier") (.bool Bool.true)] := by rfl
theorem sourceAccepted :
    claimEntry.run fixtureContext (inputEnvironment fixtureInput) fixtureState =
      .ok ([ ("nullifier", .native nullifier) ], acceptedState) := by with_unfolding_all rfl
theorem sourceReplayRejected :
    claimEntry.run fixtureContext (inputEnvironment fixtureInput) acceptedState =
      .error "state map key already present" := by with_unfolding_all rfl
#print axioms sourceEffectOrder
#print axioms sourceAccepted
#print axioms sourceReplayRejected
end PrivateClaimSequenceSourceCheck
'''


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake-cache-root", type=Path, required=True)
    parser.add_argument("--noctium", type=Path, required=True)
    parser.add_argument("--native-zkir", type=Path, required=True)
    parser.add_argument("--checker-package", type=Path, required=True)
    parser.add_argument("--checker-tarball", type=Path, required=True)
    parser.add_argument("--ledger-package", type=Path, required=True)
    parser.add_argument("--ledger-tarball", type=Path, required=True)
    a = parser.parse_args()
    for name in ["lake_cache_root", "noctium", "native_zkir", "checker_package", "checker_tarball", "ledger_package", "ledger_tarball"]:
        setattr(a, name, getattr(a, name).resolve())
    try:
        paths = [str(path.relative_to(ROOT)) for path in (ROOT / "Noctium").rglob("*.lean")] + SOURCE_PATHS
        for source in paths:
            if (ROOT / source).read_bytes() != (a.lake_cache_root / source).read_bytes():
                raise CheckFailure("infrastructure-failure", "lean-cache-source-mismatch", field=source)

        checker_metadata = json.loads((a.checker_package / "package.json").read_text())
        ledger_metadata = json.loads((a.ledger_package / "package.json").read_text())
        lock = json.loads((ROOT / "scripts/zkir/package-lock.json").read_text())
        if checker_metadata.get("version") != "3.2.1" or digest(a.checker_tarball) != TARBALL_SHA256:
            raise CheckFailure("infrastructure-failure", "official-checker-pin")
        verify_tar_package(a.checker_tarball, a.checker_package, "official-checker-package-members")
        wasm = a.checker_package / "midnight_zkir_wasm_bg.wasm"
        wasm_sha = digest(wasm)
        if wasm_sha != CHECKER_WASM_SHA256:
            raise CheckFailure("infrastructure-failure", "official-checker-wasm")
        sri = lock["packages"]["node_modules/@midnight-ntwrk/ledger-v9"]["integrity"].removeprefix("sha512-")
        actual_sri = base64.b64encode(hashlib.sha512(a.ledger_tarball.read_bytes()).digest()).decode()
        if ledger_metadata.get("version") != "1.0.2" or actual_sri != sri:
            raise CheckFailure("infrastructure-failure", "ledger-package-pin")
        verify_tar_package(a.ledger_tarball, a.ledger_package, "ledger-package-members")
        if digest(a.native_zkir) != NATIVE_ZKIR_SHA256:
            raise CheckFailure("infrastructure-failure", "native-zkir-pin")
        checker = a.checker_package / "midnight_zkir_wasm_fs.js"
        ledger_module = a.ledger_package / "midnight_ledger_wasm_v9_fs.js"
        if not checker.is_file() or not ledger_module.is_file():
            raise CheckFailure("infrastructure-failure", "pinned-module-missing")

        with tempfile.TemporaryDirectory(prefix="noctium-private-claim-sequence-") as temp:
            scratch = Path(temp)
            fixture = scratch / "fixture.json"
            prep = run(["node", str(ROOT / "tests/private-claim-sequence-checker.mjs"), "prepare",
                        str(ledger_module), str(fixture)], ROOT)
            if prep.stdout or not fixture.is_file():
                raise CheckFailure("infrastructure-failure", "fixture-preparation")
            values = json.loads(fixture.read_text())

            imports = scratch / "imports"
            (imports / "examples").mkdir(parents=True)
            (imports / "proofs").mkdir(parents=True)
            wrap = 'LEAN_PATH="$1:$LEAN_PATH"; export LEAN_PATH; shift; exec "$@"'
            for source, output in [("examples/PrivateClaim.lean", imports / "examples/PrivateClaim.olean"),
                                   ("proofs/PrivateClaim.lean", imports / "proofs/PrivateClaim.olean")]:
                run(["lake", "env", "sh", "-c", wrap, "sh", str(imports), "lean", "-D", "Elab.async=false",
                     "-o", str(output), source], a.lake_cache_root)
            source_path = scratch / "PrivateClaimSequenceSourceCheck.lean"
            source_path.write_text(source_fixture(values))
            proof = run(["lake", "env", "sh", "-c", wrap, "sh", str(imports), "lean", "-D", "Elab.async=false",
                         str(source_path)], a.lake_cache_root, allow_failure=True)
            if proof.returncode:
                combined = proof.stdout + proof.stderr
                if "unknown module" in combined or "unknown identifier" in combined:
                    raise CheckFailure("infrastructure-failure", "source-fixture-elaboration")
                raise CheckFailure("candidate-difference", "source-entrypoint", field="fixture-result")
            if "sorryAx" in proof.stdout or "sorryAx" in proof.stderr:
                raise CheckFailure("infrastructure-failure", "source-proof-axioms")
            for root in ["sourceEffectOrder", "sourceAccepted", "sourceReplayRejected"]:
                name = f"PrivateClaimSequenceSourceCheck.{root}"
                match = re.search(rf"'{re.escape(name)}' depends on axioms: \[(.*?)\]", proof.stdout, re.S)
                if not match:
                    raise CheckFailure("infrastructure-failure", "source-proof-audit", field=root)
                axioms = {item.strip() for item in match.group(1).split(",") if item.strip()}
                if not axioms.issubset(APPROVED_AXIOMS):
                    raise CheckFailure("infrastructure-failure", "source-proof-axioms", field=root)

            emitted = scratch / "emitted"
            compiled = run([str(a.noctium), "compile", "examples/PrivateClaim.lean", "--target",
                            "profiles/midnight-ledger-9-zkir-3.2.1-target.json", "--output", str(emitted)],
                           a.lake_cache_root, allow_failure=True)
            if compiled.returncode:
                raise CheckFailure("candidate-difference", "noctium-emission")
            plan, call = emitted / "PrivateClaim.claim.impact.json", emitted / "PrivateClaim.claim.zkir"
            if not plan.is_file() or not call.is_file():
                raise CheckFailure("candidate-difference", "noctium-output-set")

            native = run([str(a.native_zkir), "mock-compile", str(call)], a.lake_cache_root, allow_failure=True)
            if native.returncode:
                raise CheckFailure("checker-rejection", "native-zkir-3.2.1-mock-compile")
            sample = run(["node", str(ROOT / "tests/private-claim-sequence-checker.mjs"), "compare",
                          str(ledger_module), str(checker), str(plan), str(call), str(fixture)],
                         ROOT, allow_failure=True)
            try:
                report = json.loads(sample.stdout)
            except json.JSONDecodeError as error:
                raise CheckFailure("infrastructure-failure", "native-sample-report") from error
            if sample.returncode or report.get("status") != "passed":
                detail = report.get("firstDivergence") or {}
                raise CheckFailure(report.get("classification", "infrastructure-failure"),
                                   detail.get("boundary", "native-sample"), detail.get("step", 1),
                                   detail.get("field", "sample"))

            summary = {
                "status": "passed",
                "scope": "fresh PrivateClaim source acceptance and replay vs official 3.2.1 Impact/native state trace",
                "sourceTrace": {"effectOrderKernelChecked": True, "acceptedOutputAndSuccessorKernelChecked": True,
                                "sourceReplayRejectedKernelChecked": True},
                "comparison": report["sourceVsNative"],
                "acceptedState": report["acceptedState"],
                "replay": report["replay"],
                "nativeChecker": {"packageVersion": "3.2.1", "wasmSha256": wasm_sha,
                                  "assignmentAccepted": True,
                                  "archiveMemberBytesCompared": True,
                                  "wrongExpectedReadRejected": report["nativeChecker"]["wrongExpectedReadRejected"],
                                  "nativeCliMockCompileAccepted": True},
                "ledgerAdapter": {"packageVersion": ledger_metadata["version"], "lockfileSriValidated": True,
                                  "archiveMemberBytesCompared": True},
                "artifacts": report["artifact"],
                "failureClassification": {"checkerRejectionControl": "wrong expected read",
                                          "candidateDifferenceControl": report["replay"]["controlDivergence"],
                                          "infrastructureFailures": "reported separately"},
                "witnessValuesReported": False,
                "ordinaryAndAssuranceWorkflowsChanged": False,
            }
            print(json.dumps(summary, sort_keys=True))
        return 0
    except CheckFailure as error:
        print(json.dumps({"status": "failed", "classification": error.classification,
                          "firstDivergence": {"boundary": error.boundary, "step": error.step, "field": error.field},
                          "witnessValuesReported": False}, sort_keys=True))
        return 1
    except (OSError, json.JSONDecodeError):
        print(json.dumps({"status": "failed", "classification": "infrastructure-failure",
                          "firstDivergence": {"boundary": "local-inputs", "step": 1, "field": "tool-or-fixture"},
                          "witnessValuesReported": False}, sort_keys=True))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
