#!/usr/bin/env python3
"""Check actual claim scalar/hash lowering proofs and fresh JSON-tree certificates."""
from __future__ import annotations
import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
NS = "Noctium.PrivateClaimLowering"
PROOF_ROOTS = [f"{NS}.{name}" for name in [
    "native_constraints_sound", "native_constraints_pruned_sound", "source_acceptance_complete",
    "eligible_source_complete", "decoded_constraints_sound", "decoded_eligible_constraints_complete",
    "fixture_native_nonvacuity"]]
APPROVED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def run(args: list[str], env: dict[str, str] | None = None, *, allow_failure: bool = False) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(args, cwd=ROOT, env=env, capture_output=True, text=True, timeout=240)
    if result.returncode and not allow_failure:
        raise AssertionError(f"command failed: {args}\n{result.stdout}\n{result.stderr}")
    return result


def quote_tree(value: object) -> str:
    """Generate an untrusted candidate literal. The kernel checks its decoding.

    Python's byte-to-tree parser is not proved by this certificate. Record the
    original bytes and their digest separately for the later artifact boundary.
    """
    if value is None:
        return "Lean.Json.null"
    if isinstance(value, bool):
        return "Lean.Json.bool " + ("_root_.Bool.true" if value else "_root_.Bool.false")
    if isinstance(value, int):
        if value < 0:
            raise ValueError("negative JSON number in expected native artifact")
        return f"Lean.toJson ({value} : Nat)"
    if isinstance(value, str):
        return "Lean.Json.str " + json.dumps(value, ensure_ascii=False)
    if isinstance(value, list):
        return "Lean.Json.arr #[" + ", ".join(quote_tree(item) for item in value) + "]"
    if isinstance(value, dict):
        return "Lean.Json.mkObj [" + ", ".join(
            "(" + json.dumps(key, ensure_ascii=False) + ", " + quote_tree(item) + ")"
            for key, item in value.items()) + "]"
    raise TypeError(type(value))


def certificate_source(tree: object, namespace: str) -> str:
    return f'''import proofs.PrivateClaimLowering
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace {namespace}
open Noctium Noctium.PrivateClaimProofs Noctium.Verification.NativeRelation Noctium.PrivateClaimLowering
def emittedJson : Lean.Json := {quote_tree(tree)}
theorem decoded : Noctium.Verification.NativeRelationJson.decode emittedJson =
    .ok {NS}.program := by
  have check : (Noctium.Verification.NativeRelationJson.decode emittedJson).toOption =
      some {NS}.program := by decide +kernel
  cases h : Noctium.Verification.NativeRelationJson.decode emittedJson with
  | error message => rw [h] at check; contradiction
  | ok value =>
    rw [h] at check
    exact congrArg Except.ok (Option.some.inj check)
theorem sound (ctx : EvalContext) (hash : Hash) (agreement : HashAgreement ctx hash)
    (input : Inputs) (assignment : Assignment) (groups : List (List Scalar))
    (sat : DecodedCircuitRelation emittedJson hash input.streams assignment groups) :
    claimEntry.circuit.run ctx (inputEnvironment input.source) =
      .ok [("nullifier", .native input.nullifier.val)] ∧
    program.returns assignment = [input.nullifier] ∧
    program.returns assignment = groups.getLastD [] :=
  {NS}.decoded_constraints_sound emittedJson decoded ctx hash agreement input assignment groups sat
 theorem complete (ctx : EvalContext) (hash : Hash) (agreement : HashAgreement ctx hash)
    (input : InputValues) (canonical : CanonicalInputs ctx input) (leaf node : Nat)
    (trace : HashTrace ctx input leaf node) :
    let nativeInputs := Inputs.ofSource ctx input canonical agreement.modulus
    ∃ assignment, DecodedCircuitRelation emittedJson hash nativeInputs.streams assignment
      [[nativeInputs.root], [nativeInputs.campaign], [nativeInputs.nullifier], [nativeInputs.nullifier]] :=
  {NS}.decoded_eligible_constraints_complete emittedJson decoded ctx hash agreement input canonical leaf node trace
#print axioms decoded
#print axioms sound
#print axioms complete
end {namespace}
'''


def exported_axioms(path: Path) -> list[str]:
    """Inspect actual exported axiom declarations, not imported axiom metadata."""
    names = {0: ""}
    axioms = []
    for line in path.read_text().splitlines():
        item = json.loads(line)
        if "in" in item:
            if "str" in item:
                piece = item["str"]
                prefix = names[piece["pre"]]
                names[item["in"]] = (prefix + "." if prefix else "") + piece["str"]
            elif "num" in item:
                piece = item["num"]
                prefix = names[piece["pre"]]
                names[item["in"]] = (prefix + "." if prefix else "") + str(piece["i"])
        if "axiom" in item:
            axiom = item["axiom"]
            name = names[axiom["name"]]
            assert name in APPROVED_AXIOMS and not axiom.get("isUnsafe"), name
            axioms.append(name)
        for kind in ["def", "thm", "opaque"]:
            if kind in item:
                assert not item[kind].get("isUnsafe", False), item[kind]
                assert item[kind].get("safety", "safe") == "safe", item[kind]
    return sorted(set(axioms))


def strict_json_bytes(contents: bytes) -> object:
    def object_pairs(pairs: list[tuple[str, object]]) -> dict:
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"duplicate JSON key: {key}")
            result[key] = value
        return result

    def reject_number(value: str) -> object:
        raise ValueError(f"unsupported non-integer JSON number: {value}")

    def natural_number(value: str) -> int:
        if not value.isascii() or not value.isdecimal():
            raise ValueError(f"unsupported non-natural JSON number: {value}")
        return int(value)

    return json.loads(contents, object_pairs_hook=object_pairs, parse_int=natural_number,
                      parse_float=reject_number, parse_constant=reject_number)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=ROOT / ".noctium/audits/private-claim-lowering")
    args = parser.parse_args()
    for malformed in [b'{"x":1,"x":2}', b'{"x":NaN}', b'{"x":Infinity}',
                      b'{"x":1.0}', b'{"x":1e0}', b'{"x":-0}', b'{"x":-1}']:
        try:
            strict_json_bytes(malformed)
        except ValueError:
            pass
        else:
            raise AssertionError(f"malformed JSON accepted: {malformed!r}")
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    run(["lake", "build", "noctium", "Noctium", "Noctium.Frontend", "Noctium.Verification.NativeRelationJson"])
    run(["lake", "env", "lean", "tests/NativeRelationJson.lean"])
    with tempfile.TemporaryDirectory(prefix="noctium-claim-lowering-") as directory:
        scratch = Path(directory)
        imports = scratch / "imports"
        for child in ["examples", "proofs"]:
            (imports / child).mkdir(parents=True)
        environment = os.environ.copy()
        environment["LEAN_PATH"] = str(imports)
        for source in ["examples/PrivateClaim.lean", "proofs/PrivateClaim.lean", "proofs/PrivateClaimLowering.lean"]:
            built = run(["lake", "env", "lean", "-D", "Elab.async=false", "-o",
                         str(imports / Path(source).with_suffix(".olean")), source], environment)
            if source.endswith("PrivateClaimLowering.lean"):
                (output / "direct-axioms.txt").write_text(built.stdout)
        emitted = output / "emitted"
        run([str(ROOT / ".lake/build/bin/noctium"), "compile", "examples/PrivateClaim.lean",
             "--target", "profiles/midnight-ledger-9-zkir-3.2.1-target.json", "--output", str(emitted)])
        artifact = emitted / "claimRelation.zkir"
        original_bytes = artifact.read_bytes()
        tree = strict_json_bytes(original_bytes)
        assert len(tree["instructions"]) == 27, tree
        source_dir = scratch / "source"
        (source_dir / "proofs").mkdir(parents=True)

        def check_certificate(value: object, filename: str, namespace: str, negative: bool = False) -> str:
            text = certificate_source(value, namespace)
            candidate = source_dir / "proofs" / filename
            candidate.write_text(text)
            (output / filename).write_text(text)
            result = run(["lake", "env", "lean", "-D", "Elab.async=false", "--root", str(source_dir),
                          "-o", str(imports / "proofs" / Path(filename).with_suffix(".olean")), str(candidate)],
                         environment, allow_failure=negative)
            if negative:
                assert result.returncode != 0, filename
                proof_line = next(index for index, line in enumerate(text.splitlines(), 1)
                                  if "some " + NS + ".program := by decide +kernel" in line)
                assert f"{filename}:{proof_line}:" in result.stdout, result.stdout + result.stderr
                assert "decide" in result.stdout and "error:" in result.stdout, result.stdout
                assert "theorems cannot use" not in result.stdout, result.stdout
                assert "unknown module" not in result.stdout and "unknown identifier" not in result.stdout, result.stdout
                (output / (filename + ".rejection.txt")).write_text(result.stdout + result.stderr)
            return result.stdout

        positive = check_certificate(tree, "PrivateClaimEmittedCertificate.lean", "PrivateClaimEmittedCertificate")
        (output / "certificate-axioms.txt").write_text(positive)
        changed_path = copy.deepcopy(tree)
        selector = next(item for item in changed_path["instructions"] if item.get("output") == "%v1")
        selector["a"], selector["b"] = selector["b"], selector["a"]
        check_certificate(changed_path, "WrongPathCertificate.lean", "WrongPathCertificate", negative=True)
        missing_constraint = copy.deepcopy(tree)
        missing_constraint["instructions"].remove({"op": "assert", "cond": "%v7"})
        check_certificate(missing_constraint, "MissingConstraintCertificate.lean", "MissingConstraintCertificate", negative=True)
        roots = PROOF_ROOTS + ["PrivateClaimEmittedCertificate.decoded", "PrivateClaimEmittedCertificate.sound",
                               "PrivateClaimEmittedCertificate.complete"]
        export = run(["lake", "env", "sh", "-c",
                      'LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"; export LEAN_PATH; shift; exec "$@"',
                      "sh", str(imports), "leanexport", "proofs.PrivateClaimEmittedCertificate", "--", *roots], environment)
        exported = output / "proof-closure.ndjson"
        exported.write_text(export.stdout)
        axioms = exported_axioms(exported)
        replay = run(["lake", "env", "leanchecker", "--from-export", str(exported)])
        (output / "kernel-replay.txt").write_text(replay.stdout + replay.stderr)
        summary = {"status": "passed", "scope": "actual claim scalar/Boolean/hash target relation and JSON-tree certificate",
                   "sourceSha256": hashlib.sha256((ROOT / "examples/PrivateClaim.lean").read_bytes()).hexdigest(),
                   "artifactSha256": hashlib.sha256(original_bytes).hexdigest(),
                   "proofExportSha256": hashlib.sha256(exported.read_bytes()).hexdigest(),
                   "axioms": axioms, "mutantsRejected": ["swapped-first-path-selector", "missing-root-assertion"],
                   "kernelReplayed": True, "arbitrarySatisfyingWitnessSoundness": True,
                   "sourceCompleteness": True, "hashAgreementRequired": True,
                   "byteParserCorrespondenceProved": False, "compilerBuildAuthenticated": False,
                   "ledgerStatePreservationProved": False, "compiledContractVerified": False,
                   "retainedArtifacts": str(output)}
        (output / "summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
        print(json.dumps(summary, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
