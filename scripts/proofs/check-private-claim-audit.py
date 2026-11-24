#!/usr/bin/env python3
"""Fresh actual-source proof exports, exact-policy auditing and stale-source negatives."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
NS = "Noctium.PrivateClaimVerification"
MODULE = "proofs.PrivateClaimVerification"
OPERATION = "PrivateClaim.claim"
TARGET = ROOT / "profiles/midnight-ledger-9-zkir-3.2.1-target.json"
TARGET_PROFILE_SHA256 = "02b4242c2561232daea1d7d1d29bde68f3157eb9eed8cfb037254a0013f40093"
MODEL_PIN = ROOT / "proofs/PrivateClaimVerification.model.sha256"
MODEL_ROOTS = ["Noctium.Verification.FunctionalObligation", "Noctium.Verification.PrivacyObligation",
               f"{NS}.policy"]
AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
OPERATION_ROOTS = ["Noctium.Contract.name", "Noctium.Entrypoint.name"]
SOURCE_COVERAGE_PREFIX = "NOCTIUM_SOURCE_PROOF_COVERAGE "
FUNCTIONAL_OBLIGATION = "Noctium.Verification.FunctionalObligation"
PRIVACY_OBLIGATION = "Noctium.Verification.PrivacyObligation"


def expected_source_operations(metadata: dict) -> list[tuple[str, int, str]]:
    if not isinstance(metadata, dict) or not isinstance(metadata.get("contracts"), list):
        raise ValueError("invalid_compiler_contract_metadata")
    operations = []
    contracts = set()
    for contract in metadata["contracts"]:
        if not isinstance(contract, dict) or not isinstance(contract.get("name"), str):
            raise ValueError("invalid_compiler_contract_metadata")
        contract_name = contract["name"]
        if contract_name in contracts:
            raise ValueError(f"duplicate_compiler_contract: {contract_name}")
        contracts.add(contract_name)
        entrypoints = contract.get("entrypoints")
        if not isinstance(entrypoints, list):
            raise ValueError(f"invalid_compiler_entrypoints: {contract_name}")
        names = set()
        for index, entrypoint in enumerate(entrypoints):
            if not isinstance(entrypoint, dict) or not isinstance(entrypoint.get("name"), str):
                raise ValueError(f"invalid_compiler_entrypoint: {contract_name}")
            name = entrypoint["name"]
            if name in names:
                raise ValueError(f"duplicate_compiler_entrypoint: {contract_name}.{name}")
            names.add(name)
            operations.append((contract_name, index, name))
    if not operations:
        raise ValueError("compiler_metadata_has_no_entrypoints")
    return operations


def validate_source_coverage(operations: list[tuple[str, int, str]], reports: list[dict]) -> list[str]:
    expected: dict[str, list[tuple[int, str]]] = {}
    for contract, index, entrypoint in operations:
        expected.setdefault(contract, []).append((index, entrypoint))
    report_by_contract = {}
    for report in reports:
        if not isinstance(report, dict) or not isinstance(report.get("contract"), str):
            raise ValueError("invalid_source_proof_coverage_report")
        contract = report["contract"]
        if contract in report_by_contract:
            raise ValueError(f"duplicate_source_proof_coverage_report: {contract}")
        report_by_contract[contract] = report
    if set(report_by_contract) != set(expected):
        missing = sorted(set(expected) - set(report_by_contract))
        extra = sorted(set(report_by_contract) - set(expected))
        raise ValueError(f"source_proof_coverage_contract_mismatch: missing={missing}, extra={extra}")

    for contract, entries in expected.items():
        report = report_by_contract[contract]
        if (report.get("schemaVersion") != 1 or report.get("kind") != "source-proof-coverage"
                or report.get("status") != "covered"
                or report.get("sourceProofsRechecked") is not True):
            raise ValueError(f"invalid_source_proof_coverage_report: {contract}")
        rows = report.get("entrypoints")
        if not isinstance(rows, list):
            raise ValueError(f"invalid_source_proof_coverage_rows: {contract}")
        row_names = []
        rows_by_name = {}
        for row in rows:
            if not isinstance(row, dict) or not isinstance(row.get("entrypoint"), str):
                raise ValueError(f"invalid_source_proof_coverage_row: {contract}")
            name = row["entrypoint"]
            if name in rows_by_name:
                raise ValueError(f"duplicate_source_proof_entrypoint: {contract}.{name}")
            row_names.append(name)
            rows_by_name[name] = row
        expected_names = [name for _, name in entries]
        missing = sorted(set(expected_names) - set(row_names))
        extra = sorted(set(row_names) - set(expected_names))
        if missing or extra:
            raise ValueError(f"source_proof_coverage_scope_mismatch: {contract}: missing={missing}, extra={extra}")
        for index, name in entries:
            row = rows_by_name[name]
            if row.get("index") != index:
                raise ValueError(f"source_proof_coverage_index_mismatch: {contract}.{name}")
            if row.get("status") != "covered" or row.get("policyPairing") != "matched":
                raise ValueError(f"source_proof_coverage_incomplete: {contract}.{name}")
            roles = row.get("roles")
            if not isinstance(roles, list) or any(not isinstance(role, dict) for role in roles):
                raise ValueError(f"invalid_source_proof_coverage_roles: {contract}.{name}")
            role_names = [role.get("role") for role in roles]
            if any(not isinstance(role_name, str) for role_name in role_names):
                raise ValueError(f"invalid_source_proof_coverage_roles: {contract}.{name}")
            for role in ("functional", "privacy"):
                if role_names.count(role) == 0:
                    raise ValueError(f"missing_source_proof_role: {contract}.{name}.{role}")
                if role_names.count(role) > 1:
                    raise ValueError(f"duplicate_source_proof_role: {contract}.{name}.{role}")
            if set(role_names) != {"functional", "privacy"}:
                raise ValueError(f"unexpected_source_proof_role: {contract}.{name}")
            for role in roles:
                role_name = role["role"]
                registrations = role.get("registrations")
                if (role.get("status") != "covered" or role.get("duplicateRegistrationCount") != 0
                        or not isinstance(registrations, list) or len(registrations) != 1):
                    raise ValueError(f"source_proof_role_not_unique_and_covered: {contract}.{name}.{role_name}")
    return [f"{contract}.{entrypoint}" for contract, _, entrypoint in operations]


def run(args: list[str], env: dict[str, str] | None = None, stdin: str | None = None) -> str:
    result = subprocess.run(args, cwd=ROOT, env=env, input=stdin, capture_output=True, text=True, timeout=240)
    if result.returncode:
        raise AssertionError(f"command failed: {args}\n{result.stdout}\n{result.stderr}")
    return result.stdout


def direct_axioms(report: str, proof: str) -> list[str]:
    match = re.search(rf"^{re.escape(repr(proof))} depends on axioms: \[(.*?)\]$",
                      report, re.MULTILINE)
    if match is None:
        raise AssertionError(f"missing fresh Lean axiom output for {proof}")
    return [item.strip() for item in match.group(1).split(",") if item.strip()]


def validate_role_records(result: dict, report: str, roles: list[tuple[str, str, str]]) -> None:
    records = result.get("roleRecords")
    if not isinstance(records, list) or len(records) != len(roles):
        raise AssertionError(f"wrong source proof role record count: {result}")
    aggregate = set()
    for record, (role, obligation, proof) in zip(records, roles, strict=True):
        if (record.get("schemaVersion") != 1 or record.get("role") != role
                or record.get("obligationDeclaration") != obligation
                or record.get("policyDeclaration") != f"{NS}.policy"
                or record.get("proofDeclaration") != proof
                or record.get("proposition") != f"{obligation} {NS}.policy"
                or not isinstance(record.get("policyNormalizedProposition"), str)
                or f"{NS}.policy" not in record["policyNormalizedProposition"]):
            raise AssertionError(f"invalid {role} role record: {record}")
        actual = record.get("axioms")
        expected = direct_axioms(report, proof)
        if actual != expected or len(actual) != len(set(actual)):
            raise AssertionError(
                f"{role} axiom record differs from fresh Lean closure: actual={actual}, expected={expected}")
        aggregate.update(actual)
    reported_aggregate = result.get("axioms")
    if (not isinstance(reported_aggregate, list)
            or len(reported_aggregate) != len(set(reported_aggregate))
            or set(reported_aggregate) != aggregate):
        raise AssertionError("aggregate axiom identity changed from role records")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--report", action="store_true", help="print the checked source report as JSON")
    parser.add_argument("--proof-export", type=Path, help="candidate data export for --report")
    parser.add_argument("--trusted-model-export", type=Path)
    parser.add_argument("--trusted-model-sha256")
    args = parser.parse_args()
    if bool(args.trusted_model_export) != bool(args.trusted_model_sha256):
        parser.error("external model export and SHA256 must be supplied together")
    if args.report and args.trusted_model_export:
        parser.error("--report uses the checked-in fixture model pin")
    if args.proof_export and not args.report:
        parser.error("--proof-export requires --report")
    run(["lake", "build", "Noctium", "Noctium.Cli", "Noctium.Compiler", "Noctium.Frontend",
         "Noctium.Verification.ExportAudit"])
    with tempfile.TemporaryDirectory(prefix="noctium-private-claim-audit-") as directory:
        scratch = Path(directory)
        default_output = scratch / "evidence" if args.report else ROOT / ".noctium/audits/private-claim-source"
        output = (args.output_dir or default_output).resolve()
        output.mkdir(parents=True, exist_ok=True)
        imports = scratch / "imports"
        for subdir in ["examples", "proofs"]:
            (imports / subdir).mkdir(parents=True)
        environment = os.environ.copy()
        environment.pop("LEAN_PATH", None)
        lake_import_path = run(["lake", "env", "printenv", "LEAN_PATH"], environment).strip()
        # Lake puts its own cache before inherited LEAN_PATH. Apply the fresh
        # audit path after entering Lake's environment so it takes precedence.
        audit_import_path = os.pathsep.join((str(imports), lake_import_path))
        audit_tool = ["lake", "env", "env", f"LEAN_PATH={audit_import_path}"]

        def build(path: str, source: str | None = None) -> str:
            command = [*audit_tool, "lean", "-D", "Elab.async=false", "-o",
                       str(imports / Path(path).with_suffix(".olean"))]
            if source is not None and not (ROOT / path).exists():
                candidate = scratch / "source" / path
                candidate.parent.mkdir(parents=True, exist_ok=True)
                candidate.write_text(source)
                command += ["--root", str(scratch / "source"), str(candidate)]
                return run(command, environment)
            command += (["--stdin", path] if source is not None else [path])
            return run(command, environment, source)

        def export(filename: str, roots: list[str], module: str = MODULE) -> Path:
            contents = run([*audit_tool, "leanexport", module, "--", *roots], environment)
            destination = output / filename
            destination.write_text(contents)
            return destination

        build("examples/PrivateClaim.lean")
        build("proofs/PrivateClaim.lean")
        report = build("proofs/PrivateClaimVerification.lean")
        (output / "direct-axioms.txt").write_text(report)
        assert report.count("depends on axioms: [propext, Classical.choice, Quot.sound]") == 2, report
        selected_operations = []
        source_coverage = []
        if args.report:
            compiler_output = scratch / "compiler-artifacts"
            run(["lake", "env", "lean", "--run", "NoctiumMain.lean", "compile",
                 "examples/PrivateClaim.lean",
                 "--target", str(TARGET), "--emit", "ledger", "--output", str(compiler_output)])
            profile_bytes = TARGET.read_bytes()
            profile_sha256 = hashlib.sha256(profile_bytes).hexdigest()
            if profile_sha256 != TARGET_PROFILE_SHA256:
                parser.exit(1, f"{OPERATION}: target profile pin mismatch\n")
            metadata = json.loads((compiler_output / "noctium.json").read_text())
            operations = expected_source_operations(metadata)
            contract_names = list(dict.fromkeys(contract for contract, _, _ in operations))
            coverage_source = ("import proofs.PrivateClaimVerification\n"
                               "import Noctium.Verification\n"
                               "open Noctium Noctium.Verification\n" +
                               "".join(f"#noctium_source_proof_coverage {contract}\n"
                                       for contract in contract_names))
            coverage_output = build("proofs/PrivateClaimSourceCoverageReport.lean", coverage_source)
            try:
                source_coverage = [json.loads(line.split(SOURCE_COVERAGE_PREFIX, 1)[1])
                                   for line in coverage_output.splitlines()
                                   if SOURCE_COVERAGE_PREFIX in line]
                selected_operations = validate_source_coverage(operations, source_coverage)
            except ValueError as error:
                parser.exit(1, f"{OPERATION}: {error}\n")
            contract, entrypoint = OPERATION.split(".", 1)
            association = json.loads(run([
                "python3", "scripts/proofs/check-source-operation-artifacts.py",
                "--artifacts", str(compiler_output), "--profile", str(TARGET),
                "--profile-sha256", TARGET_PROFILE_SHA256,
                "--contract", contract, "--entrypoint", entrypoint,
            ]))
            if (association.get("status") != "operation-artifacts-associated"
                    or association.get("operation", {}).get("contract") != contract
                    or association.get("operation", {}).get("entrypoint") != entrypoint):
                parser.exit(1, f"{OPERATION}: operation artifact association mismatch\n")
        if not args.report:
            negative = '''import proofs.PrivateClaimVerification
open Noctium Noctium.Verification Noctium.PrivateClaimVerification
namespace PrivateClaimAuditNegative
def wrongPolicy : AuditPolicy :=
  {policy with subject := {subject with specification := {specification with postcondition := fun _ _ _ _ _ => True}}}
axiom forbiddenFunctional : FunctionalObligation policy
end PrivateClaimAuditNegative
'''
            build("proofs/PrivateClaimAuditNegative.lean", negative)
            roots = [*MODEL_ROOTS, "PrivateClaimAuditNegative.wrongPolicy", *AXIOMS]
            baseline = export("baseline-model.ndjson", roots, "proofs.PrivateClaimAuditNegative")
        else:
            baseline = export("baseline-model.ndjson", [*MODEL_ROOTS, *OPERATION_ROOTS, *AXIOMS])
        proof = (args.proof_export.resolve() if args.proof_export
                 else export("proofs.ndjson", [f"{NS}.functional", f"{NS}.privacy"]))
        # Retain reviewed input bytes before the external driver reads them. A local
        # regression baseline is not an independent review of the business specification.
        model = output / "trusted-model.ndjson"
        model.write_bytes(args.trusted_model_export.read_bytes() if args.trusted_model_export else baseline.read_bytes())
        pin = args.trusted_model_sha256
        if pin is None:
            pin = MODEL_PIN.read_text().strip() if args.report else hashlib.sha256(model.read_bytes()).hexdigest()
        (output / "trusted-model.sha256").write_text(pin + "\n")

        def audit(candidate: Path, expected_error: str | None = None,
                  policy: str = f"{NS}.policy", functional_proof: str = f"{NS}.functional",
                  privacy_proof: str | None = f"{NS}.privacy") -> dict:
            command = ["python3", "scripts/proofs/audit-source-proof.py", "--model-export", str(model),
                       "--proof-export", str(candidate), "--trusted-model-sha256", pin,
                       "--policy", policy, "--functional-proof", functional_proof]
            if privacy_proof is not None:
                command.extend(["--privacy-proof", privacy_proof])
            checked = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=240)
            result = json.loads(checked.stdout)
            if args.report and checked.returncode != 0 and not expected_error:
                parser.exit(1, f"{OPERATION}: {result['error']}\n")
            if expected_error:
                assert checked.returncode != 0 and expected_error in result["error"], result
            else:
                assert checked.returncode == 0, result
                assert result["compiledContractVerified"] is False, result
                assert result["sourceFunctionalChecked"] is True, result
                assert result["sourcePrivacyChecked"] is (privacy_proof is not None), result
                assert set(result["axioms"]) <= set(AXIOMS), result
            return result

        accepted = audit(proof)
        validate_role_records(accepted, report, [
            ("functional", FUNCTIONAL_OBLIGATION, f"{NS}.functional"),
            ("privacy", PRIVACY_OBLIGATION, f"{NS}.privacy"),
        ])
        (output / "audit.json").write_text(json.dumps(accepted, indent=2, sort_keys=True) + "\n")
        functional_only = export("functional-only-proofs.ndjson", [f"{NS}.functional"])
        single_role = audit(functional_only, privacy_proof=None)
        validate_role_records(single_role, report, [
            ("functional", FUNCTIONAL_OBLIGATION, f"{NS}.functional"),
        ])
        if args.report:
            if (accepted.get("operation") != OPERATION
                    or accepted.get("operation") not in selected_operations
                    or accepted.get("sourceFunctionalChecked") is not True
                    or accepted.get("sourcePrivacyChecked") is not True):
                parser.exit(1, f"{OPERATION}: unexpected checked subject or proof roles\n")
            accepted["selectedOperations"] = selected_operations
            accepted["sourceProofCoverage"] = source_coverage
            specification = accepted["specification"]
            for key in ("initial", "invariant", "precondition", "enabled", "postcondition", "releaseDefinition"):
                del specification[key]
            profile = json.loads(profile_bytes)
            accepted.update(schemaVersion=1, targetProfile={
                "name": profile["name"], "ledger": profile["ledger"], "zkir": profile["zkir"],
                "sha256": profile_sha256,
            })
            accepted["operationArtifacts"] = association
            print(json.dumps(accepted, indent=2, sort_keys=True))
            return 0
        run([*audit_tool, "leanchecker", "--from-export", str(proof)], environment)
        if not args.trusted_model_export:
            wrong_policy = audit(proof, "wrong_obligation", "PrivateClaimAuditNegative.wrongPolicy")
            (output / "wrong-policy-rejection.json").write_text(json.dumps(wrong_policy, indent=2) + "\n")
            forged = export("forbidden-axiom.ndjson",
                            ["PrivateClaimAuditNegative.forbiddenFunctional"],
                            "proofs.PrivateClaimAuditNegative")
            forbidden = audit(forged, "forbidden_axiom",
                              functional_proof="PrivateClaimAuditNegative.forbiddenFunctional",
                              privacy_proof=None)
            (output / "forbidden-axiom-rejection.json").write_text(
                json.dumps(forbidden, indent=2) + "\n")
        # Deliberately stale proof objects plus a freshly compiled changed actual
        # source relation. Exact retained-model identity must reject before replay.
        source = (ROOT / "examples/PrivateClaim.lean").read_text()
        guard = "    require eq(storedRoot, root)\n"
        assert source.count(guard) == 1
        build("examples/PrivateClaim.lean", source.replace(guard, ""))
        changed = export("changed-source-stale-proofs.ndjson", [f"{NS}.functional", f"{NS}.privacy"])
        rejected = audit(changed, "model_declaration_mismatch: PrivateClaim")
        (output / "changed-source-rejection.json").write_text(json.dumps(rejected, indent=2) + "\n")
        summary = {"status": "passed", "scope": "actual PrivateClaim source functional and successful-only privacy obligations",
                   "modelSha256": pin, "externalModelSupplied": bool(args.trusted_model_export),
                   "specificationReviewVerified": False, "compiledContractVerified": False,
                   "retainedArtifacts": str(output), "axioms": accepted["axioms"]}
        (output / "summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
        print(json.dumps(summary, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
