import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts/proofs/check-foundation-source-profile.py"
SPEC = importlib.util.spec_from_file_location("foundation_source_profile", SCRIPT)
PROFILE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(PROFILE)


def encoded(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


class FoundationSourceProfileTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.profile, _, self.target = PROFILE.profile_data()

    def operation_fixture(self, operation):
        directory = self.root / operation["operation"].replace(".", "-")
        directory.mkdir()
        contract = operation["contract"]
        entrypoint = operation["entrypoint"]
        circuit_name = f"{contract}.{entrypoint}.zkir"
        plan_name = f"{contract}.{entrypoint}.impact.json"
        target_bytes = (ROOT / self.profile["targetProfile"]["path"]).read_bytes()
        target_profile = json.loads(target_bytes)
        circuit = encoded({"version": {"major": 3, "minor": 2}, "inputs": [], "outputs": [],
                           "instructions": [{"op": "input"}], "do_communications_commitment": True})
        plan = encoded({"schemaVersion": 1, "contractName": contract, "entrypoint": entrypoint,
                        "nativeCircuitFile": circuit_name, "target": self.target["name"],
                        "targetProfile": target_profile, "circuit": {"name": operation["circuit"]}})
        manifest = encoded({
            "schemaVersion": 3, "target": self.target["name"], "targetProfile": target_profile,
            "contracts": [{"name": contract, "entrypoints": [{
                "name": entrypoint, "circuit": operation["circuit"],
                "nativeCircuitFile": circuit_name, "nativePlanFile": plan_name,
                "nativePlanSha256": hashlib.sha256(plan).hexdigest(),
            }]}],
            "artifacts": [{"file": circuit_name, "role": "ledger"},
                          {"file": plan_name, "role": "ledger"}],
        })
        (directory / "noctium.json").write_bytes(manifest)
        (directory / circuit_name).write_bytes(circuit)
        (directory / plan_name).write_bytes(plan)
        return directory

    def report_fixture(self, operation, artifacts):
        roles = PROFILE.expected_roles(operation)
        role_records = [{
            "schemaVersion": 1, "role": identity["role"],
            "obligationDeclaration": identity["obligation"],
            "policyDeclaration": identity["policy"],
            "proofDeclaration": identity["proof"],
            "proposition": f"{identity['obligation']} {identity['policy']}",
            "policyNormalizedProposition": f"{identity['policy']}.subject",
            "axioms": ["propext", "Classical.choice", "Quot.sound"],
        } for identity in roles]
        report = {
            "status": "source-functional-and-scoped-privacy-checked" if operation["operation"] == "PrivateClaim.claim" else "passed",
            "operation": operation["operation"],
            "trustedModelSha256": PROFILE.model_pin(operation),
            "targetProfile": {**self.target},
            "policy": operation["policy"],
            "functionalProof": operation["functionalProof"],
            "privacyProof": operation["privacyProof"],
            "roleRecords": role_records,
            "axioms": ["propext", "Classical.choice", "Quot.sound"],
            "compiledContractVerified": False,
            "specificationReviewVerified": False,
            "sourceAuthorizationCorrespondenceProved": False,
            "externalModelPinChecked": True,
            "operationArtifacts": PROFILE.ARTIFACT_CHECKER["bind_operation"](
                artifacts, ROOT / self.profile["targetProfile"]["path"],
                self.profile["targetProfile"]["sha256"], operation["contract"], operation["entrypoint"]),
        }
        report.update({key: value for key, value in self.profile["privacyObservation"].items()})
        if operation["operation"] == "PrivateClaim.claim":
            report.update(sourceFunctionalChecked=True, sourcePrivacyChecked=True)
            report["specification"] = dict(self.profile["privacyObservation"])
            report["sourceProofCoverage"] = [{
                "schemaVersion": 1, "kind": "source-proof-coverage", "contract": operation["contract"],
                "status": "covered", "sourceProofsRechecked": True,
                "entrypoints": [{"entrypoint": operation["entrypoint"], "index": 0,
                                 "status": "covered", "policyPairing": "matched",
                                 "roles": [{"role": identity["role"], "status": "covered",
                                            "duplicateRegistrationCount": 0,
                                            "registrations": [{"policy": identity["policy"],
                                                               "proof": identity["proof"]}]}
                                           for identity in roles]}],
            }]
            report["selectedOperations"] = [operation["operation"]]
        else:
            report["scope"] = operation["operation"]
            report["operationSubjectCheckedByKernel"] = True
            report["policy"] = operation["policy"]
            report["functionalProof"] = operation["functionalProof"]
            report["privacyProof"] = operation["privacyProof"]
            report["privacyObservation"] = dict(self.profile["privacyObservation"])
            report["targetProfile"]["path"] = self.profile["targetProfile"]["path"]
            report.pop("releasePolicy")
            report.pop("privacyScope")
            report.pop("publicObserver")
            report.pop("publicEquivalence")
            report.pop("privacyDomain")
        return report

    def inputs(self):
        reports = {}
        artifacts = {}
        for operation in self.profile["operations"]:
            artifacts[operation["operation"]] = self.operation_fixture(operation)
            report = self.report_fixture(operation, artifacts[operation["operation"]])
            report_path = self.root / (operation["operation"].replace(".", "-") + ".json")
            report_path.write_bytes(encoded(report))
            reports[operation["operation"]] = report_path
        return reports, artifacts

    def test_accepts_both_actual_report_shapes_and_reports_open_evidence(self):
        reports, artifacts = self.inputs()
        evidence = PROFILE.run_profile(reports, artifacts)
        repeated = PROFILE.run_profile(reports, artifacts)
        self.assertEqual(evidence["status"], "source-evidence-checked")
        self.assertEqual([item["operation"] for item in evidence["operations"]],
                         PROFILE.EXPECTED_OPERATIONS)
        self.assertEqual(len(evidence["openRequirements"]), 8)
        self.assertIn("independent-review", {item["name"] for item in evidence["openRequirements"]})
        self.assertEqual(PROFILE.render_json(evidence), PROFILE.render_json(repeated))
        self.assertEqual(PROFILE.render_text(evidence), PROFILE.render_text(repeated))

    def test_rejects_crossed_duplicate_observer_pin_and_artifact_evidence(self):
        reports, artifacts = self.inputs()
        private_path = reports["PrivateClaim.claim"]
        original = json.loads(private_path.read_text())
        cases = [
            (lambda value: value.update(operation="BoundedScalars.apply"), "crossed_source_operation"),
            (lambda value: value["roleRecords"].append(copy.deepcopy(value["roleRecords"][0])),
             "required_role_records_missing_or_duplicated"),
            (lambda value: value["specification"].update(publicObserver="altered"),
             "privacy_observation_mismatch:publicObserver"),
            (lambda value: value.update(trustedModelSha256="0" * 64), "fixture_model_pin_mismatch"),
            (lambda value: value["operationArtifacts"]["artifacts"][0].update(sha256="0" * 64),
             "reported_operation_artifact_identity_mismatch"),
        ]
        for mutate, error in cases:
            with self.subTest(error=error):
                candidate = copy.deepcopy(original)
                mutate(candidate)
                private_path.write_bytes(encoded(candidate))
                with self.assertRaisesRegex(ValueError, error):
                    PROFILE.run_profile(reports, artifacts)
        private_path.write_bytes(encoded(original))


if __name__ == "__main__":
    unittest.main()
