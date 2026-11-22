#!/usr/bin/env python3
"""Build and independently check exact public PrivateClaim artifact certificates.

Authority preparation requires externally pinned source/model/toolchain inputs.
Candidate manifests never supply their own trust anchor. No invocation inputs
are accepted by this public build pipeline.
"""
from __future__ import annotations

import argparse
import hashlib
import io
import json
import os
from pathlib import Path
import re
import runpy
import shutil
import subprocess
import sys
import tarfile
import tempfile

ROOT = Path(__file__).resolve().parents[2]
HELPERS = runpy.run_path(str(ROOT / "scripts/proofs/check-private-claim-lowering.py"))
ARTIFACTS = ["claimRelation.zkir", "PrivateClaim.claim.impact.json", "PrivateClaim.claim.zkir", "target-profile.json", "noctium.json"]
SOURCE_POLICY = "Noctium.PrivateClaimVerification.policy"
NATIVE_POLICY = "Noctium.PrivateClaimNativePrivacy.policy"
NS = "Noctium.PrivateClaimArtifacts"
CERT = "PrivateClaimArtifactCertificate"
PROFILE = "profiles/midnight-ledger-9-zkir-3.2.1-target.json"
SOURCES = ["examples/PrivateClaim.lean", "proofs/PrivateClaim.lean", "proofs/PrivateClaimVerification.lean",
           "proofs/PrivateClaimLowering.lean", "proofs/PrivateClaimNativeState.lean",
           "proofs/PrivateClaimNativePrivacy.lean", "proofs/PrivateClaimArtifacts.lean"]
MODEL_ROOTS = [f"{NS}.Certified", f"{NS}.FunctionalPreservation", f"{NS}.EligibleCompleteness", f"{NS}.concrete_complete", f"{NS}.concrete_preservation", f"{NS}.concrete_privacy", f"{NS}.exact_byte_build_binding",
    "Noctium.Verification.ArtifactBytes.parse", "Noctium.Verification.ArtifactCertificate.Authenticated",
    "Noctium.Verification.ArtifactCertificate.selectedProfile", NATIVE_POLICY, SOURCE_POLICY,
    "Noctium.PrivateClaimNativePrivacy.NativePrivacyObligation", "Noctium.PrivateClaimNativePrivacy.actualObserve",
    "Noctium.Verification.FunctionalObligation", "Noctium.Verification.PrivacyObligation",
    "propext", "Classical.choice", "Quot.sound"]
BASE_ROOTS = MODEL_ROOTS + [
    "Noctium.PrivateClaimVerification.functional", "Noctium.PrivateClaimVerification.privacy",
    "Noctium.PrivateClaimLowering.native_constraints_sound", "Noctium.PrivateClaimLowering.eligible_source_complete",
    "Noctium.PrivateClaimNativeState.native_execution_sound", "Noctium.PrivateClaimNativeState.source_native_preservation",
    "Noctium.PrivateClaimNativeState.eligible_admitted_complete", "Noctium.PrivateClaimNativePrivacy.privacy",
    "Noctium.PrivateClaimNativePrivacy.symmetric_eligible_native_pair"]


def run(command: list[str], cwd: Path = ROOT, env: dict | None = None, *, failure: bool = False,
        data: str | None = None, timeout: int = 300) -> subprocess.CompletedProcess:
    result = subprocess.run(command, cwd=cwd, env=env, input=data, capture_output=True, text=True, timeout=timeout)
    if result.returncode and not failure:
        raise AssertionError(f"command failed: {command}\n{result.stdout}\n{result.stderr}")
    return result


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def canonical(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n").encode()


def json_file(path: Path, pin: str | None = None) -> dict:
    contents = path.read_bytes()
    if pin is not None:
        assert re.fullmatch("[0-9a-f]{64}", pin) and digest(contents) == pin, "external_pin_mismatch"
    return HELPERS["strict_json_bytes"](contents)


def save(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(canonical(value))


def clean_env(toolchain: Path, imports: Path | None = None) -> dict:
    env = {key: value for key, value in os.environ.items() if not (
        key.startswith(("LEAN_", "DYLD_")) or key in {"CFLAGS", "CXXFLAGS", "LDFLAGS", "LD_LIBRARY_PATH", "LAKE_HOME"})}
    env.update(PATH=str(toolchain / "bin") + ":/usr/bin:/bin:/usr/sbin:/sbin", LC_ALL="C", TZ="UTC")
    if imports is not None:
        env["LEAN_PATH"] = str(imports)
    return env


def toolchain_measurement(root: Path | None = None) -> dict:
    if root is None:
        root = Path(run(["lake", "env", "lean", "--print-prefix"]).stdout.strip()).resolve()
    # Lean v4.35.0's Linux release stages ld.lld; preserve the existing macOS tool.
    if sys.platform == "darwin":
        linker = "ld64.lld"
    elif sys.platform.startswith("linux"):
        linker = "ld.lld"
    else:
        raise AssertionError("unsupported_Lean_toolchain_platform: " + sys.platform)

    identities = {}
    for name in ["lean", "lake", "leanexport", "leanchecker", "leanc", "clang", linker, "llvm-ar"]:
        path = root / "bin" / name
        assert path.is_file(), "required_toolchain_binary_missing: bin/" + name
        identities["bin/" + name] = sha(path)
    for path in sorted((root / "lib").rglob("*")):
        if path.is_file() and path.name.endswith((".dylib", ".so", ".olean", ".olean.private", ".ir", ".ir.sig")):
            identities[path.relative_to(root).as_posix()] = sha(path)
    value = {"version": run([str(root / "bin/lean"), "--version"]).stdout.strip(),
             "revision": run([str(root / "bin/lean"), "--githash"]).stdout.strip(), "files": identities}
    assert "4.35.0" in value["version"], "wrong_Lean_toolchain"
    return {"root": str(root), "identity": value, "sha256": digest(canonical(value))}


def archive(commit: str, destination: Path) -> dict:
    assert re.fullmatch("[0-9a-f]{40}", commit), "immutable_full_commit_required"
    tree = run(["git", "rev-parse", commit + "^{tree}"]).stdout.strip()
    contents = subprocess.run(["git", "archive", commit], cwd=ROOT, capture_output=True, check=True).stdout
    if destination.exists():
        assert not any(destination.iterdir()), "fresh_isolated_source_directory_required"
    destination.mkdir(parents=True, exist_ok=True)
    with tarfile.open(fileobj=io.BytesIO(contents)) as handle:
        handle.extractall(destination, filter="data")
    files = {}
    for path in sorted(destination.rglob("*")):
        assert not path.is_symlink(), "source_symlink_not_qualified"
        if path.is_file():
            files[path.relative_to(destination).as_posix()] = sha(path)
    return {"commit": commit, "tree": tree, "files": files, "sha256": digest(canonical(files))}


def source_build(commit: str, directory: Path, toolchain: Path) -> dict:
    directory.mkdir(parents=True, exist_ok=True)
    assert not any(directory.iterdir()), "fresh_isolated_build_output_required"
    source = directory / "source"
    source_identity = archive(commit, source)
    env = clean_env(toolchain)
    lake = str(toolchain / "bin/lake")
    run([lake, "build", "noctium", "Noctium.Compiler", "Noctium.Claim", "Noctium.Verification.ArtifactCertificate"], source, env)
    run([str(toolchain / "bin/lean"), "tests/ArtifactBytes.lean"], source,
        clean_env(toolchain, source / ".lake/build/lib/lean"))
    imports = directory / "proof-imports"
    for path in SOURCES:
        output = imports / Path(path).with_suffix(".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        run([str(toolchain / "bin/lean"), "-D", "Elab.async=false", "-o", str(output), path], source,
            clean_env(toolchain, Path(str(imports) + os.pathsep + str(source / ".lake/build/lib/lean"))))
    proof_env = clean_env(toolchain, Path(str(imports) + os.pathsep + str(source / ".lake/build/lib/lean")))
    for filename, roots in [("model.ndjson", MODEL_ROOTS), ("base-proof-closure.ndjson", BASE_ROOTS)]:
        exported = run([str(toolchain / "bin/leanexport"), "proofs.PrivateClaimArtifacts", "--", *roots], source, proof_env)
        (directory / filename).write_text(exported.stdout)
        HELPERS["exported_axioms"](directory / filename)
    artifacts = directory / "artifacts"
    run([str(source / ".lake/build/bin/noctium"), "compile", "examples/PrivateClaim.lean", "--target", PROFILE,
         "--output", str(artifacts)], source, env)
    shutil.copyfile(source / PROFILE, artifacts / "target-profile.json")
    imports_identity = []
    products = directory / "products"
    for prefix, location in [("library", source / ".lake/build/lib/lean"), ("proofs", imports)]:
        for path in sorted(location.rglob("*")):
            if path.is_file() and path.name.endswith((".olean", ".olean.private", ".olean.server", ".ir", ".ir.sig")):
                relative = prefix + "/" + path.relative_to(location).as_posix()
                target = products / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(path, target)
                imports_identity.append([relative, sha(path)])
    source_identity["profileSha256"] = sha(source / PROFILE)
    save(directory / "source-identity.json", source_identity)
    return {"source": source_identity, "imports": imports_identity,
            "modelSha256": sha(directory / "model.ndjson"),
            "baseProofSha256": sha(directory / "base-proof-closure.ndjson"),
            "compilerSha256": sha(source / ".lake/build/bin/noctium"),
            "artifacts": {name: sha(artifacts / name) for name in ARTIFACTS}}


def lean_bytes(data: bytes) -> str:
    return "[" + ", ".join(map(str, data)) + "]"


def quote_build(build: dict, profile_name: str) -> str:
    fields = []
    for name in ["sourceCommit", "sourceTree", "sourceClosureSha256", "sourcePolicy", "nativePolicy",
                 "theoremClosureSha256", "trustedModelSha256", "toolchainSha256"]:
        fields.append(name + " := " + json.dumps(build[name]))
    fields.append("profileBytes := " + profile_name)
    fields.append("importProducts := [" + ", ".join("(" + json.dumps(path) + ", " + json.dumps(value) + ")"
                                                  for path, value in build["importProducts"]) + "]")
    fields.append("compilerProductSha256 := " + json.dumps(build["compilerProductSha256"]))
    return "{ " + ", ".join(fields) + " }"


def certificate_source(build: dict, artifacts: Path) -> str:
    definitions = []
    for constant, filename in [("standaloneBytes", ARTIFACTS[0]), ("planBytes", ARTIFACTS[1]),
                               ("callBytes", ARTIFACTS[2]), ("profileBytes", ARTIFACTS[3])]:
        definitions.append(f"def {constant} : Noctium.Verification.ArtifactBytes.«Bytes» := {lean_bytes((artifacts / filename).read_bytes())}")
    checks = []
    for name, decoder, constant, expected in [("standalone", "decodeProgram", "standaloneBytes", "program"),
                                            ("plan", "decodePlan", "planBytes", "symbolicPlan"),
                                            ("call", "decodeProgram", "callBytes", "callProgram"),
                                            ("profile", "decodeProfile", "profileBytes", "selectedProfile")]:
        checks.append(f'''theorem {name}Valid : {decoder} {constant} = .ok {expected} := by
  have check : ({decoder} {constant}).toOption = some {expected} := by decide +kernel
  cases h : {decoder} {constant} with
  | error message => rw [h] at check; contradiction
  | ok target => rw [h] at check; exact congrArg Except.ok (Option.some.inj check)
''')
    return f'''import proofs.PrivateClaimArtifacts
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace {CERT}
open Noctium.Verification.ArtifactBytes Noctium.Verification.ArtifactCertificate
open Noctium.PrivateClaimLowering Noctium.PrivateClaimNativeState Noctium.PrivateClaimArtifacts
{os.linesep.join(definitions)}
def authority : Authority := {{
  build := {quote_build(build, 'profileBytes')}
  planBytes := planBytes
  callBytes := callBytes
  standaloneBytes := standaloneBytes
}}
def build : BuildIdentity := authority.build
def sourceIdentity : String := {json.dumps(build['sourceCommit'])}
{os.linesep.join(checks)}
theorem certified : Certified authority build sourceIdentity standaloneBytes planBytes callBytes profileBytes :=
  ⟨standaloneValid, planValid, callValid, profileValid, rfl, rfl, ⟨rfl,rfl,rfl,rfl⟩⟩
theorem binding : Noctium.Verification.NativePrivacy.ExactArtifactBinding
    Noctium.Verification.ArtifactBytes.«Bytes» BuildIdentity sourceIdentity
    planBytes callBytes (Noctium.Verification.ArtifactBytes.«tree» planBytes)
      (Noctium.Verification.ArtifactBytes.«tree» callBytes) build parse (Authenticated authority) :=
  exact_byte_build_binding authority build sourceIdentity standaloneBytes planBytes callBytes profileBytes certified
theorem functional : FunctionalPreservation (Noctium.Verification.ArtifactBytes.«tree» planBytes)
    (Noctium.Verification.ArtifactBytes.«tree» callBytes) :=
  concrete_preservation authority build sourceIdentity standaloneBytes planBytes callBytes profileBytes certified
theorem complete : EligibleCompleteness (Noctium.Verification.ArtifactBytes.«tree» planBytes)
    (Noctium.Verification.ArtifactBytes.«tree» callBytes) :=
  concrete_complete authority build sourceIdentity standaloneBytes planBytes callBytes profileBytes certified
theorem privacy : Noctium.PrivateClaimNativePrivacy.DecodedPrivacyObligation
    (Noctium.Verification.ArtifactBytes.«tree» planBytes) (Noctium.Verification.ArtifactBytes.«tree» callBytes) :=
  concrete_privacy authority build sourceIdentity standaloneBytes planBytes callBytes profileBytes certified
#print axioms certified
#print axioms binding
#print axioms privacy
end {CERT}
'''


def make_certificate(directory: Path, build: dict, toolchain: Path) -> None:
    source = directory / "source"
    candidate_root = directory / "certificate-source"
    path = candidate_root / "proofs/PrivateClaimArtifactCertificate.lean"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(certificate_source(build, directory / "artifacts"))
    imports = directory / "proof-imports"
    env = clean_env(toolchain, Path(str(imports) + os.pathsep + str(source / ".lake/build/lib/lean")))
    result = run([str(toolchain / "bin/lean"), "-D", "Elab.async=false", "--root", str(candidate_root),
                  "-o", str(imports / "proofs/PrivateClaimArtifactCertificate.olean"), str(path)], source, env)
    (directory / "certificate-axioms.txt").write_text(result.stdout)
    roots = BASE_ROOTS + [CERT + "." + item for item in ["certified", "binding", "functional", "complete", "privacy"]]
    exported = run([str(toolchain / "bin/leanexport"), "proofs.PrivateClaimArtifactCertificate", "--", *roots], source, env)
    (directory / "certificate.ndjson").write_text(exported.stdout)
    HELPERS["exported_axioms"](directory / "certificate.ndjson")
    replay = run([str(toolchain / "bin/leanchecker"), "--from-export", str(directory / "certificate.ndjson")], source, env)
    (directory / "kernel-replay.txt").write_text(replay.stdout + replay.stderr)


def check_authority_record(authority: dict) -> None:
    trust, record, build = authority["trustInput"], authority["record"], authority["build"]
    assert build == {"sourceCommit": trust["sourceCommit"], "sourceTree": trust["sourceTree"],
        "sourceClosureSha256": record["source"]["sha256"], "sourcePolicy": SOURCE_POLICY, "nativePolicy": NATIVE_POLICY,
        "theoremClosureSha256": record["baseProofSha256"], "trustedModelSha256": trust["trustedModelSha256"],
        "toolchainSha256": trust["toolchain"]["sha256"], "importProducts": record["imports"],
        "compilerProductSha256": record["compilerSha256"]}, "inconsistent_authority_record"
    assert record["source"]["commit"] == trust["sourceCommit"] and record["source"]["tree"] == trust["sourceTree"]
    assert digest(canonical(record["source"]["files"])) == record["source"]["sha256"]
    assert record["source"]["profileSha256"] == trust["targetProfileSha256"] == record["artifacts"]["target-profile.json"]
    assert authority["compiledContractVerified"] is False and authority["businessSpecificationReviewed"] is False


def check_driver_source(expected_files: dict) -> None:
    for name in ["scripts/proofs/check-private-claim-artifacts.py", "scripts/proofs/check-private-claim-lowering.py"]:
        assert sha(ROOT / name) == expected_files[name], "checker_source_not_the_published_revision: " + name


def check_files(directory: Path, record: dict) -> None:
    assert json_file(directory / "source-identity.json")["files"] == record["source"]["files"], "source_manifest_mismatch"
    for path, expected in record["source"]["files"].items():
        file = directory / "source" / path
        assert not file.is_symlink() and sha(file) == expected, "source_file_mismatch: " + path
    for path, expected in record["imports"]:
        assert sha(directory / "products" / path) == expected, "import_product_mismatch: " + path
        prefix, relative = path.split("/", 1)
        original = directory / ("source/.lake/build/lib/lean" if prefix == "library" else "proof-imports") / relative
        assert sha(original) == expected, "loaded_import_product_mismatch: " + path
    assert sha(directory / "source/.lake/build/bin/noctium") == record["compilerSha256"], "compiler_product_mismatch"
    for name, expected in record["artifacts"].items():
        assert sha(directory / "artifacts" / name) == expected, "artifact_file_mismatch: " + name
    assert sha(directory / "base-proof-closure.ndjson") == record["baseProofSha256"], "theorem_body_closure_mismatch"
    assert sha(directory / "model.ndjson") == record["modelSha256"], "trusted_model_mismatch"


def measure(commit: str, output: Path, toolchain: Path | None = None) -> dict:
    measured = toolchain_measurement(toolchain)
    record = source_build(commit, output, Path(measured["root"]))
    build = {"sourceCommit": commit, "sourceTree": record["source"]["tree"],
             "sourceClosureSha256": record["source"]["sha256"], "sourcePolicy": SOURCE_POLICY,
             "nativePolicy": NATIVE_POLICY, "theoremClosureSha256": record["baseProofSha256"],
             "trustedModelSha256": record["modelSha256"], "toolchainSha256": measured["sha256"],
             "importProducts": record["imports"], "compilerProductSha256": record["compilerSha256"]}
    check_driver_source(record["source"]["files"])
    make_certificate(output, build, Path(measured["root"]))
    trust = {"status": "measurement-only-not-an-authority", "sourceCommit": commit, "sourceTree": record["source"]["tree"],
             "targetProfileSha256": record["source"]["profileSha256"], "trustedModelSha256": record["modelSha256"],
             "toolchain": measured, "businessSpecificationReviewed": False,
             "artifactSha256": record["artifacts"], "compilerProductSha256": record["compilerSha256"],
             "sourceClosureSha256": record["source"]["sha256"], "theoremClosureSha256": record["baseProofSha256"],
             "importProducts": record["imports"], "localCertificateSha256": sha(output / "certificate.ndjson"),
             "localCertificateAxiomsSha256": sha(output / "certificate-axioms.txt"),
             "localKernelReplaySha256": sha(output / "kernel-replay.txt"),
             "localKernelReplayPassed": True, "externalAuthorityChecked": False,
             "compiledContractVerified": False}
    save(output / "measurements.json", trust)
    return trust


def prepare(trust_path: Path, trust_pin: str, output: Path) -> dict:
    trust = json_file(trust_path, trust_pin)
    tools = toolchain_measurement(Path(trust["toolchain"]["root"]))
    assert tools["sha256"] == trust["toolchain"]["sha256"], "trusted_toolchain_mismatch"
    record = source_build(trust["sourceCommit"], output, Path(tools["root"]))
    assert record["source"]["tree"] == trust["sourceTree"], "trusted_source_tree_mismatch"
    assert record["source"]["profileSha256"] == trust["targetProfileSha256"], "trusted_profile_mismatch"
    assert record["modelSha256"] == trust["trustedModelSha256"], "independently_reviewed_model_mismatch"
    build = {"sourceCommit": trust["sourceCommit"], "sourceTree": trust["sourceTree"],
             "sourceClosureSha256": record["source"]["sha256"], "sourcePolicy": SOURCE_POLICY, "nativePolicy": NATIVE_POLICY,
             "theoremClosureSha256": record["baseProofSha256"], "trustedModelSha256": record["modelSha256"],
             "toolchainSha256": tools["sha256"], "importProducts": record["imports"],
             "compilerProductSha256": record["compilerSha256"]}
    check_driver_source(record["source"]["files"])
    make_certificate(output, build, Path(tools["root"]))
    authority = {"schemaVersion": 1, "trustInputSha256": digest(canonical(trust)), "trustInputFileSha256": trust_pin, "trustInput": trust, "build": build, "record": record,
                 "certificateSha256": sha(output / "certificate.ndjson"), "businessSpecificationReviewed": False,
                 "remainingRequiredBridge": "issue57 key/deployment identity", "compiledContractVerified": False}
    save(output / "authority.json", authority)
    return authority


def candidate(authority_path: Path, authority_pin: str, output: Path) -> dict:
    authority = json_file(authority_path, authority_pin)
    check_authority_record(authority)
    check_driver_source(authority["record"]["source"]["files"])
    trust = authority["trustInput"]
    assert digest(canonical(trust)) == authority["trustInputSha256"], "authority_trust_input_mismatch"
    tools = toolchain_measurement(Path(trust["toolchain"]["root"]))
    assert tools["sha256"] == trust["toolchain"]["sha256"], "trusted_toolchain_mismatch"
    record = source_build(trust["sourceCommit"], output, Path(tools["root"]))
    assert record == authority["record"], "independent_build_not_reproducible"
    make_certificate(output, authority["build"], Path(tools["root"]))
    assert sha(output / "certificate.ndjson") == authority["certificateSha256"], "certificate_not_reproducible"
    manifest = {"schemaVersion": 1, "externalAuthoritySha256": authority_pin, "sourceCommit": trust["sourceCommit"],
                "sourceTree": trust["sourceTree"], "certificateSha256": sha(output / "certificate.ndjson"),
                "privateInvocationInputsConsumed": False, "compiledContractVerified": False}
    save(output / "manifest.json", manifest)
    return manifest


def verify(authority_path: Path, authority_pin: str, bundle: Path) -> dict:
    authority = json_file(authority_path, authority_pin)
    trusted = authority_path.parent
    check_authority_record(authority)
    check_driver_source(authority["record"]["source"]["files"])
    trust = authority["trustInput"]
    assert digest(canonical(trust)) == authority["trustInputSha256"], "authority_trust_input_mismatch"
    tools = toolchain_measurement(Path(trust["toolchain"]["root"]))
    assert tools["sha256"] == trust["toolchain"]["sha256"], "trusted_toolchain_mismatch"
    check_files(trusted, authority["record"])
    check_files(bundle, authority["record"])
    assert sha(trusted / "certificate.ndjson") == authority["certificateSha256"], "trusted_certificate_mismatch"
    assert sha(bundle / "certificate.ndjson") == authority["certificateSha256"], "certificate_body_mismatch"
    manifest = json_file(bundle / "manifest.json")
    assert manifest["externalAuthoritySha256"] == authority_pin and manifest["compiledContractVerified"] is False
    source = trusted / "source"
    env = clean_env(Path(tools["root"]), source / ".lake/build/lib/lean")
    # Only the immutable trusted checker source/products are imported. Candidate
    # modules and initializers are never loaded by this process.
    checked = run([str(Path(tools["root"]) / "bin/lean"), "--run", "scripts/proofs/AuditArtifactExport.lean",
                   str(trusted / "model.ndjson"), str(bundle / "certificate.ndjson"), str(authority_path),
                   str(trusted / "artifacts"), str(bundle / "artifacts")], source, env, timeout=600)
    result = json.loads(checked.stdout)
    assert result["compiledContractVerified"] is False and result["retainedBytesKernelMatched"]
    result.update(externalAuthoritySha256=authority_pin, sourceCommit=trust["sourceCommit"], sourceTree=trust["sourceTree"],
                  toolchainSha256=tools["sha256"], reproduciblePublicBuildChecked=True,
                  exactArtifactByteBuildBindingVerified=True, privateInvocationInputsConsumed=False,
                  scope="actual PrivateClaim 27-instruction scalar / 55-instruction call / 21-operation state plan",
                  observer="successfulClaimPublicTranscriptV1", successfulValidExecutionsOnly=True,
                  hashAndNativeImplementationAgreementRequired=True, finalBindingImplementationAgreementRequired=True,
                  proofByteZeroKnowledgeProved=False, bootstrapVerified=False,
                  remainingRequiredBridge="issue57 key/deployment identity")
    save(bundle / "audit.json", result)
    return result


def native_agreement(bundle: Path, cargo: Path, checker: Path | None) -> dict:
    samples = bundle / "parser-samples"
    samples.mkdir(exist_ok=True)
    values = [b' \t\n\r[0,12,true,false,null] \n',
              b'{"esc":"\\u0041\\n\\t\\r\\b\\f\\\"\\\\\\/"}',
              b'18446744073709551615', b'{"a":[{"b":0}],"c":{}}', b'[' * 64 + b'0' + b']' * 64]
    paths = []
    for i, data in enumerate(values):
        file = samples / f"positive-{i}.json"
        file.write_bytes(data)
        paths.append(str(file))
    paths += [str(bundle / "artifacts" / name) for name in ARTIFACTS[:4]]
    tools = toolchain_measurement()
    source = bundle / "source"
    env = clean_env(Path(tools["root"]), source / ".lake/build/lib/lean")
    lean = run([str(Path(tools["root"]) / "bin/lean"), "--run", "tests/ArtifactBytes.lean", *paths], source, env)
    native_env = os.environ.copy()
    compiled = run([str(cargo), "build", "--offline", "--locked", "--manifest-path",
                    str(ROOT / "scripts/proofs/artifact-json-native/Cargo.toml"), "--target-dir", str(samples / "native-target")],
                   env=native_env)
    (samples / "native-build.txt").write_text(compiled.stdout + compiled.stderr)
    rust = run([str(samples / "native-target/debug/noctium-artifact-json-probe"), *paths])
    assert [HELPERS["strict_json_bytes"](line.encode()) for line in lean.stdout.splitlines()] == [
        HELPERS["strict_json_bytes"](line.encode()) for line in rust.stdout.splitlines()], "native_parser_sample_mismatch"
    result = {"scope": "accepted actual artifact subset samples, not a proof of Rust/serde", "acceptedSamples": len(paths),
              "serdeJsonVersion": "1.0.154", "boundedAsciiParserAgreement": True, "nativeParserAgreementProved": False}
    if checker:
        js = samples / "official-parser.mjs"
        js.write_text(r"""import assert from 'node:assert/strict';
import {readFile} from 'node:fs/promises';
import {resolve} from 'node:path';
import {pathToFileURL} from 'node:url';
const [checker,...files] = process.argv.slice(2);
const {Zkir} = await import(pathToFileURL(resolve(checker)).href);
let checked = 0;
for (const file of files) {
  const original = await readFile(file,'utf8');
  const expected = Zkir.fromJson(original).serialize();
  for (const changed of [' \n\t'+original+'\r ', original.replace('"op"','"\\u006fp"')]) {
    assert.deepEqual(Zkir.fromJson(changed).serialize(),expected);
    checked++;
  }
}
console.log(JSON.stringify({officialParserVariants:checked,whitespaceAndAsciiEscapesAgree:true}));
""")
        official = run(["node", str(js), str(checker.resolve()), str(bundle / "artifacts/claimRelation.zkir"),
                        str(bundle / "artifacts/PrivateClaim.claim.zkir")])
        result.update(json.loads(official.stdout))
        result["officialCheckerModuleSha256"] = sha(checker)
    save(bundle / "native-parser-agreement.json", result)
    return result


def missing_root_assertion(contents: bytes) -> bytes:
    value = HELPERS["strict_json_bytes"](contents)
    instructions = value["instructions"]
    changed = [op for op in instructions if op != {"op": "assert", "cond": "%v7"}]
    assert len(changed) + 1 == len(instructions)
    value["instructions"] = changed
    return (json.dumps(value, indent=1, ensure_ascii=True) + "\n").encode()


def regress(authority_path: Path, authority_pin: str, bundle: Path) -> dict:
    authority = json_file(authority_path, authority_pin)
    verify(authority_path, authority_pin, bundle)
    rejections = []
    cases = [
        ("whitespace-bytes", bundle / "artifacts/PrivateClaim.claim.zkir", lambda b: b + b"\n", "artifact_file_mismatch"),
        ("semantic-bytes", bundle / "artifacts/PrivateClaim.claim.zkir", missing_root_assertion, "artifact_file_mismatch"),
        ("source-definition", bundle / "source/examples/PrivateClaim.lean", lambda b: b.replace(b"    require eq(storedRoot, root)\n", b"", 1), "source_file_mismatch"),
        ("specification", bundle / "source/proofs/PrivateClaimVerification.lean", lambda b: b.replace(b'outputs = [("nullifier", .native input.nullifier)]', b'outputs = []', 1), "source_file_mismatch"),
        ("theorem-body", bundle / "source/proofs/PrivateClaimNativePrivacy.lean", lambda b: b.replace("⟨rfl, bound_native_privacy⟩".encode(), "by exact ⟨rfl, bound_native_privacy⟩".encode(), 1), "source_file_mismatch"),
        ("imported-product", bundle / "products" / authority["record"]["imports"][0][0], lambda b: b + b"\x00", "import_product_mismatch"),
        ("selected-target", bundle / "artifacts/target-profile.json", lambda b: b.replace(b'"zkir": "3.2.1"', b'"zkir": "3.2.0"', 1), "artifact_file_mismatch"),
        ("certificate-body", bundle / "certificate.ndjson", lambda b: b + b" ", "certificate_body_mismatch"),
    ]
    for label, path, edit, expected in cases:
        original = path.read_bytes()
        changed = edit(original)
        assert changed != original, label
        try:
            path.write_bytes(changed)
            try:
                verify(authority_path, authority_pin, bundle)
            except AssertionError as error:
                assert expected in str(error), str(error)
            else:
                raise AssertionError("old_binding_accepted_mutation: " + label)
        finally:
            path.write_bytes(original)
        rejections.append(label)
    # The trusted kernel sub-check separately rejects changed retained bytes.
    # This check deliberately bypasses the hash manifest's earlier rejection.
    tools = Path(authority["trustInput"]["toolchain"]["root"])
    trusted = authority_path.parent
    path = bundle / "artifacts/PrivateClaim.claim.zkir"
    original = path.read_bytes()
    try:
        path.write_bytes(original + b"\n")
        negative = run([str(tools / "bin/lean"), "--run", "scripts/proofs/AuditArtifactExport.lean",
                        str(trusted / "model.ndjson"), str(bundle / "certificate.ndjson"), str(authority_path),
                        str(trusted / "artifacts"), str(bundle / "artifacts")], trusted / "source",
                       clean_env(tools, trusted / "source/.lake/build/lib/lean"), failure=True, timeout=600)
        assert negative.returncode and "retained_byte_mismatch: PrivateClaim.claim.zkir" in negative.stderr, negative.stdout + negative.stderr
    finally:
        path.write_bytes(original)
    # A fresh semantic mutant must fail at a real kernel reduction equality,
    # rather than receiving credit for import/setup failure.
    temporary = bundle / "negative-certificates"
    temporary.mkdir(exist_ok=True)
    for label, changed, accepts in [("whitespace", original + b"\n", True),
                                    ("semantic-root-assertion", missing_root_assertion(original), False)]:
        source = """import proofs.PrivateClaimArtifacts
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
open Noctium.Verification.ArtifactBytes Noctium.Verification.ArtifactCertificate
""" + "def bytes : Noctium.Verification.ArtifactBytes.«Bytes» := " + lean_bytes(changed) + "\n" +             "example : (decodeProgram bytes).toOption = some Noctium.PrivateClaimNativeState.callProgram := by decide +kernel\n"
        path = temporary / (label + ".lean")
        path.write_text(source)
        env = clean_env(tools, Path(str(bundle / "proof-imports") + os.pathsep + str(trusted / "source/.lake/build/lib/lean")))
        checked = run([str(tools / "bin/lean"), "-D", "Elab.async=false", str(path)], trusted / "source", env, failure=not accepts)
        if not accepts:
            line = len(source.splitlines())
            assert checked.returncode and f"{path.name}:{line}:" in checked.stdout and "decide" in checked.stdout, checked.stdout + checked.stderr
            assert "unknown module" not in checked.stdout and "unknown identifier" not in checked.stdout
    result = {"status": "passed", "oldBindingsRejected": rejections, "retainedWhitespaceKernelMismatchRejected": True,
              "whitespaceParserCertificateAccepted": True, "semanticMutantKernelEqualityRejected": True,
              "importSetupErrorsCountedAsSemanticRejection": False, "compiledContractVerified": False}
    save(bundle / "regressions.json", result)
    return result


def main() -> int:
    if not __debug__:
        print(json.dumps({"status": "rejected", "error": "optimized_python_is_not_qualified"}))
        return 1
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    measurement = commands.add_parser("measure", help="Produce untrusted measurements for independent review/pinning")
    measurement.add_argument("--trusted-source-commit", required=True)
    measurement.add_argument("--output-dir", type=Path, required=True)
    preparation = commands.add_parser("prepare-authority", help="Rebuild externally pinned reviewed inputs in isolation")
    preparation.add_argument("--trust-input", type=Path, required=True)
    preparation.add_argument("--trust-input-sha256", required=True)
    preparation.add_argument("--output-dir", type=Path, required=True)
    for action in ["build-candidate", "verify"]:
        command = commands.add_parser(action)
        command.add_argument("--authority", type=Path, required=True)
        command.add_argument("--authority-sha256", required=True)
        command.add_argument("--bundle", type=Path, required=True)
    agreement = commands.add_parser("native-agreement")
    agreement.add_argument("--bundle", type=Path, required=True)
    agreement.add_argument("--cargo", type=Path, required=True)
    agreement.add_argument("--native-checker", type=Path)
    regression = commands.add_parser("regress")
    regression.add_argument("--authority", type=Path, required=True)
    regression.add_argument("--authority-sha256", required=True)
    regression.add_argument("--bundle", type=Path, required=True)
    args = parser.parse_args()
    try:
        if args.command == "measure":
            result = measure(args.trusted_source_commit, args.output_dir.resolve())
        elif args.command == "prepare-authority":
            result = prepare(args.trust_input.resolve(), args.trust_input_sha256, args.output_dir.resolve())
        elif args.command == "build-candidate":
            result = candidate(args.authority.resolve(), args.authority_sha256, args.bundle.resolve())
        elif args.command == "verify":
            result = verify(args.authority.resolve(), args.authority_sha256, args.bundle.resolve())
        elif args.command == "native-agreement":
            result = native_agreement(args.bundle.resolve(), args.cargo.absolute(), args.native_checker)
        else:
            result = regress(args.authority.resolve(), args.authority_sha256, args.bundle.resolve())
        if args.command == "measure":
            result = {"status": result["status"], "measurements": str(args.output_dir.resolve() / "measurements.json"),
                      "measurementsSha256": sha(args.output_dir.resolve() / "measurements.json"),
                      "sourceCommit": result["sourceCommit"], "trustedModelSha256": result["trustedModelSha256"],
                      "toolchainSha256": result["toolchain"]["sha256"]}
        elif args.command == "prepare-authority":
            result = {"status": "externally-pinned-public-source-rebuilt", "authority": str(args.output_dir.resolve() / "authority.json"),
                      "authoritySha256": sha(args.output_dir.resolve() / "authority.json"), "compiledContractVerified": False}
        print(json.dumps(result, sort_keys=True))
        return 0
    except (AssertionError, OSError, ValueError, subprocess.SubprocessError) as error:
        print(json.dumps({"status": "rejected", "error": str(error)}))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
