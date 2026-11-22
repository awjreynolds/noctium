#!/usr/bin/env python3
"""Check retained K7 SDK receipts against the tracked 3.2.1 state bytes.

This offline check covers the recorded scalar-witness deployment and final
state for Rust, C++, Chrome, Swift on macOS and iOS simulator, and Kotlin on an
Android emulator. It checks JSON state lengths and SHA-256 values against
tests/witness62-public/states/321-{deploy,call}.bin, receipt ordering, profile
identity where recorded, and retained recovery fields. The Rust and historical
C++ records have explicit recovery-evidence gaps. The C++ profile also omits a
circuit digest, so the current manifest is not treated as its artifact proof.
The later C ABI recovery record is excluded because it records different state
lengths and digests.

This validates retained record consistency. It does not rerun SDKs, prove the
receipts authentic, establish a source-to-deployment or consensus claim,
qualify current Noctium source, or establish K9 qualification.
"""
from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
PROFILE = "midnight-ledger-9-zkir-3.2.1"
ENTRYPOINT = "TypedWitness.ScalarWitness.claim"
DEPLOY_SHA = "affbcd6f2b192893bb0d5b777a01446dffdb097b48af27f5aa0f2539a9cbfd4e"
CALL_SHA = "f9b24f4480110e62fe9333e5c3be687073922bd24b0935fbd62c0eb1b699c600"
RECOVERY_GAPS = {
    "Rust": "K7 receipt records final state and private commit, but no restart recovery run.",
    "C++": (
        "The retained 3.2.1 C++ profile records deployment, call and independent observation, "
        "but no restart recovery fields. A later C ABI recovery receipt has different state bytes."
    ),
}


class EvidenceError(AssertionError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise EvidenceError(message)


def required(mapping: Any, key: str, where: str) -> Any:
    require(isinstance(mapping, dict), f"{where}: expected an object")
    require(key in mapping, f"{where}: missing required field {key}")
    return mapping[key]


def load_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as error:
        raise EvidenceError(f"cannot read {path.relative_to(ROOT)}: {error}") from error


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def check_state(record: Any, expected: bytes, expected_sha: str, where: str) -> None:
    size = required(record, "contractStateBytes", where)
    digest = required(record, "contractStateSha256", where)
    require(type(size) is int and size == len(expected),
            f"{where}: state length {size!r} does not match tracked {len(expected)} bytes")
    require(digest == expected_sha == sha256(expected),
            f"{where}: state digest does not match tracked 3.2.1 bytes")


def parse_height(value: Any, where: str) -> int:
    if type(value) is int and value > 0:
        return value
    if isinstance(value, str) and value.isascii() and value.isdecimal():
        parsed = int(value)
        if parsed > 0:
            return parsed
    raise EvidenceError(f"{where}: invalid height")


def check_transaction(record: Any, event: str, state: bytes, digest: str, where: str) -> tuple[int, str]:
    require(required(record, "event", where) == event, f"{where}: expected {event} event")
    check_state(record, state, digest, where)
    parsed_height = parse_height(required(record, "height", where), where)
    parsed_finalized = parse_height(required(record, "finalizedHeight", where), where)
    require(parsed_height > 0 and parsed_height == parsed_finalized,
            f"{where}: height is missing, nonpositive, or not finalized")
    address = required(record, "contractAddress", where)
    require(isinstance(address, str) and len(address) == 64,
            f"{where}: invalid contract address")
    return parsed_height, address


def check_pair(deploy: Any, call: Any, where: str,
               deploy_state: bytes, call_state: bytes) -> dict[str, Any]:
    deploy_height, deploy_address = check_transaction(
        deploy, "Deploy", deploy_state, DEPLOY_SHA, f"{where} deployment")
    call_height, call_address = check_transaction(
        call, "Call", call_state, CALL_SHA, f"{where} final call")
    require(deploy_height < call_height, f"{where}: deployment must precede final call")
    require(deploy_address == call_address, f"{where}: deployment and call addresses differ")
    return {
        "deploymentHeight": deploy_height,
        "finalHeight": call_height,
        "contractAddress": deploy_address,
    }


def check_profile(record: Any, where: str) -> None:
    require(required(record, "profile", where) == PROFILE, f"{where}: wrong or missing 3.2.1 profile")
    require(required(record, "entrypoint", where) == ENTRYPOINT, f"{where}: wrong or missing entrypoint")


def check_k7(record: Any, where: str, circuit_digest: str) -> None:
    require(required(record, "k", where) == 7, f"{where}: missing K7 marker")
    require(required(record, "circuitSha256", where) == circuit_digest,
            f"{where}: circuit digest differs from retained K7 bundle")


def validate_cpp(qualification: Any, circuit_digest: str, manifest_digest: str,
                 deploy_state: bytes, call_state: bytes) -> dict[str, Any]:
    profiles = required(qualification, "profiles", "C++ qualification")
    matches = [item for item in profiles if isinstance(item, dict) and item.get("profile") == "321"]
    require(len(matches) == 1, "C++ qualification: missing or duplicate required 321 host record")
    record = matches[0]
    cpp = required(record, "cpp", "C++ qualification profile 321")
    for key in ("binarySha256", "sourceSha256", "librarySha256", "logSha256"):
        value = required(cpp, key, "C++ qualification")
        require(isinstance(value, str) and len(value) == 64,
                f"C++ qualification: invalid {key}")
    require(required(cpp, "beforeAfterHashesMatched", "C++ qualification") is True,
            "C++ qualification: linked library hashes did not match")
    observer = required(record, "independentObservation", "C++ qualification")
    require(required(observer, "profile", "C++ observer") == "321",
            "C++ observer: missing 3.2.1 profile")
    require(required(observer, "exactStatesMatched", "C++ observer") is True,
            "C++ observer: exact state comparison is missing or failed")
    require(required(observer, "linkedLibraryMatchesRecordedBeforeAfter", "C++ observer") is True,
            "C++ observer: linked library digest comparison is missing or failed")
    pair = check_pair(record.get("deployment"), record.get("call"), "C++",
                      deploy_state, call_state)
    require(required(record, "contractAddress", "C++ profile") == pair["contractAddress"],
            "C++ profile: top-level address differs from receipts")
    heights = required(observer, "heights", "C++ observer")
    require(heights == [str(pair["deploymentHeight"]), str(pair["finalHeight"])],
            "C++ observer: ordered heights differ from receipts")
    require(required(record, "sourceProviderCalls", "C++ profile") == 5,
            "C++ profile: missing source provider run")
    require(required(record, "sourceJournalCasAndValueCheckPassed", "C++ profile") is True,
            "C++ profile: source journal CAS check is missing or failed")

    bundle_entries = [item for item in required(qualification, "bundles", "qualification")
                      if item.get("profile") == "321" and item.get("workload") == "scalar"]
    require(len(bundle_entries) == 1, "qualification: missing or duplicate 3.2.1 scalar bundle pin")
    require(required(bundle_entries[0], "file", "3.2.1 scalar bundle pin") ==
            "bundles/321-scalar.manifest.json", "qualification: wrong scalar bundle manifest path")
    recorded_manifest_digest = required(bundle_entries[0], "sha256", "3.2.1 scalar bundle pin")
    require(isinstance(recorded_manifest_digest, str) and len(recorded_manifest_digest) == 64,
            "qualification: invalid historical scalar manifest digest")
    state_files = required(qualification, "publicStateFiles", "qualification")
    for event, state, digest, file_stem, height in (
        ("Deploy", deploy_state, DEPLOY_SHA, "deploy", pair["deploymentHeight"]),
        ("Call", call_state, CALL_SHA, "call", pair["finalHeight"]),
    ):
        rows = [row for row in state_files if row.get("profile") == "321" and row.get("event") == event]
        require(len(rows) == 1, f"C++ state inventory: missing or duplicate {event} row")
        row = rows[0]
        require(required(row, "file", f"C++ {event} state inventory") ==
                f"states/321-{file_stem}.bin", f"C++ state inventory: wrong {event} file")
        require(required(row, "bytes", f"C++ {event} state inventory") == len(state) and
                required(row, "sha256", f"C++ {event} state inventory") == digest == sha256(state),
                f"C++ state inventory: {event} bytes or digest changed")
        require(required(row, "height", f"C++ {event} state inventory") == height,
                f"C++ state inventory: {event} height changed")
        require(required(row, "contractAddress", f"C++ {event} state inventory") ==
                pair["contractAddress"], f"C++ state inventory: {event} address changed")
    pair["profile"] = PROFILE
    pair["recovery"] = {"gap": RECOVERY_GAPS["C++"]}
    pair["circuitAssociation"] = {
        "gap": "Historical C++ profile omits a circuit SHA-256 binding.",
        "currentManifestCircuitSha256": circuit_digest,
        "historicalManifestDigest": recorded_manifest_digest,
        "currentManifestDigest": manifest_digest,
    }
    return pair


def validate(data: dict[str, Any], deploy_state: bytes, call_state: bytes) -> dict[str, Any]:
    deploy_sha = sha256(deploy_state)
    call_sha = sha256(call_state)
    require(deploy_sha == DEPLOY_SHA, "tracked deployment state bytes changed")
    require(call_sha == CALL_SHA, "tracked final state bytes changed")
    require(len(deploy_state) == 1482 and len(call_state) == 1482,
            "tracked state byte lengths changed")

    manifest = required(data, "manifest", "records")
    require(required(manifest, "profile", "3.2.1 manifest") == PROFILE,
            "3.2.1 manifest: wrong profile")
    circuit_entries = [item for item in required(manifest, "entries", "3.2.1 manifest")
                       if item.get("role") == "circuit" and
                       item.get("name") == f"{ENTRYPOINT}.zkir"]
    require(len(circuit_entries) == 1, "3.2.1 manifest: missing selected K7 circuit")
    circuit_digest = required(circuit_entries[0], "sha256", "selected K7 circuit")

    hosts: dict[str, dict[str, Any]] = {}

    rust = required(data, "rust", "records")
    check_profile(rust, "Rust receipt")
    check_k7(rust, "Rust receipt", circuit_digest)
    hosts["Rust"] = check_pair(rust.get("deployment"), rust.get("receipt"), "Rust",
                               deploy_state, call_state)
    exact = required(rust, "exactState", "Rust receipt")
    check_state({"contractStateBytes": required(exact, "bytes", "Rust exact state"),
                 "contractStateSha256": required(exact, "sha256", "Rust exact state")},
                call_state, CALL_SHA, "Rust exact state")
    require(required(rust, "privateCommitAfterFinality", "Rust receipt") is True,
            "Rust receipt: private commit-after-finality check is missing or failed")
    hosts["Rust"].update(profile=PROFILE, recovery={"gap": RECOVERY_GAPS["Rust"]},
                         circuitSha256=circuit_digest)

    hosts["C++"] = validate_cpp(required(data, "qualification", "records"), circuit_digest,
                                  required(data, "manifestSha256", "records"),
                                  deploy_state, call_state)

    web = required(data, "web", "records")
    check_profile(web, "Chrome receipt")
    web_circuit = required(web, "circuit", "Chrome receipt")
    require(required(web_circuit, "k", "Chrome circuit") == 7,
            "Chrome circuit: missing K7 marker")
    web_bundle_digest = required(web, "bundleManifestSha256", "Chrome receipt")
    require(isinstance(web_bundle_digest, str) and len(web_bundle_digest) == 64,
            "Chrome receipt: invalid bundle manifest digest")
    hosts["Chrome"] = check_pair(web.get("deployment"), web.get("receipt"), "Chrome",
                                 deploy_state, call_state)
    for key in ("workerRestarted", "recoveredWithoutReproof", "pendingBeforeRestart",
                "approvalDenied", "exactState"):
        require(required(web, key, "Chrome receipt") is True,
                f"Chrome receipt: recovery/state field {key} is missing or false")
    hosts["Chrome"].update(profile=PROFILE, recovery={
        "workerRestarted": web["workerRestarted"],
        "recoveredWithoutReproof": web["recoveredWithoutReproof"],
        "exactState": web["exactState"],
    }, circuitAssociation={
        "gap": "Chrome receipt records K7 and a bundle digest, but no circuit SHA-256.",
        "bundleManifestSha256": web_bundle_digest,
    })

    swift = required(data, "swift", "records")
    check_profile(swift, "Swift receipts")
    check_k7(swift, "Swift receipts", circuit_digest)
    runs = required(swift, "runs", "Swift receipts")
    require(isinstance(runs, list) and len(runs) == 2,
            "Swift receipts: both required platform runs must be present")
    expected_platforms = {"macOS arm64", "iOS 27.0 simulator arm64"}
    require({run.get("platform") for run in runs if isinstance(run, dict)} == expected_platforms,
            "Swift receipts: missing or unexpected platform record")
    for run in runs:
        platform = required(run, "platform", "Swift run")
        recovery = {}
        for key in ("seedlessRecovery", "privateStateAcknowledged", "recoveredSealedBytesMatched"):
            require(required(run, key, f"Swift {platform}") is True,
                    f"Swift {platform}: recovery field {key} is missing or false")
            recovery[key] = run[key]
        hosts[f"Swift {platform}"] = check_pair(
            run.get("deployment"), run.get("call"), f"Swift {platform}",
            deploy_state, call_state)
        hosts[f"Swift {platform}"].update(profile=PROFILE, recovery=recovery,
                                           circuitSha256=circuit_digest)

    android = required(data, "android", "records")
    check_profile(android, "Kotlin Android receipt")
    check_k7(android, "Kotlin Android receipt", circuit_digest)
    platform = required(android, "platform", "Kotlin Android receipt")
    require(platform == "AOSP Android 35 ARM64 emulator",
            "Kotlin Android receipt: wrong or missing emulator platform")
    hosts["Kotlin Android emulator"] = check_pair(
        android.get("deployment"), android.get("call"), "Kotlin Android emulator",
        deploy_state, call_state)
    recovery = {}
    for key in ("seedlessRecovery", "recoveredSealedBytesMatched",
                "privateStateAcknowledgedAfterFinality"):
        require(required(android, key, "Kotlin Android receipt") is True,
                f"Kotlin Android receipt: recovery field {key} is missing or false")
        recovery[key] = android[key]
    hosts["Kotlin Android emulator"].update(profile=PROFILE, recovery=recovery,
                                           circuitSha256=circuit_digest)

    expected_hosts = {"Rust", "C++", "Chrome", "Swift macOS arm64",
                      "Swift iOS 27.0 simulator arm64", "Kotlin Android emulator"}
    require(set(hosts) == expected_hosts,
            "required host set mismatch: " + ", ".join(sorted(set(hosts) ^ expected_hosts)))
    for name, receipt in hosts.items():
        require(receipt["profile"] == PROFILE, f"{name}: missing profile")
        require("recovery" in receipt, f"{name}: missing recovery evidence or explicit gap")
    return {
        "status": "passed",
        "scope": "offline scalar-witness 3.2.1 receipt consistency, with K7 identity where recorded",
        "scopeLimits": {
            "currentSourceQualified": False,
            "k9Qualified": False,
            "receiptsAuthenticated": False,
        },
        "state": {
            "deploymentBytes": len(deploy_state), "deploymentSha256": deploy_sha,
            "finalBytes": len(call_state), "finalSha256": call_sha,
        },
        "hosts": hosts,
    }


def expect_rejected(name: str, data: dict[str, Any], deploy_state: bytes,
                    call_state: bytes, expected: str) -> None:
    try:
        validate(data, deploy_state, call_state)
    except EvidenceError as error:
        require(expected in str(error), f"{name}: unexpected rejection: {error}")
    else:
        raise EvidenceError(f"{name}: mutated evidence unexpectedly passed")


def check_mutations(data: dict[str, Any], deploy_state: bytes, call_state: bytes) -> list[str]:
    cases = []
    changed_digest = copy.deepcopy(data)
    changed_digest["web"]["receipt"]["contractStateSha256"] = "0" * 64
    expect_rejected("changed digest", changed_digest, deploy_state, call_state,
                    "state digest does not match")
    cases.append("changed receipt digest rejected")

    missing_host = copy.deepcopy(data)
    del missing_host["android"]
    expect_rejected("missing host", missing_host, deploy_state, call_state,
                    "missing required field")
    cases.append("missing required host rejected")

    missing_recovery = copy.deepcopy(data)
    del missing_recovery["web"]["recoveredWithoutReproof"]
    expect_rejected("missing recovery field", missing_recovery, deploy_state, call_state,
                    "missing required field recoveredWithoutReproof")
    cases.append("missing required recovery field rejected")
    return cases


def main() -> int:
    deploy_path = ROOT / "tests/witness62-public/states/321-deploy.bin"
    call_path = ROOT / "tests/witness62-public/states/321-call.bin"
    manifest_path = ROOT / "tests/witness62-public/bundles/321-scalar.manifest.json"
    deploy_state = deploy_path.read_bytes()
    call_state = call_path.read_bytes()
    manifest_bytes = manifest_path.read_bytes()
    data = {
        "rust": load_json(ROOT / "docs/development/rust-typed-witness-localnet-receipt.json"),
        "qualification": load_json(ROOT / "tests/witness62-public/qualification-evidence.json"),
        "manifest": json.loads(manifest_bytes),
        "manifestSha256": sha256(manifest_bytes),
        "web": load_json(ROOT / "docs/development/web-localnet-receipt.json"),
        "swift": load_json(ROOT / "docs/development/swift-localnet-receipts.json"),
        "android": load_json(ROOT / "docs/development/android-localnet-receipt.json"),
    }
    report = validate(data, deploy_state, call_state)
    report["mutationChecks"] = check_mutations(data, deploy_state, call_state)
    print(json.dumps(report, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
