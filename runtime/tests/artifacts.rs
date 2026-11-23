use noctium_runtime::artifacts::{
    self, ContractBundleSet, Manifest, Recipe, Role, Selection, VerifiedBundle,
};
use serde_json::{Value, json};
use std::{
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

static NEXT: AtomicU64 = AtomicU64::new(1);
struct Fixture {
    root: PathBuf,
}
impl Fixture {
    fn new() -> Self {
        let root = std::env::temp_dir().join(format!(
            "noctium-artifact-tests-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&root).unwrap();
        let root = fs::canonicalize(root).unwrap();
        let fixture = Self { root };
        fs::write(fixture.path("Contract.lean"), b"import Noctium\n").unwrap();
        fs::write(fixture.path("entry.zkir"), json!({"version":{"major":3,"minor":2},"do_communications_commitment":true,"instructions":[],"inputs":[],"outputs":[]}).to_string()).unwrap();
        let circuit = json!({"name":"relation","file":"relation.zkir","inputs":[],"outputs":[],"constraints":[]});
        fs::write(fixture.path("entry.impact.json"), json!({"schemaVersion":1,"nativeCircuitFile":"Contract.call.zkir","contractName":"Contract","entrypoint":"call","operations":[],"reads":[],"state":[],"circuit":circuit}).to_string()).unwrap();
        let profile = noctium_runtime::profile::target_json();
        fs::write(fixture.path("target.json"), profile.to_string()).unwrap();
        fs::write(fixture.path("noctium.json"), json!({"schemaVersion":1,"target":noctium_runtime::profile::NAME,"targetProfile":profile,"contracts":[{"name":"Contract","state":[],"entrypoints":[{"name":"call","circuit":"relation","nativeCircuitFile":"Contract.call.zkir","nativePlanFile":"Contract.call.impact.json"}]}],"circuits":[circuit]}).to_string()).unwrap();
        fs::write(
            fixture.path("noctium_runtime.h"),
            b"#define NOCTIUM_ABI_VERSION 1u\nint noctium_session_begin(void);\n",
        )
        .unwrap();
        fs::write(fixture.path("ledger.params"), b"public ledger parameters").unwrap();
        fs::write(fixture.path("entry.prover"), b"synthetic public prover key").unwrap();
        fs::write(
            fixture.path("entry.verifier"),
            b"synthetic public verifier key",
        )
        .unwrap();
        fs::write(fixture.path("tool.json"), json!({"repository":"https://github.com/midnightntwrk/midnight-zkir","revision":"446c7fecc6bd41dab99ebe89ab404e9d077d11a9","rust":"1.100.0","host":"test-host","version":"midnight-zkir 3.2.0","binary":"/private/local/build/zkir","binarySha256":"a".repeat(64),"cargoLockSha256":"b".repeat(64),"command":"cargo +1.100.0 build --release --locked --package midnight-zkir --features binary"}).to_string()).unwrap();
        if cfg!(feature = "zkir-321") {
            let mut plan: serde_json::Value =
                serde_json::from_slice(&fs::read(fixture.path("entry.impact.json")).unwrap())
                    .unwrap();
            plan["target"] = json!(noctium_runtime::profile::NAME);
            plan["targetProfile"] = profile;
            fs::write(fixture.path("entry.impact.json"), plan.to_string()).unwrap();
            let mut tool: serde_json::Value =
                serde_json::from_slice(&fs::read(fixture.path("tool.json")).unwrap()).unwrap();
            tool["revision"] = json!(noctium_runtime::profile::REVISION);
            tool["requestedVersion"] = json!(noctium_runtime::profile::RELEASE);
            tool["releaseLabel"] = json!(noctium_runtime::profile::RELEASE);
            tool["expectedCliVersion"] = json!(noctium_runtime::profile::CRATE_VERSION);
            fs::write(fixture.path("tool.json"), tool.to_string()).unwrap();
        }
        fixture
    }
    fn path(&self, name: &str) -> PathBuf {
        self.root.join(name)
    }
    fn recipe(&self) -> Recipe {
        Recipe {
            schema_version: 1,
            compiler_revision: "c".repeat(40),
            files: vec![
                self.selection(Role::Source, "examples/Contract.lean", "Contract.lean"),
                self.selection(Role::Circuit, "Contract.call.zkir", "entry.zkir"),
                self.selection(Role::Plan, "Contract.call.impact.json", "entry.impact.json"),
                self.selection(Role::Metadata, "noctium.json", "noctium.json"),
                self.selection(Role::Abi, "noctium_runtime.h", "noctium_runtime.h"),
                self.selection(Role::Profile, "target.json", "target.json"),
                self.selection(Role::LedgerParameters, "ledger.params", "ledger.params"),
                self.selection(Role::ProverKey, "entrypoint.prover", "entry.prover"),
                self.selection(Role::VerifierKey, "entrypoint.verifier", "entry.verifier"),
                self.selection(Role::Toolchain, "native-zkir.json", "tool.json"),
            ],
        }
    }
    fn selection(&self, role: Role, name: &str, path: &str) -> Selection {
        Selection {
            role,
            name: name.into(),
            input: self.path(path),
        }
    }
    fn assemble(&self, name: &str) -> Manifest {
        artifacts::assemble(self.recipe(), &self.path(name)).unwrap()
    }
    fn operation_recipe(&self, operation: &str, compiler_revision: &str) -> Recipe {
        let mut recipe = self.recipe();
        recipe.compiler_revision = compiler_revision.into();
        for selection in &mut recipe.files {
            match selection.role {
                Role::Circuit => {
                    selection.name = format!("Contract.{operation}.zkir");
                    selection.input = self.path(&format!("Contract.{operation}.zkir"));
                }
                Role::Plan => {
                    selection.name = format!("Contract.{operation}.impact.json");
                    selection.input = self.path(&format!("Contract.{operation}.impact.json"));
                }
                _ => {}
            }
        }
        recipe
    }
    fn configure_operations(&self, operations: &[&str], state: &Value) {
        let base: Value =
            serde_json::from_slice(&fs::read(self.path("entry.impact.json")).unwrap()).unwrap();
        let circuit = base["circuit"].clone();
        let mut metadata: Value =
            serde_json::from_slice(&fs::read(self.path("noctium.json")).unwrap()).unwrap();
        metadata["contracts"][0]["state"] = state.clone();
        metadata["contracts"][0]["entrypoints"] = json!(
            operations
                .iter()
                .map(|operation| json!({
                    "name": operation,
                    "circuit": "relation",
                    "nativeCircuitFile": format!("Contract.{operation}.zkir"),
                    "nativePlanFile": format!("Contract.{operation}.impact.json")
                }))
                .collect::<Vec<_>>()
        );
        fs::write(self.path("noctium.json"), metadata.to_string()).unwrap();
        for operation in operations {
            let circuit_name = format!("Contract.{operation}.zkir");
            let plan_name = format!("Contract.{operation}.impact.json");
            let mut plan = base.clone();
            plan["entrypoint"] = json!(operation);
            plan["nativeCircuitFile"] = json!(circuit_name);
            plan["state"] = state.clone();
            fs::write(
                self.path(&circuit_name),
                json!({
                    "version":{"major":3,"minor":2},
                    "do_communications_commitment":true,
                    "instructions":[],
                    "inputs":[],
                    "outputs":[]
                })
                .to_string(),
            )
            .unwrap();
            fs::write(self.path(&plan_name), plan.to_string()).unwrap();
        }
        metadata["circuits"] = json!([circuit]);
        fs::write(self.path("noctium.json"), metadata.to_string()).unwrap();
    }
    fn verified_operation(
        &self,
        directory: &str,
        operation: &str,
        operations: &[&str],
        compiler_revision: &str,
        state: &Value,
    ) -> VerifiedBundle {
        self.configure_operations(operations, state);
        let manifest = artifacts::assemble(
            self.operation_recipe(operation, compiler_revision),
            &self.path(directory),
        )
        .unwrap();
        let pin = artifacts::digest(&artifacts::manifest_bytes(&manifest).unwrap());
        artifacts::verify(&self.path(directory), Some(&pin)).unwrap()
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

fn witness_recipe(fixture: &Fixture) -> Recipe {
    let relation: serde_json::Value =
        serde_json::from_slice(&fs::read(fixture.path("entry.zkir")).unwrap()).unwrap();
    let binding = json!({
        "schemaVersion":1,"kind":"typed-witness-bindings","circuitName":"relation","sourceExport":"main",
        "target":{"kind":"entrypoint","contractName":"Contract","entrypoint":"call",
            "nativeCircuitFile":"Contract.call.zkir","targetProfile":noctium_runtime::profile::NAME},
        "types":[],"signatures":[],"inputBindings":[],"circuitInputs":[],"circuitOutputs":[],"calls":[],
        "nativeRelation":relation
    });
    write_witness_pair(fixture, &binding);
    let mut metadata: serde_json::Value =
        serde_json::from_slice(&fs::read(fixture.path("noctium.json")).unwrap()).unwrap();
    metadata["hostWitnessPlans"] = json!([{"circuit":"relation","bindingFile":"Contract.call.witness.json",
        "controlFile":"Contract.call.witness.control.json","target":"entrypoint","contract":"Contract",
        "entrypoint":"call","nativeWitnessQualified":false}]);
    fs::write(fixture.path("noctium.json"), metadata.to_string()).unwrap();
    let mut recipe = fixture.recipe();
    recipe.files.push(fixture.selection(
        Role::WitnessBinding,
        "Contract.call.witness.json",
        "call.witness.json",
    ));
    recipe.files.push(fixture.selection(
        Role::WitnessControl,
        "Contract.call.witness.control.json",
        "call.witness.control.json",
    ));
    recipe
}

fn selected_rust_recipe(fixture: &Fixture, include_rust: bool) -> Recipe {
    let contract = "NoctiumExamples.PrivateStateCounter";
    let entrypoint = "advance";
    let prefix = format!("{contract}.{entrypoint}");
    let mut recipe = fixture.recipe();
    for selection in &mut recipe.files {
        match selection.role {
            Role::Circuit => {
                selection.name = format!("{prefix}.zkir");
                selection.input = fixture.path("entry.zkir");
            }
            Role::Plan => {
                selection.name = format!("{prefix}.impact.json");
                selection.input = fixture.path("entry.impact.json");
            }
            _ => {}
        }
    }
    recipe.files.push(fixture.selection(
        Role::WitnessBinding,
        &format!("{prefix}.witness.json"),
        "call.witness.json",
    ));
    recipe.files.push(fixture.selection(
        Role::WitnessControl,
        &format!("{prefix}.witness.control.json"),
        "call.witness.control.json",
    ));
    if include_rust {
        recipe.files.push(fixture.selection(
            Role::RustBinding,
            &format!("{prefix}.rs"),
            &format!("{prefix}.rs"),
        ));
    }
    recipe
}

fn rust_binding_recipe(fixture: &Fixture) -> Recipe {
    const CIRCUIT: &[u8] = include_bytes!(
        "fixtures/private-authoring/321/NoctiumExamples.PrivateStateCounter.advance.zkir"
    );
    const PLAN: &[u8] = include_bytes!(
        "fixtures/private-authoring/321/NoctiumExamples.PrivateStateCounter.advance.impact.json"
    );
    const CONTROL: &[u8] = include_bytes!(
        "fixtures/private-authoring/321/NoctiumExamples.PrivateStateCounter.advance.witness.control.json"
    );
    const RUST: &[u8] = include_bytes!(
        "fixtures/private-authoring/321/bindings/rust/NoctiumExamples.PrivateStateCounter.advance.rs"
    );
    let control: Value = serde_json::from_slice(CONTROL).unwrap();
    let mut plan: Value = serde_json::from_slice(PLAN).unwrap();
    plan["circuit"].as_object_mut().unwrap().remove("file");
    let mut plan_bytes = serde_json::to_vec(&plan).unwrap();
    plan_bytes.push(b'\n');
    fs::write(fixture.path("entry.zkir"), CIRCUIT).unwrap();
    fs::write(fixture.path("entry.impact.json"), &plan_bytes).unwrap();
    fs::write(
        fixture.path("call.witness.json"),
        control["binding"].as_str().unwrap().as_bytes(),
    )
    .unwrap();
    fs::write(fixture.path("call.witness.control.json"), CONTROL).unwrap();
    fs::write(
        fixture.path("NoctiumExamples.PrivateStateCounter.advance.rs"),
        RUST,
    )
    .unwrap();

    let contract = "NoctiumExamples.PrivateStateCounter";
    let entrypoint = "advance";
    let prefix = format!("{contract}.{entrypoint}");
    let mut metadata_entrypoint = json!({
        "name": entrypoint,
        "circuit": plan["circuit"]["name"],
        "nativeCircuitFile": plan["nativeCircuitFile"],
        "nativePlanFile": format!("{prefix}.impact.json"),
        "nativeCircuitQualified": false,
        "nativePlanSha256": artifacts::digest(&plan_bytes)
    });
    for field in ["callInputs", "returns", "returnViews"] {
        if let Some(value) = plan.get(field) {
            metadata_entrypoint[field] = value.clone();
        }
    }
    let mut metadata_contract = json!({
        "name": contract,
        "state": plan["state"],
        "entrypoints": [metadata_entrypoint]
    });
    if let Some(constructor) = plan.get("constructor") {
        metadata_contract["constructor"] = constructor.clone();
    }
    let metadata = json!({
        "schemaVersion": 3,
        "target": noctium_runtime::profile::NAME,
        "targetProfile": noctium_runtime::profile::target_json(),
        "qualification": "unqualified-relation-and-state-description",
        "deployable": false,
        "contracts": [metadata_contract],
        "circuits": [],
        "hostWitnessPlans": [{
            "circuit": plan["circuit"]["name"],
            "bindingFile": format!("{prefix}.witness.json"),
            "controlFile": format!("{prefix}.witness.control.json"),
            "target": "entrypoint",
            "contract": contract,
            "entrypoint": entrypoint,
            "nativeWitnessQualified": false
        }],
        "artifacts": [
            {"file":format!("{prefix}.zkir"),"role":"ledger"},
            {"file":format!("{prefix}.impact.json"),"role":"ledger"},
            {"file":format!("{prefix}.witness.json"),"role":"witness"},
            {"file":format!("{prefix}.witness.control.json"),"role":"witness"},
            {"file":format!("bindings/rust/{prefix}.rs"),"role":"rustBinding","sha256":artifacts::digest(RUST)}
        ]
    });
    fs::write(fixture.path("noctium.json"), metadata.to_string()).unwrap();
    selected_rust_recipe(fixture, true)
}

fn write_witness_pair(fixture: &Fixture, binding: &serde_json::Value) {
    let text = serde_json::to_string(binding).unwrap();
    fs::write(fixture.path("call.witness.json"), &text).unwrap();
    fs::write(
        fixture.path("call.witness.control.json"),
        json!({
            "schemaVersion":2,"kind":"host-control","mode":"native","binding":text,"name":"main",
            "types":[],"witnesses":[],"inputs":[],"functions":[{"id":"f","name":"main",
                "parameters":[],"resultType":"Unit","body":[{"tag":"return","value":null}]}],
            "entry":"f","limits":{"maxSteps":1000}
        })
        .to_string(),
    )
    .unwrap();
}

#[test]
fn retained_typed_witness_pair_is_selected_and_checked() {
    let fixture = Fixture::new();
    let recipe = witness_recipe(&fixture);
    let manifest = artifacts::assemble(recipe, &fixture.path("typed")).unwrap();
    let manifest_bytes = fs::read(fixture.path("typed/manifest.json")).unwrap();
    use sha2::{Digest, Sha256};
    let digest = hex::encode(Sha256::digest(&manifest_bytes));
    let bundle = artifacts::verify(&fixture.path("typed"), Some(&digest)).unwrap();
    assert_eq!(
        bundle.file(Role::WitnessBinding).unwrap(),
        fs::read(fixture.path("call.witness.json")).unwrap()
    );
    assert_eq!(
        bundle.file(Role::WitnessControl).unwrap(),
        fs::read(fixture.path("call.witness.control.json")).unwrap()
    );
    assert_eq!(manifest.entries.last().unwrap().role, Role::WitnessControl);
}

#[test]
fn selected_compiler_inventory_binds_ledger_and_witness_files() {
    let fixture = Fixture::new();
    let recipe = witness_recipe(&fixture);
    let metadata_path = fixture.path("noctium.json");
    let plan_path = fixture.path("entry.impact.json");
    let mut metadata: Value = serde_json::from_slice(&fs::read(&metadata_path).unwrap()).unwrap();
    let mut plan: Value = serde_json::from_slice(&fs::read(&plan_path).unwrap()).unwrap();
    plan["circuit"].as_object_mut().unwrap().remove("file");
    let plan_text = plan.to_string();
    fs::write(&plan_path, &plan_text).unwrap();
    metadata["schemaVersion"] = json!(3);
    metadata["circuits"] = json!([]);
    metadata["contracts"][0]["entrypoints"][0]["nativePlanSha256"] =
        json!(artifacts::digest(plan_text.as_bytes()));
    metadata["artifacts"] = json!([
        {"file":"Contract.call.zkir","role":"ledger"},
        {"file":"Contract.call.impact.json","role":"ledger"},
        {"file":"Contract.call.witness.json","role":"witness"},
        {"file":"Contract.call.witness.control.json","role":"witness"}
    ]);
    fs::write(&metadata_path, metadata.to_string()).unwrap();
    artifacts::assemble(recipe, &fixture.path("selected")).unwrap();

    fs::write(&plan_path, format!("{plan_text}\n")).unwrap();
    assert_eq!(
        failure(artifacts::assemble(
            witness_recipe(&fixture),
            &fixture.path("wrong-plan")
        )),
        "plan_mismatch"
    );
    fs::write(&plan_path, plan_text).unwrap();

    metadata["artifacts"][0]["role"] = json!("standalone");
    fs::write(metadata_path, metadata.to_string()).unwrap();
    let altered = witness_recipe(&fixture);
    assert_eq!(
        failure(artifacts::assemble(altered, &fixture.path("wrong-role"))),
        "plan_mismatch"
    );
}

#[test]
fn rust_binding_payload_matches_exact_inventory_bytes_and_selected_control() {
    let fixture = Fixture::new();
    let recipe = rust_binding_recipe(&fixture);
    let assembled = artifacts::assemble(recipe, &fixture.path("rust-binding"));
    if cfg!(feature = "zkir-320") {
        // The retained binding and plan name the 3.2.1 target.
        assert_eq!(failure(assembled), "profile_mismatch");
        return;
    }
    let manifest = assembled.unwrap();
    let pin = artifacts::digest(&artifacts::manifest_bytes(&manifest).unwrap());
    let bundle = artifacts::verify(&fixture.path("rust-binding"), Some(&pin)).unwrap();
    assert_eq!(
        bundle.file(Role::RustBinding).unwrap(),
        include_bytes!(
            "fixtures/private-authoring/321/bindings/rust/NoctiumExamples.PrivateStateCounter.advance.rs"
        )
    );

    fs::write(
        fixture.path("NoctiumExamples.PrivateStateCounter.advance.rs"),
        b"pub fn stale_witness() {}\n",
    )
    .unwrap();
    let stale_recipe = selected_rust_recipe(&fixture, true);
    assert_eq!(
        failure(artifacts::assemble(
            stale_recipe,
            &fixture.path("stale-rust-binding")
        )),
        "plan_mismatch"
    );

    let legacy = Fixture::new();
    let mut no_rust_recipe = rust_binding_recipe(&legacy);
    no_rust_recipe
        .files
        .retain(|selection| selection.role != Role::RustBinding);
    let metadata_path = legacy.path("noctium.json");
    let mut metadata: Value = serde_json::from_slice(&fs::read(&metadata_path).unwrap()).unwrap();
    metadata["artifacts"][4]
        .as_object_mut()
        .unwrap()
        .remove("sha256");
    fs::write(metadata_path, metadata.to_string()).unwrap();
    artifacts::assemble(no_rust_recipe, &legacy.path("no-rust-module")).unwrap();
}

#[test]
fn missing_unreferenced_or_mismatched_witness_pair_rejects() {
    let fixture = Fixture::new();
    let mut recipe = witness_recipe(&fixture);
    recipe
        .files
        .retain(|selection| selection.role != Role::WitnessBinding);
    assert_eq!(
        failure(artifacts::assemble(recipe, &fixture.path("missing"))),
        "missing_role"
    );

    let recipe = witness_recipe(&fixture);
    let mut metadata: serde_json::Value =
        serde_json::from_slice(&fs::read(fixture.path("noctium.json")).unwrap()).unwrap();
    metadata.as_object_mut().unwrap().remove("hostWitnessPlans");
    fs::write(fixture.path("noctium.json"), metadata.to_string()).unwrap();
    assert_eq!(
        failure(artifacts::assemble(recipe, &fixture.path("unreferenced"))),
        "plan_mismatch"
    );

    for (index, mutation) in ["relation", "input", "target", "unknown"]
        .into_iter()
        .enumerate()
    {
        let recipe = witness_recipe(&fixture);
        let mut binding: serde_json::Value =
            serde_json::from_slice(&fs::read(fixture.path("call.witness.json")).unwrap()).unwrap();
        match mutation {
            "relation" => binding["nativeRelation"]["do_communications_commitment"] = json!(false),
            "input" => {
                binding["circuitInputs"] =
                    json!([{"name":"forged","type":"Native","visibility":"private"}])
            }
            "target" => binding["target"]["entrypoint"] = json!("different"),
            _ => binding["unknown"] = json!(true),
        }
        write_witness_pair(&fixture, &binding);
        assert_eq!(
            failure(artifacts::assemble(
                recipe,
                &fixture.path(&format!("mutated-{index}"))
            )),
            "plan_mismatch"
        );
    }
}

#[test]
fn typed_witness_role_bounds_apply_before_json_parse() {
    let fixture = Fixture::new();
    let recipe = witness_recipe(&fixture);
    fs::write(fixture.path("call.witness.json"), vec![b' '; 524_289]).unwrap();
    assert_eq!(
        failure(artifacts::assemble(
            recipe,
            &fixture.path("oversize-binding")
        )),
        "limit_exceeded"
    );
    let recipe = witness_recipe(&fixture);
    fs::write(
        fixture.path("call.witness.control.json"),
        vec![b' '; 1_048_577],
    )
    .unwrap();
    assert_eq!(
        failure(artifacts::assemble(
            recipe,
            &fixture.path("oversize-control")
        )),
        "limit_exceeded"
    );
}
fn failure<T>(result: artifacts::Result<T>) -> String {
    match result {
        Ok(_) => panic!("expected rejection"),
        Err(error) => error.code.into(),
    }
}
fn rewrite_manifest(root: &Path, manifest: &Manifest) {
    fs::write(
        root.join("manifest.json"),
        artifacts::manifest_bytes(manifest).unwrap(),
    )
    .unwrap();
}

#[test]
fn assembly_is_canonical_order_independent_and_retains_verified_bytes() {
    let fixture = Fixture::new();
    let first = fixture.assemble("first");
    let mut recipe = fixture.recipe();
    recipe.files.reverse();
    let second = artifacts::assemble(recipe, &fixture.path("second")).unwrap();
    assert_eq!(first, second);
    assert_eq!(
        fs::read(fixture.path("first/manifest.json")).unwrap(),
        fs::read(fixture.path("second/manifest.json")).unwrap()
    );
    let bytes = artifacts::manifest_bytes(&first).unwrap();
    assert!(
        !String::from_utf8(bytes.clone())
            .unwrap()
            .contains("/private/")
    );
    let bundle =
        artifacts::verify(&fixture.path("first"), Some(&artifacts::digest(&bytes))).unwrap();
    assert!(
        !String::from_utf8(bundle.file(Role::Toolchain).unwrap().to_vec())
            .unwrap()
            .contains("/private/local")
    );
    fs::write(
        fixture.path("first/source/examples/Contract.lean"),
        "changed later",
    )
    .unwrap();
    assert_eq!(
        bundle.source("examples/Contract.lean").unwrap(),
        b"import Noctium\n"
    );
    assert_eq!(
        failure(artifacts::assemble(
            fixture.recipe(),
            &fixture.path("first")
        )),
        "destination_exists"
    );
}

#[test]
fn memory_bundle_checks_manifest_before_reading_payloads() {
    let fixture = Fixture::new();
    let manifest = fixture.assemble("bundle");
    let bytes = artifacts::manifest_bytes(&manifest).unwrap();
    let pin = artifacts::digest(&bytes);
    let count = manifest.entries.len();
    let total = manifest.entries.iter().map(|entry| entry.size).sum::<u64>();
    for (expected, limit, actual_count, code) in [
        ("0".repeat(64), total, count, "manifest_digest_mismatch"),
        (pin.clone(), total - 1, count, "limit_exceeded"),
        (pin.clone(), total, count - 1, "unexpected_file"),
    ] {
        assert_eq!(
            failure(artifacts::verify_memory_with_limit(
                &bytes, &expected, limit, actual_count, |_, _| {
                    panic!("untrusted payload read")
                },
            )),
            code
        );
    }
    let bundle = artifacts::verify_memory_with_limit(&bytes, &pin, total, count, |index, size| {
        let file = fs::read(fixture.path("bundle").join(&manifest.entries[index].path)).unwrap();
        assert_eq!(file.len(), size);
        Some(file)
    })
    .unwrap();
    assert_eq!(bundle.authenticated_manifest_sha256(), Some(pin.as_str()));
    assert_eq!(bundle.manifest(), &manifest);
}

#[test]
fn every_payload_role_rejects_same_length_tampering() {
    let fixture = Fixture::new();
    let manifest = fixture.assemble("bundle");
    for entry in &manifest.entries {
        let path = fixture.path("bundle").join(&entry.path);
        let original = fs::read(&path).unwrap();
        let mut changed = original.clone();
        changed[0] ^= 1;
        fs::write(&path, changed).unwrap();
        assert_eq!(
            failure(artifacts::verify(&fixture.path("bundle"), None)),
            "digest_mismatch",
            "{:?}",
            entry.role
        );
        fs::write(path, original).unwrap();
    }
}

#[test]
fn unsupported_profiles_releases_and_plan_associations_reject() {
    let fixture = Fixture::new();
    let original = fs::read(fixture.path("target.json")).unwrap();
    let mut profile: serde_json::Value = serde_json::from_slice(&original).unwrap();
    profile["zkir"] = json!(if cfg!(feature = "zkir-321") {
        "3.2.0"
    } else {
        "3.2.1"
    });
    fs::write(fixture.path("target.json"), profile.to_string()).unwrap();
    assert_eq!(
        failure(artifacts::assemble(
            fixture.recipe(),
            &fixture.path("bad-profile")
        )),
        "profile_mismatch"
    );
    assert!(!fixture.path("bad-profile").exists());
    fs::write(fixture.path("target.json"), original).unwrap();
    let mut plan: serde_json::Value =
        serde_json::from_slice(&fs::read(fixture.path("entry.impact.json")).unwrap()).unwrap();
    plan["nativeCircuitFile"] = json!("Other.call.zkir");
    fs::write(fixture.path("entry.impact.json"), plan.to_string()).unwrap();
    assert_eq!(
        failure(artifacts::assemble(
            fixture.recipe(),
            &fixture.path("bad-plan")
        )),
        "plan_mismatch"
    );
}

#[test]
fn private_material_traversal_duplicate_roles_and_missing_roles_reject() {
    let fixture = Fixture::new();
    let mut recipe = fixture.recipe();
    recipe.files[0].name = "../outside.lean".into();
    assert_eq!(
        failure(artifacts::assemble(recipe, &fixture.path("escape"))),
        "unsafe_path"
    );
    let mut recipe = fixture.recipe();
    recipe.files[0].name = "/absolute.lean".into();
    assert_eq!(
        failure(artifacts::assemble(recipe, &fixture.path("absolute"))),
        "unsafe_path"
    );
    let mut recipe = fixture.recipe();
    recipe.files[0].name = "directory\\outside.lean".into();
    assert_eq!(
        failure(artifacts::assemble(recipe, &fixture.path("backslash"))),
        "unsafe_path"
    );
    for name in [
        "runtime-config.json",
        "claim-witness.json",
        "private-state.json",
        "checker-preimage.json",
    ] {
        fs::write(fixture.path(name), "private").unwrap();
        let mut recipe = fixture.recipe();
        recipe.files[0].input = fixture.path(name);
        assert_eq!(
            failure(artifacts::assemble(recipe, &fixture.path("private"))),
            "private_artifact"
        );
    }
    fs::write(fixture.path("inputs.json"), "private").unwrap();
    let mut recipe = fixture.recipe();
    recipe.files[0].input = fixture.path("inputs.json");
    assert_eq!(
        failure(artifacts::assemble(
            recipe,
            &fixture.path("mislabeled-json")
        )),
        "invalid_role"
    );
    let mut recipe = fixture.recipe();
    recipe
        .files
        .push(fixture.selection(Role::Circuit, "Other.call.zkir", "entry.zkir"));
    assert_eq!(
        failure(artifacts::assemble(recipe, &fixture.path("duplicate"))),
        "duplicate_role"
    );
    let mut recipe = fixture.recipe();
    recipe.files.pop();
    assert_eq!(
        failure(artifacts::assemble(recipe, &fixture.path("missing"))),
        "missing_role"
    );
    let mut recipe = fixture.recipe();
    recipe.files.push(fixture.selection(
        Role::Source,
        "examples/Contract.lean/Child.lean",
        "Contract.lean",
    ));
    assert_eq!(
        failure(artifacts::assemble(
            recipe,
            &fixture.path("prefix-conflict")
        )),
        "duplicate_path"
    );
    let mut recipe = fixture.recipe();
    recipe
        .files
        .push(fixture.selection(Role::Source, "examples/contract.lean", "Contract.lean"));
    assert_eq!(
        failure(artifacts::assemble(recipe, &fixture.path("case-conflict"))),
        "duplicate_path"
    );
}

#[test]
fn shared_directory_prefixes_require_consistent_casing_before_writing() {
    let fixture = Fixture::new();
    for (first, second, destination) in [
        ("Foo/A.lean", "foo/B.lean", "root-case-alias"),
        ("Foo/Bar/A.lean", "Foo/bar/B.lean", "nested-case-alias"),
        ("Source/A.lean", "source/B.lean", "source-case-alias"),
    ] {
        let mut recipe = fixture.recipe();
        recipe.files[0].name = first.into();
        recipe
            .files
            .push(fixture.selection(Role::Source, second, "Contract.lean"));
        assert_eq!(
            failure(artifacts::assemble(recipe, &fixture.path(destination))),
            "duplicate_path"
        );
        assert!(
            !fixture.path(destination).exists(),
            "conflict must reject before creating output"
        );
    }
    let mut recipe = fixture.recipe();
    recipe.files[0].name = "Foo/A.lean".into();
    recipe
        .files
        .push(fixture.selection(Role::Source, "Foo/B.lean", "Contract.lean"));
    artifacts::assemble(recipe, &fixture.path("consistent-prefix")).unwrap();
    assert!(artifacts::verify(&fixture.path("consistent-prefix"), None).is_ok());
}

#[test]
fn unicode_logical_names_reject_before_filesystem_normalization() {
    let fixture = Fixture::new();
    let mut recipe = fixture.recipe();
    recipe.files[0].name = "é/A.lean".into();
    recipe
        .files
        .push(fixture.selection(Role::Source, "e\u{301}/B.lean", "Contract.lean"));
    assert_eq!(
        failure(artifacts::assemble(
            recipe,
            &fixture.path("normalization-alias")
        )),
        "unsupported_name"
    );
    assert!(!fixture.path("normalization-alias").exists());

    // The portable logical label does not restrict physical input names or source contents.
    fs::write(fixture.path("é.lean"), "def café := 1\n").unwrap();
    let mut recipe = fixture.recipe();
    recipe.files[0].input = fixture.path("é.lean");
    artifacts::assemble(recipe, &fixture.path("unicode-input")).unwrap();
    let bundle = artifacts::verify(&fixture.path("unicode-input"), None).unwrap();
    assert_eq!(
        bundle.source("examples/Contract.lean").unwrap(),
        "def café := 1\n".as_bytes()
    );
}

#[test]
fn private_values_in_unknown_plan_fields_and_wrong_native_source_pin_reject() {
    let fixture = Fixture::new();
    let original = fs::read(fixture.path("entry.impact.json")).unwrap();
    let mut plan: serde_json::Value = serde_json::from_slice(&original).unwrap();
    plan["witnessValues"] = json!({"secret":"42"});
    fs::write(fixture.path("entry.impact.json"), plan.to_string()).unwrap();
    assert_eq!(
        failure(artifacts::assemble(
            fixture.recipe(),
            &fixture.path("private-plan")
        )),
        "unsupported_schema"
    );
    fs::write(fixture.path("entry.impact.json"), original).unwrap();
    let mut provenance: serde_json::Value =
        serde_json::from_slice(&fs::read(fixture.path("tool.json")).unwrap()).unwrap();
    provenance["revision"] = json!("0".repeat(40));
    fs::write(fixture.path("tool.json"), provenance.to_string()).unwrap();
    assert_eq!(
        failure(artifacts::assemble(
            fixture.recipe(),
            &fixture.path("wrong-tool")
        )),
        "profile_mismatch"
    );
}

#[test]
fn manifest_versions_unknown_fields_and_noncanonical_encoding_reject() {
    let fixture = Fixture::new();
    let mut manifest = fixture.assemble("bundle");
    manifest.schema_version = 2;
    rewrite_manifest(&fixture.path("bundle"), &manifest);
    assert_eq!(
        failure(artifacts::verify(&fixture.path("bundle"), None)),
        "unsupported_version"
    );
    manifest.schema_version = 1;
    manifest.entries[0].path = "../Contract.lean".into();
    rewrite_manifest(&fixture.path("bundle"), &manifest);
    assert_eq!(
        failure(artifacts::verify(&fixture.path("bundle"), None)),
        "unsafe_path"
    );
    let manifest = fixture.assemble("original");
    let mut value = serde_json::to_value(&manifest).unwrap();
    value["unknown"] = json!(true);
    fs::write(fixture.path("original/manifest.json"), value.to_string()).unwrap();
    assert_eq!(
        failure(artifacts::verify(&fixture.path("original"), None)),
        "invalid_manifest"
    );
    fs::write(
        fixture.path("original/manifest.json"),
        serde_json::to_vec_pretty(&manifest).unwrap(),
    )
    .unwrap();
    assert_eq!(
        failure(artifacts::verify(&fixture.path("original"), None)),
        "noncanonical_manifest"
    );
}

#[test]
fn unsigned_manifest_replacement_needs_external_digest_to_authenticate() {
    let fixture = Fixture::new();
    let mut manifest = fixture.assemble("bundle");
    let expected = artifacts::digest(&artifacts::manifest_bytes(&manifest).unwrap());
    let source = manifest
        .entries
        .iter_mut()
        .find(|entry| entry.role == Role::Source)
        .unwrap();
    let new = b"altered source\n";
    fs::write(fixture.path("bundle").join(&source.path), new).unwrap();
    source.size = new.len() as u64;
    source.sha256 = artifacts::digest(new);
    rewrite_manifest(&fixture.path("bundle"), &manifest);
    assert!(artifacts::verify(&fixture.path("bundle"), None).is_ok());
    assert_eq!(
        failure(artifacts::verify(&fixture.path("bundle"), Some(&expected))),
        "manifest_digest_mismatch"
    );
}

#[test]
fn unlisted_and_missing_files_reject() {
    let fixture = Fixture::new();
    fixture.assemble("bundle");
    fs::write(fixture.path("bundle/witness.json"), "secret").unwrap();
    assert_eq!(
        failure(artifacts::verify(&fixture.path("bundle"), None)),
        "unexpected_file"
    );
    fs::remove_file(fixture.path("bundle/witness.json")).unwrap();
    fs::remove_file(fixture.path("bundle/keys/entrypoint.verifier")).unwrap();
    assert_eq!(
        failure(artifacts::verify(&fixture.path("bundle"), None)),
        "io_error"
    );
}

#[cfg(unix)]
#[test]
fn symlinks_in_sources_payloads_or_bundle_roots_reject() {
    use std::os::unix::fs::symlink;
    let fixture = Fixture::new();
    symlink(fixture.path("Contract.lean"), fixture.path("link.lean")).unwrap();
    let mut recipe = fixture.recipe();
    recipe.files[0].input = fixture.path("link.lean");
    assert_eq!(
        failure(artifacts::assemble(recipe, &fixture.path("source-link"))),
        "unsafe_path"
    );
    fixture.assemble("bundle");
    symlink(fixture.path("bundle"), fixture.path("bundle-link")).unwrap();
    assert_eq!(
        failure(artifacts::verify(&fixture.path("bundle-link"), None)),
        "unsafe_path"
    );
    fs::remove_file(fixture.path("bundle/source/examples/Contract.lean")).unwrap();
    symlink(
        fixture.path("Contract.lean"),
        fixture.path("bundle/source/examples/Contract.lean"),
    )
    .unwrap();
    assert_eq!(
        failure(artifacts::verify(&fixture.path("bundle"), None)),
        "unsafe_path"
    );
}

#[test]
fn manifest_consumer_rejects_other_linked_native_profile() {
    let fixture = Fixture::new();
    let mut manifest = fixture.assemble("selected");
    assert_eq!(manifest.zkir_revision, noctium_runtime::profile::REVISION);
    assert_eq!(manifest.profile, noctium_runtime::profile::NAME);
    manifest.profile = if cfg!(feature = "zkir-321") {
        "midnight-ledger-9"
    } else {
        "midnight-ledger-9-zkir-3.2.1"
    }
    .into();
    manifest.zkir_revision = if cfg!(feature = "zkir-321") {
        "446c7fecc6bd41dab99ebe89ab404e9d077d11a9"
    } else {
        "7a51b3385bbf4bce3604df87a7c70867c9ab43c0"
    }
    .into();
    rewrite_manifest(&fixture.path("selected"), &manifest);
    assert_eq!(
        failure(artifacts::verify(&fixture.path("selected"), None)),
        "profile_mismatch"
    );
}
#[test]
fn tool_release_label_and_source_revision_cannot_be_mixed() {
    let fixture = Fixture::new();
    let original = fs::read(fixture.path("tool.json")).unwrap();
    for (field, value) in [
        (
            "releaseLabel",
            json!(if cfg!(feature = "zkir-321") {
                "3.2.0"
            } else {
                "3.2.1"
            }),
        ),
        ("expectedCliVersion", json!("3.2.1")),
        (
            "revision",
            json!(if cfg!(feature = "zkir-321") {
                "446c7fecc6bd41dab99ebe89ab404e9d077d11a9"
            } else {
                "7a51b3385bbf4bce3604df87a7c70867c9ab43c0"
            }),
        ),
    ] {
        let mut provenance: serde_json::Value = serde_json::from_slice(&original).unwrap();
        provenance[field] = value;
        fs::write(fixture.path("tool.json"), provenance.to_string()).unwrap();
        assert_eq!(
            failure(artifacts::assemble(
                fixture.recipe(),
                &fixture.path("mixed-tool")
            )),
            "profile_mismatch"
        );
        assert!(!fixture.path("mixed-tool").exists());
    }
}

#[test]
fn present_nonstring_plan_target_never_falls_back_to_legacy_profile() {
    let fixture = Fixture::new();
    let original = fs::read(fixture.path("entry.impact.json")).unwrap();
    for target in [
        json!(321),
        json!({"profile":"midnight-ledger-9-zkir-3.2.1"}),
        serde_json::Value::Null,
    ] {
        let mut plan: serde_json::Value = serde_json::from_slice(&original).unwrap();
        plan.as_object_mut().unwrap().remove("targetProfile");
        plan["target"] = target;
        fs::write(fixture.path("entry.impact.json"), plan.to_string()).unwrap();
        assert_eq!(
            failure(artifacts::assemble(
                fixture.recipe(),
                &fixture.path("bad-target-type")
            )),
            "profile_mismatch"
        );
        assert!(!fixture.path("bad-target-type").exists());
    }
}

#[test]
fn host_payload_budget_rejects_authenticated_total_before_payload_reads() {
    let fixture = Fixture::new();
    let manifest = fixture.assemble("bounded");
    let bytes = artifacts::manifest_bytes(&manifest).unwrap();
    let pin = artifacts::digest(&bytes);
    let root = fixture.path("bounded");
    let total = manifest.entries.iter().map(|e| e.size).sum::<u64>();
    assert!(artifacts::verify_with_limit(&root, Some(&pin), total).is_ok());
    for entry in &manifest.entries {
        fs::remove_file(root.join(&entry.path)).unwrap();
    }
    assert_eq!(
        failure(artifacts::verify_with_limit(&root, Some(&pin), total - 1)),
        "limit_exceeded"
    );
    assert_eq!(
        failure(artifacts::verify_with_limit(
            &root,
            Some(&"0".repeat(64)),
            total - 1
        )),
        "manifest_digest_mismatch"
    );
    assert_eq!(
        failure(artifacts::verify_with_limit(&root, Some(&pin), total)),
        "io_error"
    );
    assert_eq!(failure(artifacts::verify(&root, Some(&pin))), "io_error");
}

#[test]
fn contract_bundle_set_joins_alias_operations_with_stable_identity() {
    let fixture = Fixture::new();
    let operations = ["claim", "claimAlias"];
    let state = json!([]);
    let claim = fixture.verified_operation(
        "claim-bundle",
        operations[0],
        &operations,
        &"c".repeat(40),
        &state,
    );
    let alias = fixture.verified_operation(
        "alias-bundle",
        operations[1],
        &operations,
        &"c".repeat(40),
        &state,
    );
    assert_eq!(
        claim.file(Role::Circuit).unwrap(),
        alias.file(Role::Circuit).unwrap()
    );
    assert_eq!(
        claim.file(Role::VerifierKey).unwrap(),
        alias.file(Role::VerifierKey).unwrap()
    );
    let set = ContractBundleSet::new(vec![claim, alias]).unwrap();
    assert_eq!(set.contract_name(), "Contract");
    assert_eq!(set.len(), 2);
    assert!(set.operation("claim").is_some());
    assert_eq!(
        set.iter().map(|(name, _)| name).collect::<Vec<_>>(),
        ["claim", "claimAlias"]
    );
    let identity = set.identity().to_owned();

    let claim = fixture.verified_operation(
        "claim-bundle-reversed",
        operations[0],
        &operations,
        &"c".repeat(40),
        &state,
    );
    let alias = fixture.verified_operation(
        "alias-bundle-reversed",
        operations[1],
        &operations,
        &"c".repeat(40),
        &state,
    );
    assert_eq!(
        ContractBundleSet::new(vec![alias, claim])
            .unwrap()
            .identity(),
        identity
    );
}

#[test]
fn contract_bundle_set_requires_each_exported_operation_once() {
    let fixture = Fixture::new();
    let operations = ["claim", "claimAlias"];
    let state = json!([]);
    let claim = fixture.verified_operation(
        "missing-operation",
        operations[0],
        &operations,
        &"c".repeat(40),
        &state,
    );
    assert_eq!(
        failure(ContractBundleSet::new(vec![claim])),
        "missing_operation"
    );

    let only = ["claim"];
    let first = fixture.verified_operation(
        "duplicate-operation-a",
        only[0],
        &only,
        &"c".repeat(40),
        &state,
    );
    let second = fixture.verified_operation(
        "duplicate-operation-b",
        only[0],
        &only,
        &"c".repeat(40),
        &state,
    );
    assert_eq!(
        failure(ContractBundleSet::new(vec![first, second])),
        "duplicate_operation"
    );

    let duplicated_exports = ["claim", "claimAlias", "claimAlias"];
    let bundle = fixture.verified_operation(
        "duplicate-export-name",
        "claim",
        &duplicated_exports,
        &"c".repeat(40),
        &state,
    );
    assert_eq!(
        failure(ContractBundleSet::new(vec![bundle])),
        "duplicate_operation"
    );
}

#[test]
fn contract_bundle_set_requires_shared_authority_metadata_source_and_parameters() {
    let state = json!([]);
    let operations = ["claim", "claimAlias"];

    let fixture = Fixture::new();
    let first = fixture.verified_operation(
        "authority-a",
        operations[0],
        &operations,
        &"c".repeat(40),
        &state,
    );
    let second = fixture.verified_operation(
        "authority-b",
        operations[1],
        &operations,
        &"d".repeat(40),
        &state,
    );
    assert_eq!(
        failure(ContractBundleSet::new(vec![first, second])),
        "authority_mismatch"
    );

    let fixture = Fixture::new();
    let first = fixture.verified_operation(
        "source-name-a",
        operations[0],
        &operations,
        &"c".repeat(40),
        &state,
    );
    fixture.configure_operations(&operations, &state);
    let mut recipe = fixture.operation_recipe(operations[1], &"c".repeat(40));
    recipe
        .files
        .iter_mut()
        .find(|selection| selection.role == Role::Source)
        .unwrap()
        .name = "examples/ContractAlias.lean".into();
    let manifest = artifacts::assemble(recipe, &fixture.path("source-name-b")).unwrap();
    let pin = artifacts::digest(&artifacts::manifest_bytes(&manifest).unwrap());
    let second = artifacts::verify(&fixture.path("source-name-b"), Some(&pin)).unwrap();
    assert_eq!(
        failure(ContractBundleSet::new(vec![first, second])),
        "authority_mismatch"
    );

    let fixture = Fixture::new();
    let first = fixture.verified_operation(
        "source-a",
        operations[0],
        &operations,
        &"c".repeat(40),
        &state,
    );
    fs::write(
        fixture.path("Contract.lean"),
        b"import Noctium\n-- changed source\n",
    )
    .unwrap();
    let second = fixture.verified_operation(
        "source-b",
        operations[1],
        &operations,
        &"c".repeat(40),
        &state,
    );
    assert_eq!(
        failure(ContractBundleSet::new(vec![first, second])),
        "authority_mismatch"
    );

    let fixture = Fixture::new();
    let first = fixture.verified_operation(
        "parameters-a",
        operations[0],
        &operations,
        &"c".repeat(40),
        &state,
    );
    fs::write(
        fixture.path("ledger.params"),
        b"different public ledger parameters",
    )
    .unwrap();
    let second = fixture.verified_operation(
        "parameters-b",
        operations[1],
        &operations,
        &"c".repeat(40),
        &state,
    );
    assert_eq!(
        failure(ContractBundleSet::new(vec![first, second])),
        "parameter_mismatch"
    );

    let fixture = Fixture::new();
    let first = fixture.verified_operation(
        "schema-a",
        operations[0],
        &operations,
        &"c".repeat(40),
        &state,
    );
    let changed_state = json!([{"name":"counter","type":"UInt"}]);
    let second = fixture.verified_operation(
        "schema-b",
        operations[1],
        &operations,
        &"c".repeat(40),
        &changed_state,
    );
    assert_eq!(
        failure(ContractBundleSet::new(vec![first, second])),
        "plan_mismatch"
    );
}

#[test]
fn contract_bundle_set_rejects_unpinned_zero_authority_and_profile_mismatch() {
    let fixture = Fixture::new();
    let operation = ["claim"];
    let state = json!([]);
    fixture.configure_operations(&operation, &state);
    let manifest = artifacts::assemble(
        fixture.operation_recipe(operation[0], &"c".repeat(40)),
        &fixture.path("unsigned-set-bundle"),
    )
    .unwrap();
    let unpinned = artifacts::verify(&fixture.path("unsigned-set-bundle"), None).unwrap();
    assert_eq!(
        failure(ContractBundleSet::new(vec![unpinned])),
        "missing_authority"
    );
    let zero_authority = fixture.verified_operation(
        "zero-authority",
        operation[0],
        &operation,
        &"0".repeat(40),
        &state,
    );
    assert_eq!(
        failure(ContractBundleSet::new(vec![zero_authority])),
        "invalid_provenance"
    );

    let mut wrong_profile = manifest;
    wrong_profile.profile = if cfg!(feature = "zkir-321") {
        "midnight-ledger-9"
    } else {
        "midnight-ledger-9-zkir-3.2.1"
    }
    .into();
    rewrite_manifest(&fixture.path("unsigned-set-bundle"), &wrong_profile);
    assert_eq!(
        failure(artifacts::verify(
            &fixture.path("unsigned-set-bundle"),
            None
        )),
        "profile_mismatch"
    );
}

#[test]
fn selected_entrypoint_association_mismatch_rejects_before_set_creation() {
    let fixture = Fixture::new();
    let operations = ["claim", "claimAlias"];
    fixture.configure_operations(&operations, &json!([]));
    let mut metadata: Value =
        serde_json::from_slice(&fs::read(fixture.path("noctium.json")).unwrap()).unwrap();
    metadata["contracts"][0]["entrypoints"][0]["nativeCircuitFile"] =
        json!("Contract.claimAlias.zkir");
    fs::write(fixture.path("noctium.json"), metadata.to_string()).unwrap();
    assert_eq!(
        failure(artifacts::assemble(
            fixture.operation_recipe("claim", &"c".repeat(40)),
            &fixture.path("swapped-operation")
        )),
        "plan_mismatch"
    );
}
