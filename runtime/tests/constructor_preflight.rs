#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use noctium_runtime::{
    Db, Plan, check, constructor::deployment_state, prepare, zkir::IrSource,
};
use onchain_runtime::state::ContractState;
use rand::{Rng, rngs::OsRng};
use serde_json::{Value as Json, json};
use serialize::{Serializable, Tagged, tagged_serialize};
use std::{
    collections::BTreeMap,
    env, fs,
    path::{Path, PathBuf},
    process::{Command, Output},
};

struct Fixture(PathBuf);

impl Fixture {
    fn new() -> Self {
        let path = env::temp_dir().join(format!(
            "noctium-constructor-preflight-{}",
            OsRng.r#gen::<u64>()
        ));
        fs::create_dir(&path).unwrap();
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(&path, fs::Permissions::from_mode(0o700)).unwrap();
        }
        fs::create_dir(path.join("zkir")).unwrap();
        Self(path)
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn encoded<T: Serializable + Tagged>(value: &T) -> Vec<u8> {
    let mut bytes = Vec::new();
    tagged_serialize(value, &mut bytes).unwrap();
    bytes
}

fn write(root: &Path, name: &str, bytes: &[u8]) {
    fs::write(root.join(name), bytes).unwrap();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(root.join(name), fs::Permissions::from_mode(0o600)).unwrap();
    }
}

fn run(root: &Path) -> Output {
    Command::new(env!("CARGO_BIN_EXE_noctium-runtime"))
        .arg(root)
        .env_clear()
        .env("PATH", "/usr/bin:/bin")
        .output()
        .unwrap()
}

#[test]
#[ignore = "requires fresh ConstructorPreflight.inspect artifacts in NOCTIUM_CONSTRUCTOR_PREFLIGHT_DIR"]
fn constructor_preflight_uses_seed_and_rejects_bad_argument() {
    let artifacts = PathBuf::from(
        env::var_os("NOCTIUM_CONSTRUCTOR_PREFLIGHT_DIR")
            .expect("NOCTIUM_CONSTRUCTOR_PREFLIGHT_DIR"),
    );
    let stem = "ConstructorPreflight.inspect";
    let plan_bytes = fs::read(artifacts.join(format!("{stem}.impact.json"))).unwrap();
    let circuit_bytes = fs::read(artifacts.join(format!("{stem}.zkir"))).unwrap();
    let plan: Plan = serde_json::from_slice(&plan_bytes).unwrap();
    let circuit = IrSource::load(circuit_bytes.as_slice()).unwrap();

    assert_eq!(plan.entrypoint, "inspect");
    assert!(plan.state.iter().any(|slot| slot.name == "initialAmount"));
    assert_eq!(
        plan.constructor
            .as_ref()
            .unwrap()
            .parameters
            .iter()
            .map(|parameter| parameter.name.as_str())
            .collect::<Vec<_>>(),
        ["seedValue"]
    );

    let constructor_arguments = BTreeMap::from([("seedValue".into(), json!("19"))]);
    let initial = deployment_state(&plan, &constructor_arguments).unwrap();
    let inputs = BTreeMap::from([("allowCall".into(), json!(true))]);
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let execution = prepare(
        &plan,
        &inputs,
        &initial,
        parameters,
        ContractAddress::default(),
    )
    .unwrap();
    check(&execution, &circuit).unwrap();
    assert_eq!(
        serde_json::to_value(execution.returns_json()).unwrap(),
        json!({"amountResult":"19"})
    );
    assert_ne!(execution.after.state, initial);

    let fixture = Fixture::new();
    write(&fixture.0, "source-plan.json", &plan_bytes);
    write(
        &fixture.0,
        "zkir/inspect.zkir",
        &circuit_bytes,
    );
    write(
        &fixture.0,
        "ledger.params",
        &encoded(parameters),
    );
    write(
        &fixture.0,
        "native-contract.json",
        serde_json::to_vec(&json!({"address":"00".repeat(32)}))
            .unwrap()
            .as_slice(),
    );
    write(
        &fixture.0,
        "runtime-config.json",
        serde_json::to_vec(&json!({
            "inputs": inputs,
            "state": constructor_arguments,
            "negativeCases": [{"name":"call-not-allowed","inputs":{"allowCall":false}}]
        }))
        .unwrap()
        .as_slice(),
    );

    let mut initial_contract = ContractState::<Db>::default();
    initial_contract.data = initial;
    let mut predicted_contract = initial_contract.clone();
    predicted_contract.data = execution.after.state;
    write(
        &fixture.0,
        "initial-state.bin",
        &encoded(&initial_contract),
    );
    write(
        &fixture.0,
        "predicted-state.bin",
        &encoded(&predicted_contract),
    );

    let output = run(&fixture.0);
    assert!(
        output.status.success(),
        "preflight failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let result: Json = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(result["runtime"], json!("native Rust"));
    assert_eq!(result["nodeInvoked"], json!(false));
    assert_eq!(result["initialStateMatches"], json!(true));
    assert_eq!(result["predictedStateMatches"], json!(true));
    assert_eq!(result["validCheck"], json!(true));
    assert_eq!(result["negativeChecks"][0]["name"], json!("call-not-allowed"));
    assert_eq!(result["negativeChecks"][0]["rejected"], json!(true));
    assert_eq!(result["replayRejected"], json!(true));
    assert_eq!(result["stateUnchangedOnRejection"], json!(true));

    write(
        &fixture.0,
        "runtime-config.json",
        serde_json::to_vec(&json!({
            "inputs": {"allowCall": true},
            "state": {"seedValue": "65536"},
            "negativeCases": [{"name":"call-not-allowed","inputs":{"allowCall":false}}]
        }))
        .unwrap()
        .as_slice(),
    );
    let invalid_constructor_argument = run(&fixture.0);
    assert!(!invalid_constructor_argument.status.success());
    assert!(invalid_constructor_argument.stdout.is_empty());
}
