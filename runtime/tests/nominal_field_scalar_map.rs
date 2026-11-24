#![cfg(feature = "zkir-321")]

use futures::executor::block_on;
use noctium_runtime::{
    Db, Execution, Plan, check, create_state, prepare, proof::TrustedParameters, zkir::IrSource,
};
use onchain_runtime::state::{ChargedState, StateValue};
use rand::rngs::OsRng;
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use transient_crypto::{
    curve::Fr,
    proofs::{ParamsVerifier, Zkir},
};

const PLAN: &str = include_str!(
    "fixtures/nominal-field-scalar-map/321/NominalFieldScalarMap.ScalarMap.lifecycle.impact.json"
);
const CIRCUIT: &[u8] = include_bytes!(
    "fixtures/nominal-field-scalar-map/321/NominalFieldScalarMap.ScalarMap.lifecycle.zkir"
);

fn map_size(state: &ChargedState<Db>) -> usize {
    let StateValue::Array(values) = state.get_ref() else {
        panic!("expected contract state array");
    };
    let StateValue::Map(map) = values.get(0).expect("balances root map exists") else {
        panic!("expected balances root map");
    };
    map.size()
}

fn prepare_lifecycle() -> Execution {
    let plan: Plan = serde_json::from_str(PLAN).unwrap();
    let initial = create_state(&plan, &BTreeMap::from([("balances".into(), json!([]))])).unwrap();
    assert_eq!(map_size(&initial), 0);

    prepare(
        &plan,
        &BTreeMap::<String, Json>::from([
            ("key".into(), json!("17")),
            ("value".into(), json!("42")),
            ("enabled".into(), json!(true)),
        ]),
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .unwrap()
}

#[test]
fn root_map_with_nominal_field_key_replays_insert_default_remove_lifecycle() {
    let circuit = IrSource::load(CIRCUIT).unwrap();
    let execution = prepare_lifecycle();
    assert_eq!(
        check(&execution, &circuit).unwrap(),
        execution.activity_schedule
    );
    assert_eq!(execution.returns_json()["wasInserted"], json!(true));
    assert_eq!(execution.returns_json()["storedValue"], json!("42"));
    assert_eq!(execution.returns_json()["defaultValue"], json!("0"));
    assert_eq!(execution.returns_json()["remains"], json!(false));
    assert_eq!(map_size(&execution.after.state), 0);
}

#[test]
#[ignore = "requires the pinned k8 SRS in NOCTIUM_ROOT_MAP_K8_SRS"]
fn root_map_lifecycle_proves_and_binds_the_statement() {
    const K: u8 = 8;
    const K8_SRS_SHA256: &str = "909b707551eaaea79828e883cde6fc46ab15986c3b1d791bed462c9e2805c933";
    let srs_path = std::env::var_os("NOCTIUM_ROOT_MAP_K8_SRS")
        .expect("set NOCTIUM_ROOT_MAP_K8_SRS to the pinned k8 SRS");
    let srs = std::fs::read(srs_path).unwrap();
    let parameters = TrustedParameters::from_bytes(&srs, K, K8_SRS_SHA256).unwrap();
    let verifier_parameters = ParamsVerifier::read(srs.as_slice()).unwrap();

    let circuit = IrSource::load(CIRCUIT).unwrap();
    assert_eq!(circuit.k(), K);
    let execution = prepare_lifecycle();
    assert_eq!(
        check(&execution, &circuit).unwrap(),
        execution.activity_schedule
    );
    let (prover, verifier) = block_on(circuit.keygen(&parameters)).unwrap();
    let (proof, statement, activity) =
        block_on(circuit.prove(OsRng, &parameters, prover, &execution.preimage)).unwrap();
    assert_eq!(activity, execution.activity_schedule);
    verifier
        .verify(&verifier_parameters, &proof, statement.iter().copied())
        .unwrap();

    let mut changed_statement = statement;
    changed_statement[0] = changed_statement[0] + Fr::from(1u64);
    assert!(
        verifier
            .verify(&verifier_parameters, &proof, changed_statement.into_iter())
            .is_err()
    );
}
