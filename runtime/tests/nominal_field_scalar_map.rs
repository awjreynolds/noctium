#![cfg(feature = "zkir-321")]

use noctium_runtime::{Db, Plan, check, create_state, prepare, zkir::IrSource};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;

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

#[test]
fn root_map_with_nominal_field_key_replays_insert_default_remove_lifecycle() {
    let plan: Plan = serde_json::from_str(PLAN).unwrap();
    let circuit = IrSource::load(CIRCUIT).unwrap();
    let initial = create_state(&plan, &BTreeMap::from([("balances".into(), json!([]))])).unwrap();
    assert_eq!(map_size(&initial), 0);

    let execution = prepare(
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
    .unwrap();
    assert_eq!(check(&execution, &circuit).unwrap(), execution.activity_schedule);
    assert_eq!(execution.returns_json()["wasInserted"], json!(true));
    assert_eq!(execution.returns_json()["storedValue"], json!("42"));
    assert_eq!(execution.returns_json()["defaultValue"], json!("0"));
    assert_eq!(execution.returns_json()["remains"], json!(false));
    assert_eq!(map_size(&execution.after.state), 0);
}
