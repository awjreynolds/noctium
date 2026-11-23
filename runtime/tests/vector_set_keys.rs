#![cfg(feature = "zkir-321")]

use base_crypto::fab::AlignedValue;
use noctium_runtime::{Db, Plan, check, create_state, field_value, prepare, zkir::IrSource};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, path::Path};
use transient_crypto::curve::Fr;

fn vector_set_artifacts() -> std::path::PathBuf {
    std::env::var_os("NOCTIUM_VECTOR_SET_KEYS_DIR")
        .map(std::path::PathBuf::from)
        .expect("set NOCTIUM_VECTOR_SET_KEYS_DIR to fresh VectorSetKeys artifacts")
}

fn load_plan(directory: &Path, name: &str) -> Plan {
    serde_json::from_slice(&std::fs::read(directory.join(name)).unwrap()).unwrap()
}

fn load_circuit(directory: &Path, name: &str) -> IrSource {
    IrSource::load(std::fs::read(directory.join(name)).unwrap().as_slice()).unwrap()
}

fn update_inputs() -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("first".into(), json!("11")),
        ("second".into(), json!("22")),
        ("third".into(), json!("23")),
    ])
}

fn vector_key(first: u64, second: u64) -> AlignedValue {
    let leaves = [field_value(Fr::from(first)), field_value(Fr::from(second))];
    AlignedValue::concat(leaves.iter())
}

fn assert_vector_set(state: &ChargedState<Db>, expected: &[(u64, u64)]) {
    let StateValue::Array(slots) = state.get_ref() else {
        panic!("expected contract state array");
    };
    let StateValue::Map(set) = slots.get(0).expect("root Set slot exists") else {
        panic!("expected root Set-backed map");
    };
    assert_eq!(set.size(), expected.len());
    for (first, second) in expected {
        assert!(set.get(&vector_key(*first, *second)).is_some());
    }
}

#[test]
#[ignore = "requires fresh VectorSetKeys artifacts in NOCTIUM_VECTOR_SET_KEYS_DIR"]
fn root_vector_set_preserves_order_duplicates_removal_and_reset() -> anyhow::Result<()> {
    let directory = vector_set_artifacts();
    let update = load_plan(&directory, "VectorSetKeys.update.impact.json");
    let update_circuit = load_circuit(&directory, "VectorSetKeys.update.zkir");
    let remove = load_plan(&directory, "VectorSetKeys.remove.impact.json");
    let remove_circuit = load_circuit(&directory, "VectorSetKeys.remove.zkir");
    let reset = load_plan(&directory, "VectorSetKeys.reset.impact.json");
    let reset_circuit = load_circuit(&directory, "VectorSetKeys.reset.zkir");

    let mut state = create_state(&update, &BTreeMap::from([("vectorKeys".into(), json!([]))]))?;
    assert_vector_set(&state, &[]);

    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();

    let inserted = prepare(&update, &update_inputs(), &state, parameters, address)?;
    assert_eq!(
        check(&inserted, &update_circuit)?,
        inserted.activity_schedule
    );
    let inserted_returns = inserted.returns_json();
    assert_eq!(inserted_returns["containsA"], json!(true));
    assert_eq!(inserted_returns["containsB"], json!(true));
    assert_eq!(inserted_returns["containsC"], json!(true));
    assert_eq!(inserted_returns["keyCount"], json!("3"));
    state = inserted.after.state;
    assert_vector_set(&state, &[(11, 22), (11, 23), (22, 11)]);

    let removed = prepare(&remove, &update_inputs(), &state, parameters, address)?;
    assert_eq!(check(&removed, &remove_circuit)?, removed.activity_schedule);
    let removed_returns = removed.returns_json();
    assert_eq!(removed_returns["containsA"], json!(false));
    assert_eq!(removed_returns["containsB"], json!(true));
    assert_eq!(removed_returns["containsC"], json!(true));
    assert_eq!(removed_returns["keyCount"], json!("2"));
    state = removed.after.state;
    assert_vector_set(&state, &[(11, 23), (22, 11)]);

    let reset_result = prepare(&reset, &BTreeMap::new(), &state, parameters, address)?;
    assert_eq!(
        check(&reset_result, &reset_circuit)?,
        reset_result.activity_schedule
    );
    let reset_returns = reset_result.returns_json();
    assert_eq!(reset_returns["keyCount"], json!("0"));
    assert_eq!(reset_returns["isEmpty"], json!(true));
    state = reset_result.after.state;
    assert_vector_set(&state, &[]);

    Ok(())
}
