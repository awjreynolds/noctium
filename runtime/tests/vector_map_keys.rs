#![cfg(feature = "zkir-321")]

use base_crypto::fab::AlignedValue;
use noctium_runtime::{
    Db, Execution, Plan, check, create_state, field_value, prepare, zkir::IrSource,
};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, path::Path};
use transient_crypto::curve::Fr;

fn vector_map_artifacts() -> std::path::PathBuf {
    std::env::var_os("NOCTIUM_VECTOR_MAP_KEYS_DIR")
        .map(std::path::PathBuf::from)
        .expect("set NOCTIUM_VECTOR_MAP_KEYS_DIR to fresh VectorMapKeys artifacts")
}

fn fixture(directory: &Path, entrypoint: &str) -> (Plan, IrSource) {
    let stem = format!("VectorMapKeys.{entrypoint}");
    let plan = serde_json::from_slice(
        &std::fs::read(directory.join(format!("{stem}.impact.json"))).unwrap(),
    )
    .unwrap();
    let circuit = IrSource::load(
        std::fs::read(directory.join(format!("{stem}.zkir")))
            .unwrap()
            .as_slice(),
    )
    .unwrap();
    (plan, circuit)
}

fn key_inputs() -> BTreeMap<String, Json> {
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

fn assert_map(state: &ChargedState<Db>, plan: &Plan, expected: &[(u64, u64, u64)]) {
    let StateValue::Array(slots) = state.get_ref() else {
        panic!("expected contract state array");
    };
    let slot = plan
        .state
        .iter()
        .position(|declaration| declaration.name == "vectorValues")
        .expect("VectorMapKeys map declaration");
    let StateValue::Map(values) = slots.get(slot).expect("vector map state slot") else {
        panic!("expected Vector-keyed map");
    };
    assert_eq!(values.size(), expected.len());
    for (first, second, value) in expected {
        let StateValue::Cell(cell) = &*values
            .get(&vector_key(*first, *second))
            .expect("ordered vector map key exists")
        else {
            panic!("expected native Cell value");
        };
        assert_eq!(**cell, field_value(Fr::from(*value)));
    }
}

fn run(
    plan: &Plan,
    circuit: &IrSource,
    inputs: &BTreeMap<String, Json>,
    state: &ChargedState<Db>,
) -> anyhow::Result<Execution> {
    let execution = prepare(
        plan,
        inputs,
        state,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )?;
    assert_eq!(check(&execution, circuit)?, execution.activity_schedule);
    Ok(execution)
}

#[test]
#[ignore = "requires fresh VectorMapKeys artifacts in NOCTIUM_VECTOR_MAP_KEYS_DIR"]
fn vector_map_keys_preserve_order_overwrite_and_missing_lookup() -> anyhow::Result<()> {
    let directory = vector_map_artifacts();
    let (update_plan, update_circuit) = fixture(&directory, "update");
    let (lookup_plan, lookup_circuit) = fixture(&directory, "lookup");
    let (member_plan, member_circuit) = fixture(&directory, "member");
    let (size_plan, size_circuit) = fixture(&directory, "size");
    let (remove_plan, remove_circuit) = fixture(&directory, "remove");

    let mut state = create_state(
        &update_plan,
        &BTreeMap::from([("vectorValues".into(), json!([]))]),
    )?;
    assert_map(&state, &update_plan, &[]);

    let keys = key_inputs();
    let updated = run(&update_plan, &update_circuit, &keys, &state)?;
    let update_returns = updated.returns_json();
    assert_eq!(update_returns["memberA"], json!(true));
    assert_eq!(update_returns["memberB"], json!(true));
    assert_eq!(update_returns["size"], json!("2"));
    state = updated.after.state;
    assert_map(&state, &update_plan, &[(11, 22, 202), (11, 23, 303)]);

    let looked_up = run(&lookup_plan, &lookup_circuit, &keys, &state)?;
    let lookup_returns = looked_up.returns_json();
    assert_eq!(lookup_returns["lookupA"], json!("202"));
    assert_eq!(lookup_returns["lookupB"], json!("303"));
    assert_eq!(lookup_returns["lookupMissing"], json!("0"));
    assert_eq!(looked_up.after.state, state);

    let membership = run(&member_plan, &member_circuit, &keys, &state)?;
    let member_returns = membership.returns_json();
    assert_eq!(member_returns["memberA"], json!(true));
    assert_eq!(member_returns["memberB"], json!(true));
    assert_eq!(member_returns["memberMissing"], json!(false));
    assert_eq!(membership.after.state, state);

    let sized = run(&size_plan, &size_circuit, &BTreeMap::new(), &state)?;
    assert_eq!(sized.returns_json()["size"], json!("2"));
    assert_eq!(sized.after.state, state);

    let removed = run(&remove_plan, &remove_circuit, &keys, &state)?;
    let remove_returns = removed.returns_json();
    assert_eq!(remove_returns["memberA"], json!(false));
    assert_eq!(remove_returns["memberB"], json!(true));
    assert_eq!(remove_returns["lookupA"], json!("0"));
    assert_eq!(remove_returns["size"], json!("1"));
    assert_map(&removed.after.state, &remove_plan, &[(11, 23, 303)]);

    Ok(())
}
