#![cfg(feature = "zkir-321")]

use anyhow::Result;
use noctium_runtime::{Db, Plan, check, create_state, prepare, zkir::IrSource};
use onchain_runtime::state::ChargedState;
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;

fn load(name: &str) -> Result<(Plan, IrSource)> {
    let plan: Plan = serde_json::from_str(match name {
        "initializeOwner" => include_str!(
            "fixtures/nested-fixed-byte-record-map/321/NestedFixedByteRecordMap.initializeOwner.impact.json"
        ),
        "exercise" => include_str!(
            "fixtures/nested-fixed-byte-record-map/321/NestedFixedByteRecordMap.exercise.impact.json"
        ),
        "inspect" => include_str!(
            "fixtures/nested-fixed-byte-record-map/321/NestedFixedByteRecordMap.inspect.impact.json"
        ),
        _ => anyhow::bail!("unknown fixture entrypoint {name}"),
    })?;
    let circuit_bytes: &[u8] = match name {
        "initializeOwner" => include_bytes!(
            "fixtures/nested-fixed-byte-record-map/321/NestedFixedByteRecordMap.initializeOwner.zkir"
        ),
        "exercise" => include_bytes!(
            "fixtures/nested-fixed-byte-record-map/321/NestedFixedByteRecordMap.exercise.zkir"
        ),
        "inspect" => include_bytes!(
            "fixtures/nested-fixed-byte-record-map/321/NestedFixedByteRecordMap.inspect.zkir"
        ),
        _ => anyhow::bail!("unknown fixture entrypoint {name}"),
    };
    Ok((plan, IrSource::load(circuit_bytes)?))
}

fn bytes_value(value: &[u8]) -> Json {
    json!({"kind":"bytes", "values":value})
}

fn owner(byte: u8) -> Json {
    bytes_value(&[byte; 32])
}

fn id(last: u8) -> Vec<u8> {
    let mut value = vec![3; 33];
    value[32] = last;
    value
}

fn initialize_inputs(owner_byte: u8) -> BTreeMap<String, Json> {
    BTreeMap::from([("owner".into(), owner(owner_byte))])
}

fn exercise_inputs(owner_byte: u8, second_owner: bool) -> BTreeMap<String, Json> {
    let (first_scalar, late_scalar, first_accepted, late_accepted) = if second_owner {
        ("707", "909", false, true)
    } else {
        ("101", "303", true, false)
    };
    BTreeMap::from([
        ("owner".into(), owner(owner_byte)),
        ("tag".into(), bytes_value(&[7])),
        ("firstId".into(), bytes_value(&id(3))),
        ("lateId".into(), bytes_value(&id(4))),
        ("firstScalar".into(), json!(first_scalar)),
        ("lateScalar".into(), json!(late_scalar)),
        ("firstAccepted".into(), json!(first_accepted)),
        ("firstCode".into(), json!(first_scalar)),
        ("lateAccepted".into(), json!(late_accepted)),
        ("lateCode".into(), json!(late_scalar)),
    ])
}

fn inspect_inputs(owner_byte: u8) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("owner".into(), owner(owner_byte)),
        ("tag".into(), bytes_value(&[7])),
        ("firstId".into(), bytes_value(&id(3))),
        ("lateId".into(), bytes_value(&id(4))),
    ])
}

fn outputs(step: &noctium_runtime::Execution) -> Json {
    Json::Object(step.returns_json().into_iter().collect())
}

fn run<'a>(
    plan: &'a Plan,
    circuit: &IrSource,
    inputs: &BTreeMap<String, Json>,
    state: &ChargedState<Db>,
) -> Result<noctium_runtime::Execution> {
    let step = prepare(
        plan,
        inputs,
        state,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )?;
    assert_eq!(check(&step, circuit)?, step.activity_schedule);
    Ok(step)
}

#[test]
fn nested_fixed_byte_record_maps_match_compact_and_isolate_parent_buckets() -> Result<()> {
    let compact: Json = serde_json::from_str(include_str!(
        "fixtures/nested-fixed-byte-record-map/compact-0.36.1.json"
    ))?;
    assert_eq!(compact["compact"], "0.36.1 (7fa3a117c 2026-11-11)");
    assert_eq!(compact["runtime"], "0.21.0");

    let (initialize_plan, initialize_circuit) = load("initializeOwner")?;
    let (exercise_plan, exercise_circuit) = load("exercise")?;
    let (inspect_plan, inspect_circuit) = load("inspect")?;
    let config = BTreeMap::from([
        ("scalars".into(), json!([])),
        ("records".into(), json!([])),
    ]);
    let mut state = create_state(&exercise_plan, &config)?;

    for owner_byte in [1, 2] {
        let step = run(
            &initialize_plan,
            &initialize_circuit,
            &initialize_inputs(owner_byte),
            &state,
        )?;
        state = step.after.state;
    }

    let first_exercise = exercise_inputs(1, false);
    let first = run(&exercise_plan, &exercise_circuit, &first_exercise, &state)?;
    assert_eq!(outputs(&first), compact["owners"]["first"]["exercise"]);
    state = first.after.state;

    let second_exercise = exercise_inputs(2, true);
    let second = run(&exercise_plan, &exercise_circuit, &second_exercise, &state)?;
    assert_eq!(outputs(&second), compact["owners"]["second"]["exercise"]);
    state = second.after.state;

    for (owner_byte, parent) in [(1, "first"), (2, "second")] {
        let inspected = run(
            &inspect_plan,
            &inspect_circuit,
            &inspect_inputs(owner_byte),
            &state,
        )?;
        assert_eq!(outputs(&inspected), compact["owners"][parent]["inspect"]);
    }

    let mut malformed = exercise_inputs(1, false);
    malformed.insert("firstId".into(), bytes_value(&id(3)[..32]));
    assert!(prepare(
        &exercise_plan,
        &malformed,
        &state,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .is_err());

    let mut fixed_byte_value: Json = serde_json::from_str(include_str!(
        "fixtures/nested-fixed-byte-record-map/321/NestedFixedByteRecordMap.exercise.impact.json"
    ))?;
    fixed_byte_value["state"][1]["kind"]["tree"]["map"][1]["map"][1]["composite"]["fields"][0]
        ["type"] = json!("Bytes<1>");
    let fixed_byte_value: Plan = serde_json::from_value(fixed_byte_value)?;
    assert!(create_state(&fixed_byte_value, &config).is_ok());

    let mut excessive_depth: Json = serde_json::from_str(include_str!(
        "fixtures/nested-fixed-byte-record-map/321/NestedFixedByteRecordMap.exercise.impact.json"
    ))?;
    let record_map = excessive_depth["state"][1]["kind"]["tree"]["map"][1].clone();
    excessive_depth["state"][1]["kind"]["tree"]["map"][1] =
        json!({"map":["Bytes<32>", record_map]});
    let excessive_depth: Plan = serde_json::from_value(excessive_depth)?;
    assert!(create_state(&excessive_depth, &config).is_err());
    Ok(())
}
