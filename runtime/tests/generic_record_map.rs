#![cfg(feature = "zkir-321")]

use anyhow::Result;
use coin_structure::contract::ContractAddress;
use noctium_runtime::{Db, Execution, Plan, check, create_state, prepare, zkir::IrSource};
use onchain_runtime::state::ChargedState;
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, env, fs::File, path::PathBuf};

fn artifacts() -> PathBuf {
    env::var_os("NOCTIUM_GENERIC_RECORD_MAP_DIR")
        .map(PathBuf::from)
        .expect("NOCTIUM_GENERIC_RECORD_MAP_DIR")
}

fn fixture(directory: &PathBuf, entry: &str) -> Result<(Plan, IrSource)> {
    let stem = format!("GenericRecordMap.{entry}");
    let plan = serde_json::from_reader(File::open(
        directory.join(format!("{stem}.impact.json")),
    )?)?;
    let relation = IrSource::load(File::open(directory.join(format!("{stem}.zkir")))?)?;
    Ok((plan, relation))
}

fn run(
    operation: &(Plan, IrSource),
    inputs: &BTreeMap<String, Json>,
    state: &ChargedState<Db>,
) -> Result<Execution> {
    let execution = prepare(
        &operation.0,
        inputs,
        state,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    assert_eq!(
        check(&execution, &operation.1)?,
        execution.activity_schedule
    );
    Ok(execution)
}

fn put_inputs(enabled: bool, key: u64, amount: u64, active: bool) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("enabled".into(), json!(enabled)),
        ("key".into(), json!(key.to_string())),
        ("next.amount".into(), json!(amount.to_string())),
        (
            "next.active".into(),
            json!(if active { "1" } else { "0" }),
        ),
    ])
}

fn lookup_inputs(key: u64) -> BTreeMap<String, Json> {
    BTreeMap::from([("key".into(), json!(key.to_string()))])
}

fn receipt(amount: &str, active: bool) -> Json {
    json!({
        "kind": "struct",
        "id": "GenericRecordMap.Receipt",
        "fields": [
            {"name": "amount", "value": {"kind": "native", "value": amount}},
            {"name": "active", "value": {"kind": "bool", "value": active}},
        ]
    })
}

fn assert_lookup(
    lookup: &(Plan, IrSource),
    state: &ChargedState<Db>,
    key: u64,
    expected_amount: &str,
    expected_active: bool,
) -> Result<()> {
    let execution = run(lookup, &lookup_inputs(key), state)?;
    assert_eq!(
        execution.returns_json(),
        BTreeMap::from([("result".into(), receipt(expected_amount, expected_active))])
    );
    assert_eq!(execution.after.state, *state);
    Ok(())
}

#[test]
#[ignore = "requires fresh GenericRecordMap artifacts in NOCTIUM_GENERIC_RECORD_MAP_DIR"]
fn generic_record_map_put_updates_one_checked_record() -> Result<()> {
    let directory = artifacts();
    let put = fixture(&directory, "put")?;
    let lookup = fixture(&directory, "lookup")?;
    assert_eq!(put.0.state.len(), 1, "fixture has one root Map");
    assert_eq!(lookup.0.state.len(), 1, "lookup has the same root Map");
    assert_eq!(lookup.0.state[0].name, put.0.state[0].name);
    assert!(
        put.0.state[0].kind.pointer("/tree/map").is_some(),
        "state is a recursive Map with a record value"
    );
    assert!(put.0.returns.is_empty(), "put has no returns");
    assert!(put.0.return_views.is_empty(), "put has no composite returns");

    let initial = create_state(
        &put.0,
        &BTreeMap::from([(put.0.state[0].name.clone(), json!([]))]),
    )?;

    let inserted_a = run(&put, &put_inputs(true, 11, 101, true), &initial)?;
    assert!(inserted_a.returns_json().is_empty(), "put has no returns");
    assert_lookup(&lookup, &inserted_a.after.state, 11, "101", true)?;

    let inserted_b = run(&put, &put_inputs(true, 12, 303, true), &inserted_a.after.state)?;
    assert!(inserted_b.returns_json().is_empty(), "put has no returns");
    assert_lookup(&lookup, &inserted_b.after.state, 11, "101", true)?;
    assert_lookup(&lookup, &inserted_b.after.state, 12, "303", true)?;

    let disabled_a = run(
        &put,
        &put_inputs(false, 11, 999, false),
        &inserted_b.after.state,
    )?;
    assert_eq!(disabled_a.after.state, inserted_b.after.state);
    assert!(disabled_a.returns_json().is_empty(), "put has no returns");
    assert_lookup(&lookup, &disabled_a.after.state, 11, "101", true)?;
    assert_lookup(&lookup, &disabled_a.after.state, 12, "303", true)?;

    let overwritten_a = run(
        &put,
        &put_inputs(true, 11, 202, false),
        &disabled_a.after.state,
    )?;
    assert!(overwritten_a.returns_json().is_empty(), "put has no returns");
    assert_lookup(&lookup, &overwritten_a.after.state, 11, "202", false)?;
    assert_lookup(&lookup, &overwritten_a.after.state, 12, "303", true)?;

    assert!(
        prepare(
            &lookup.0,
            &lookup_inputs(13),
            &overwritten_a.after.state,
            &ledger::structure::INITIAL_PARAMETERS,
            ContractAddress::default(),
        )
        .is_err(),
        "lookup of a missing key must reject"
    );
    Ok(())
}
