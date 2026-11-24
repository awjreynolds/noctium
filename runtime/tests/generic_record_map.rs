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

fn field_key(suffix: u8) -> BTreeMap<String, Json> {
    BTreeMap::from([("key".into(), json!(suffix.to_string()))])
}

fn byte_key(suffix: u8) -> BTreeMap<String, Json> {
    (1..=31)
        .chain([suffix])
        .enumerate()
        .map(|(index, byte)| (format!("key.{index}"), json!(byte.to_string())))
        .collect()
}

fn record_key(active: bool, epoch: u16) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("key.active".into(), json!(u8::from(active).to_string())),
        ("key.epoch".into(), json!(epoch.to_string())),
    ])
}

fn empty_maps_state(plan: &Plan) -> Result<ChargedState<Db>> {
    let config = plan
        .state
        .iter()
        .map(|state| (state.name.clone(), json!([])))
        .collect();
    Ok(create_state(plan, &config)?)
}

fn assert_same_map_schema(left: &Plan, right: &Plan) {
    assert_eq!(left.state.len(), 3, "fixture has all three root Maps");
    assert_eq!(right.state.len(), left.state.len());
    for (left_state, right_state) in left.state.iter().zip(&right.state) {
        assert_eq!(left_state.name, right_state.name);
        assert!(left_state.kind.pointer("/tree/map").is_some());
        assert!(right_state.kind.pointer("/tree/map").is_some());
    }
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

fn check_map(
    put_entry: &str,
    lookup_entry: &str,
    key: fn(u8) -> BTreeMap<String, Json>,
) -> Result<()> {
    let directory = artifacts();
    let put = fixture(&directory, put_entry)?;
    let lookup = fixture(&directory, lookup_entry)?;
    assert_same_map_schema(&put.0, &lookup.0);
    assert!(put.0.returns.is_empty(), "put has no returns");
    assert!(put.0.return_views.is_empty(), "put has no composite returns");

    let insert = |state: &ChargedState<Db>, enabled, suffix, amount: u64, active| {
        let mut inputs = key(suffix);
        inputs.extend([
            ("enabled".into(), json!(enabled)),
            ("next.amount".into(), json!(amount.to_string())),
            ("next.active".into(), json!(if active { "1" } else { "0" })),
        ]);
        let execution = run(&put, &inputs, state)?;
        assert!(execution.returns_json().is_empty(), "put has no returns");
        Ok::<_, anyhow::Error>(execution.after.state)
    };
    let read = |state: &ChargedState<Db>, suffix, amount, active| {
        let execution = run(&lookup, &key(suffix), state)?;
        assert_eq!(
            execution.returns_json(),
            BTreeMap::from([("result".into(), receipt(amount, active))])
        );
        assert_eq!(execution.after.state, *state);
        Ok::<_, anyhow::Error>(())
    };

    let initial = empty_maps_state(&put.0)?;
    let inserted_a = insert(&initial, true, 11, 101, true)?;
    read(&inserted_a, 11, "101", true)?;

    let inserted_b = insert(&inserted_a, true, 12, 303, true)?;
    read(&inserted_b, 11, "101", true)?;
    read(&inserted_b, 12, "303", true)?;

    let disabled = insert(&inserted_b, false, 11, 999, false)?;
    assert_eq!(disabled, inserted_b);
    read(&disabled, 11, "101", true)?;
    read(&disabled, 12, "303", true)?;

    let overwritten = insert(&disabled, true, 11, 202, false)?;
    read(&overwritten, 11, "202", false)?;
    read(&overwritten, 12, "303", true)?;
    assert!(
        prepare(
            &lookup.0,
            &key(13),
            &overwritten,
            &ledger::structure::INITIAL_PARAMETERS,
            ContractAddress::default(),
        )
        .is_err(),
        "lookup of a missing key must reject"
    );
    Ok(())
}

fn check_record_key_map() -> Result<()> {
    let directory = artifacts();
    let put = fixture(&directory, "putRecordKey")?;
    let lookup = fixture(&directory, "lookupRecordKey")?;
    assert_same_map_schema(&put.0, &lookup.0);
    assert!(put.0.returns.is_empty(), "put has no returns");

    let insert = |state: &ChargedState<Db>, enabled, active, epoch, next: u16| {
        let mut inputs = record_key(active, epoch);
        inputs.insert("enabled".into(), json!(enabled));
        inputs.insert("next".into(), json!(next.to_string()));
        let execution = run(&put, &inputs, state)?;
        assert!(execution.returns_json().is_empty(), "put has no returns");
        Ok::<_, anyhow::Error>(execution.after.state)
    };
    let read = |state: &ChargedState<Db>, active, epoch, expected: u16| {
        let execution = run(&lookup, &record_key(active, epoch), state)?;
        assert_eq!(execution.returns_json(), BTreeMap::from([
            ("result".into(), json!(expected.to_string())),
        ]));
        assert_eq!(execution.after.state, *state);
        Ok::<_, anyhow::Error>(())
    };

    let initial = empty_maps_state(&put.0)?;
    let first = insert(&initial, true, true, 513, 101)?;
    read(&first, true, 513, 101)?;
    let second = insert(&first, true, false, 513, 303)?;
    read(&second, true, 513, 101)?;
    read(&second, false, 513, 303)?;

    let disabled = insert(&second, false, true, 513, 999)?;
    assert_eq!(disabled, second);
    read(&disabled, true, 513, 101)?;
    read(&disabled, false, 513, 303)?;

    let overwritten = insert(&disabled, true, true, 513, 202)?;
    read(&overwritten, true, 513, 202)?;
    read(&overwritten, false, 513, 303)?;
    assert!(
        prepare(
            &lookup.0,
            &record_key(true, 514),
            &overwritten,
            &ledger::structure::INITIAL_PARAMETERS,
            ContractAddress::default(),
        )
        .is_err(),
        "lookup of a missing checked record key must reject"
    );
    Ok(())
}

#[test]
#[ignore = "requires fresh GenericRecordMap artifacts in NOCTIUM_GENERIC_RECORD_MAP_DIR"]
fn generic_record_map_put_updates_one_checked_record() -> Result<()> {
    check_map("put", "lookup", field_key)
}

#[test]
#[ignore = "requires fresh GenericRecordMap artifacts in NOCTIUM_GENERIC_RECORD_MAP_DIR"]
fn generic_record_map_put_bytes_updates_one_checked_record() -> Result<()> {
    check_map("putBytes", "lookupBytes", byte_key)
}

#[test]
#[ignore = "requires fresh GenericRecordMap artifacts in NOCTIUM_GENERIC_RECORD_MAP_DIR"]
fn generic_record_map_put_record_key_updates_one_uint16() -> Result<()> {
    check_record_key_map()
}
