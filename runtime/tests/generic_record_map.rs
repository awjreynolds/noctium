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
    contract_fixture(directory, "GenericRecordMap", entry)
}

fn contract_fixture(directory: &PathBuf, contract: &str, entry: &str) -> Result<(Plan, IrSource)> {
    let stem = format!("{contract}.{entry}");
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
    assert_eq!(left.state.len(), 4, "fixture has all four root Maps");
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

fn check_record_key_receipt_map() -> Result<()> {
    let directory = artifacts();
    let put = fixture(&directory, "putRecordKeyReceipt")?;
    let lookup = fixture(&directory, "lookupRecordKeyReceipt")?;
    assert_same_map_schema(&put.0, &lookup.0);
    assert!(put.0.returns.is_empty(), "put has no returns");
    assert!(put.0.return_views.is_empty(), "put has no composite returns");
    assert_eq!(lookup.0.return_views.len(), 1, "lookup groups its record return");
    assert_eq!(lookup.0.return_views[0].name, "result");
    assert_eq!(
        lookup.0.return_views[0].schema.pointer("/layout/id").and_then(Json::as_str),
        Some("GenericRecordMap.Receipt"),
    );
    assert_eq!(lookup.0.return_views[0].fields.len(), 2);

    let insert = |state: &ChargedState<Db>, enabled, active, epoch, amount: u64, next_active| {
        let mut inputs = record_key(active, epoch);
        inputs.extend([
            ("enabled".into(), json!(enabled)),
            ("next.amount".into(), json!(amount.to_string())),
            ("next.active".into(), json!(if next_active { "1" } else { "0" })),
        ]);
        let execution = run(&put, &inputs, state)?;
        assert!(execution.returns_json().is_empty(), "put has no returns");
        Ok::<_, anyhow::Error>(execution.after.state)
    };
    let read = |state: &ChargedState<Db>, active, epoch, amount, next_active| {
        let execution = run(&lookup, &record_key(active, epoch), state)?;
        assert_eq!(
            execution.returns_json(),
            BTreeMap::from([("result".into(), receipt(amount, next_active))])
        );
        assert_eq!(execution.after.state, *state);
        Ok::<_, anyhow::Error>(())
    };

    let initial = empty_maps_state(&put.0)?;
    let first = insert(&initial, true, true, 513, 101, true)?;
    read(&first, true, 513, "101", true)?;
    let sibling = insert(&first, true, false, 513, 303, true)?;
    read(&sibling, true, 513, "101", true)?;
    read(&sibling, false, 513, "303", true)?;

    let disabled = insert(&sibling, false, true, 513, 999, false)?;
    assert_eq!(disabled, sibling);
    read(&disabled, true, 513, "101", true)?;
    read(&disabled, false, 513, "303", true)?;

    let overwritten = insert(&disabled, true, true, 513, 202, false)?;
    read(&overwritten, true, 513, "202", false)?;
    read(&overwritten, false, 513, "303", true)?;
    assert!(
        prepare(
            &lookup.0,
            &record_key(true, 514),
            &overwritten,
            &ledger::structure::INITIAL_PARAMETERS,
            ContractAddress::default(),
        )
        .is_err(),
        "lookup of a missing checked record key and value must reject"
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

#[test]
#[ignore = "requires fresh GenericRecordMap artifacts in NOCTIUM_GENERIC_RECORD_MAP_DIR"]
fn generic_record_map_put_record_key_receipt_guards_replace_and_preserves_siblings() -> Result<()> {
    check_record_key_receipt_map()
}

fn check_curve_map(
    contract: &str,
    key: fn(u8) -> BTreeMap<String, Json>,
    values: [Json; 3],
) -> Result<()> {
    let directory = artifacts();
    let put = contract_fixture(&directory, contract, "put")?;
    let lookup = contract_fixture(&directory, contract, "lookup")?;
    let mut state = empty_maps_state(&put.0)?;
    for (index, value) in [1, 2, 1].into_iter().zip(values.iter()) {
        let mut inputs = key(index);
        inputs.insert("enabled".into(), json!(true));
        inputs.insert("next".into(), value.clone());
        state = run(&put, &inputs, &state)?.after.state;
        let read = run(&lookup, &key(index), &state)?;
        assert_eq!(read.returns_json().get("result"), Some(value));
        assert_eq!(read.after.state, state);
    }
    let sibling = run(&lookup, &key(2), &state)?;
    assert_eq!(sibling.returns_json().get("result"), Some(&values[1]));
    assert!(
        prepare(
            &lookup.0,
            &key(3),
            &state,
            &ledger::structure::INITIAL_PARAMETERS,
            ContractAddress::default(),
        )
        .is_err()
    );
    Ok(())
}

#[test]
#[ignore = "requires fresh GenericJubjubScalarMap artifacts in NOCTIUM_GENERIC_RECORD_MAP_DIR"]
fn generic_jubjub_scalar_map_preserves_sibling_values() -> Result<()> {
    check_curve_map(
        "GenericJubjubScalarMap",
        field_key,
        ["5", "17", "23"].map(|value| json!({"kind":"jubjubScalar","value":value})),
    )
}

#[test]
#[ignore = "requires fresh GenericJubjubPointMap artifacts in NOCTIUM_GENERIC_RECORD_MAP_DIR"]
fn generic_jubjub_point_map_preserves_sibling_values() -> Result<()> {
    let point = |x: &str, y: &str| json!({"kind":"jubjubPoint","x":x,"y":y});
    let byte_key = |byte: u8| {
        (0..32)
            .map(|index| (format!("key.{index}"), json!(byte.to_string())))
            .collect()
    };
    check_curve_map(
        "GenericJubjubPointMap",
        byte_key,
        [
            point("0", "1"),
            point(
                "28336281903124990867587793011069573392383982287722241916350956173377953689573",
                "39385640392217313770878525135509063452020585410343666726093009378539878503883",
            ),
            point(
                "28470720865600895264575250048565445848783776096727055802752773414594395577565",
                "22436823168302830732060329876357833227584559018655015131868680653136578255473",
            ),
        ],
    )
}
