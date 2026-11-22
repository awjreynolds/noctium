#![cfg(feature = "zkir-321")]

use base_crypto::fab::AlignedValue;
use noctium_runtime::{Db, Plan, check, create_state, field_decimal, prepare, zkir::IrSource};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use transient_crypto::{curve::Fr, fab::AlignedValueExt};

const PLAN: &str = include_str!("fixtures/structured-maps/321/StructuredMaps.update.impact.json");
const CIRCUIT: &[u8] = include_bytes!("fixtures/structured-maps/321/StructuredMaps.update.zkir");

fn inputs(enabled: bool, account: &[u8; 32], amount: u64) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("enabled".into(), json!(enabled)),
        (
            "account".into(),
            json!({"kind":"bytes", "values":account.as_slice()}),
        ),
        ("amount".into(), json!(amount.to_string())),
    ])
}

fn assert_balance(
    state: &ChargedState<Db>,
    account: &[u8; 32],
    expected: Option<&str>,
    expected_size: usize,
) {
    let StateValue::Array(array) = state.get_ref() else {
        panic!("expected state array");
    };
    let StateValue::Map(map) = &*array.get(0).expect("balances map exists") else {
        panic!("expected balances map");
    };
    assert_eq!(map.size(), expected_size);
    let key: AlignedValue = (*account).into();
    match (map.get(&key), expected) {
        (None, None) => {}
        (Some(value), Some(expected)) => {
            let StateValue::Cell(cell) = &*value else {
                panic!("expected balance cell");
            };
            let mut fields = Vec::new();
            cell.value_only_field_repr(&mut fields);
            assert_eq!(fields.len(), 1);
            assert_eq!(field_decimal(fields[0]), expected);
        }
        _ => panic!("map state differs from the expected entry"),
    }
}

fn assert_result(execution: &noctium_runtime::Execution, expected: u64) {
    assert_eq!(
        execution.returns_json(),
        BTreeMap::from([("result".into(), json!(expected.to_string()))])
    );
}

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_RECORD_MAP_KEYS_DIR"]
fn record_map_keys_preserve_strict_lookup_and_distinct_members() -> anyhow::Result<()> {
    let directory = std::path::PathBuf::from(std::env::var("NOCTIUM_RECORD_MAP_KEYS_DIR")?);
    let load = |entry: &str| -> anyhow::Result<(Plan, IrSource)> {
        let stem = format!("RecordMapKeys.{entry}");
        Ok((
            serde_json::from_slice(&std::fs::read(
                directory.join(format!("{stem}.impact.json")),
            )?)?,
            IrSource::load(std::fs::File::open(directory.join(format!("{stem}.zkir")))?)?,
        ))
    };
    let (update, update_relation) = load("update")?;
    let (lookup, lookup_relation) = load("lookup")?;
    let (remove, remove_relation) = load("removeMemo")?;
    let mut state = create_state(&update, &BTreeMap::from([("memos".into(), json!([]))]))?;
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let key = |active, amount: u32| {
        BTreeMap::from([
            ("active".into(), json!(active)),
            ("amount".into(), json!(amount.to_string())),
        ])
    };
    let update_args = |active, amount, value: u16| {
        let mut arguments = key(active, amount);
        arguments.insert("value".into(), json!(value.to_string()));
        arguments
    };
    let read = |active, amount, state: &ChargedState<Db>| -> anyhow::Result<Json> {
        let execution = prepare(&lookup, &key(active, amount), state, parameters, address)?;
        assert_eq!(
            check(&execution, &lookup_relation)?,
            execution.activity_schedule
        );
        Ok(execution.returns_json()["storedValue"].clone())
    };

    assert!(read(true, 513, &state).is_err());
    let records = [(true, 513, 11u16), (false, 513, 22u16), (true, 514, 33u16)];
    for (active, amount, value) in records {
        let arguments = update_args(active, amount, value);
        let execution = prepare(&update, &arguments, &state, parameters, address)?;
        assert_eq!(
            check(&execution, &update_relation)?,
            execution.activity_schedule
        );
        assert_eq!(execution.returns_json()["presentBefore"], json!(false));
        assert_eq!(execution.returns_json()["presentAfter"], json!(true));
        state = execution.after.state;
    }
    for (active, amount, value) in records {
        assert_eq!(read(active, amount, &state)?, json!(value.to_string()));
    }

    let removed = prepare(&remove, &key(true, 513), &state, parameters, address)?;
    assert_eq!(
        check(&removed, &remove_relation)?,
        removed.activity_schedule
    );
    assert_eq!(removed.returns_json()["presentBefore"], json!(true));
    assert_eq!(removed.returns_json()["presentAfter"], json!(false));
    state = removed.after.state;
    assert!(read(true, 513, &state).is_err());
    assert_eq!(read(false, 513, &state)?, json!("22"));
    assert_eq!(read(true, 514, &state)?, json!("33"));
    assert!(read(true, 65536, &state).is_err());
    Ok(())
}

#[test]
fn structured_helper_binds_guarded_bytes32_map_effects_and_returns() {
    let plan: Plan = serde_json::from_str(PLAN).expect("source map plan parses");
    let circuit = IrSource::load(CIRCUIT).expect("source ZKIR parses");
    let initial = create_state(&plan, &BTreeMap::from([("balances".into(), json!([]))]))
        .expect("empty balances map creates");
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let account = [0x42; 32];

    let disabled_empty = prepare(
        &plan,
        &inputs(false, &account, 8),
        &initial,
        params,
        address,
    )
    .expect("disabled call skips narrowing and map writes");
    check(&disabled_empty, &circuit).expect("disabled call relation checks");
    assert_eq!(disabled_empty.after.state, initial);
    assert_balance(&disabled_empty.after.state, &account, None, 0);
    assert_result(&disabled_empty, 0);

    let first = prepare(&plan, &inputs(true, &account, 7), &initial, params, address)
        .expect("active call inserts a missing balance");
    check(&first, &circuit).expect("insert call relation checks");
    assert_balance(&first.after.state, &account, Some("7"), 1);
    assert_result(&first, 7);

    let second = prepare(
        &plan,
        &inputs(true, &account, 2),
        &first.after.state,
        params,
        address,
    )
    .expect("active call reads and increments an existing balance");
    check(&second, &circuit).expect("increment call relation checks");
    assert_balance(&second.after.state, &account, Some("9"), 1);
    assert_result(&second, 9);

    let disabled_existing = prepare(
        &plan,
        &inputs(false, &account, 8),
        &second.after.state,
        params,
        address,
    )
    .expect("disabled call preserves an existing balance");
    check(&disabled_existing, &circuit).expect("disabled existing call relation checks");
    assert_eq!(disabled_existing.after.state, second.after.state);
    assert_balance(&disabled_existing.after.state, &account, Some("9"), 1);
    assert_result(&disabled_existing, 9);

    if let Ok(invalid_active) = prepare(
        &plan,
        &inputs(true, &account, 8),
        &second.after.state,
        params,
        address,
    ) {
        assert!(check(&invalid_active, &circuit).is_err());
    }

    let mut altered_guard = prepare(
        &plan,
        &inputs(false, &account, 8),
        &second.after.state,
        params,
        address,
    )
    .expect("disabled call prepares for guard tampering");
    assert_eq!(altered_guard.preimage.private_transcript.len(), 1);
    altered_guard.preimage.private_transcript[0] = Fr::from(1u64);
    assert!(check(&altered_guard, &circuit).is_err());
}
