#![cfg(feature = "zkir-321")]

use base_crypto::fab::AlignedValue;
use noctium_runtime::{
    Db, Plan, canonical_field, check, create_state, field_decimal, field_value, prepare,
    zkir::IrSource,
};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::{
    collections::BTreeMap,
    env,
    path::{Path, PathBuf},
};
use storage::arena::Sp;
use transient_crypto::{curve::Fr, fab::AlignedValueExt};

#[derive(Clone)]
struct Record {
    amount: u64,
    payload: [u8; 32],
    recipient: (String, String),
}

fn artifacts() -> PathBuf {
    env::var_os("NOCTIUM_MIXED_LEDGER_RECORD_DIR")
        .map(PathBuf::from)
        .expect("set fresh outputs in NOCTIUM_MIXED_LEDGER_RECORD_DIR")
}

fn fixture(directory: &Path, entry: &str) -> (Plan, IrSource) {
    let stem = format!("MixedLedgerRecord.{entry}");
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

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_TYPED_RECORD_MAP_DIR"]
fn typed_map_record_insert_lookup_and_remove() -> anyhow::Result<()> {
    let directory = PathBuf::from(env::var("NOCTIUM_TYPED_RECORD_MAP_DIR")?);
    let load = |entry: &str| -> anyhow::Result<(Plan, IrSource)> {
        let stem = format!("TypedRecordMap.{entry}");
        Ok((
            serde_json::from_slice(&std::fs::read(
                directory.join(format!("{stem}.impact.json")),
            )?)?,
            IrSource::load(std::fs::read(directory.join(format!("{stem}.zkir")))?.as_slice())?,
        ))
    };
    let (store, store_relation) = load("storeMemo")?;
    let (read, read_relation) = load("inspectMemo")?;
    let (has, has_relation) = load("hasMemo")?;
    let (remove, remove_relation) = load("removeMemo")?;
    let initial = create_state(&read, &BTreeMap::from([("memos".into(), json!([]))]))?;
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let key = BTreeMap::from([("key".into(), json!("7"))]);
    let mut inputs = key.clone();
    inputs.insert("active".into(), json!(true));
    inputs.insert("amount".into(), json!("513"));

    let inserted = prepare(&store, &inputs, &initial, params, address)?;
    check(&inserted, &store_relation)?;
    for (state, present) in [(&initial, false), (&inserted.after.state, true)] {
        let result = prepare(&has, &key, state, params, address)?;
        check(&result, &has_relation)?;
        assert_eq!(result.returns_json()["presentResult"], json!(present));
    }

    let result = prepare(&read, &key, &inserted.after.state, params, address)?;
    check(&result, &read_relation)?;
    assert_eq!(result.returns_json()["activeResult"], json!(true));
    assert_eq!(result.returns_json()["amountResult"], json!("513"));
    assert_eq!(result.after.state.get_ref(), inserted.after.state.get_ref());

    let removed = prepare(&remove, &key, &inserted.after.state, params, address)?;
    check(&removed, &remove_relation)?;
    assert_eq!(removed.returns_json()["presentAfterRemove"], json!(false));
    assert_eq!(removed.after.state.get_ref(), initial.get_ref());
    assert!(prepare(&read, &key, &removed.after.state, params, address).is_err());

    inputs.insert("amount".into(), json!("65536"));
    assert!(prepare(&store, &inputs, &initial, params, address).is_err());
    Ok(())
}

fn identity() -> (String, String) {
    ("0".into(), "1".into())
}

fn generator() -> (String, String) {
    let point = transient_crypto::curve::EmbeddedGroupAffine::generator();
    (
        field_decimal(point.x().unwrap()),
        field_decimal(point.y().unwrap()),
    )
}

fn point_json((x, y): &(String, String)) -> Json {
    json!({"kind":"jubjubPoint", "x":x, "y":y})
}

fn bytes_json(value: &[u8; 32]) -> Json {
    json!({"kind":"bytes", "values":value.as_slice()})
}

fn inputs(owner: u8, account: u8, value: &Record, enabled: bool) -> BTreeMap<String, Json> {
    BTreeMap::from([
        (
            "owner".into(),
            json!({"kind":"bytes", "values":vec![owner; 32]}),
        ),
        (
            "account".into(),
            json!({"kind":"bytes", "values":vec![account; 32]}),
        ),
        ("amount".into(), json!(value.amount.to_string())),
        ("payload".into(), bytes_json(&value.payload)),
        ("recipient".into(), point_json(&value.recipient)),
        ("enabled".into(), json!(enabled)),
    ])
}

fn record_alignment(value: &Record) -> AlignedValue {
    let fields = [
        field_value(Fr::from(value.amount)),
        value.payload.into(),
        field_value(canonical_field(&value.recipient.0).unwrap()),
        field_value(canonical_field(&value.recipient.1).unwrap()),
    ];
    AlignedValue::concat(fields.iter())
}

fn wrong_record_alignment(value: &Record) -> AlignedValue {
    let payload: AlignedValue = value.payload.into();
    let mut payload_fields = Vec::new();
    payload.value_only_field_repr(&mut payload_fields);
    let mut fields = vec![field_value(Fr::from(value.amount))];
    fields.extend(payload_fields.into_iter().map(field_value));
    fields.extend([
        field_value(canonical_field(&value.recipient.0).unwrap()),
        field_value(canonical_field(&value.recipient.1).unwrap()),
    ]);
    AlignedValue::concat(fields.iter())
}

fn expected_append(value: &Record) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("directAmount".into(), json!(value.amount.to_string())),
        ("directPayload".into(), bytes_json(&value.payload)),
        ("directRecipient".into(), point_json(&value.recipient)),
        ("nestedAmount".into(), json!(value.amount.to_string())),
        ("nestedPayload".into(), bytes_json(&value.payload)),
        ("nestedRecipient".into(), point_json(&value.recipient)),
        ("hasHistory".into(), json!(true)),
        ("headAmount".into(), json!(value.amount.to_string())),
        ("headPayload".into(), bytes_json(&value.payload)),
        ("headRecipient".into(), point_json(&value.recipient)),
    ])
}

fn expected_guarded(value: &Record, present: bool) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("present".into(), json!(present)),
        ("nestedIsPresent".into(), json!(present)),
        ("hasHistory".into(), json!(present)),
        ("directAmount".into(), json!(value.amount.to_string())),
        ("directPayload".into(), bytes_json(&value.payload)),
        ("directRecipient".into(), point_json(&value.recipient)),
        ("nestedAmount".into(), json!(value.amount.to_string())),
        ("nestedPayload".into(), bytes_json(&value.payload)),
        ("nestedRecipient".into(), point_json(&value.recipient)),
        ("headAmount".into(), json!(value.amount.to_string())),
        ("headPayload".into(), bytes_json(&value.payload)),
        ("headRecipient".into(), point_json(&value.recipient)),
    ])
}

fn expected_head(value: &Record, present: bool) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("hasHistory".into(), json!(present)),
        ("headAmount".into(), json!(value.amount.to_string())),
        ("headPayload".into(), bytes_json(&value.payload)),
        ("headRecipient".into(), point_json(&value.recipient)),
    ])
}

fn assert_record_cell(value: &StateValue<Db>, expected: &Record) {
    let StateValue::Cell(cell) = value else {
        panic!("expected mixed record Cell")
    };
    assert_eq!(**cell, record_alignment(expected));
}

fn assert_direct_map_record(state: &ChargedState<Db>, account: u8, expected: &Record) {
    let StateValue::Array(slots) = state.get_ref() else {
        panic!("expected contract state array")
    };
    let StateValue::Map(records) = slots.get(0).unwrap() else {
        panic!("expected records map")
    };
    let key: AlignedValue = [account; 32].into();
    assert_record_cell(&records.get(&key).expect("record exists"), expected);
}

fn assert_nested_map_record(state: &ChargedState<Db>, owner: u8, account: u8, expected: &Record) {
    let StateValue::Array(slots) = state.get_ref() else {
        panic!("expected contract state array")
    };
    let StateValue::Map(owners) = slots.get(1).unwrap() else {
        panic!("expected outer owner map")
    };
    let owner_key: AlignedValue = [owner; 32].into();
    let StateValue::Map(records) = &*owners.get(&owner_key).expect("owner path exists") else {
        panic!("expected nested records map")
    };
    let account_key: AlignedValue = [account; 32].into();
    assert_record_cell(
        &records.get(&account_key).expect("nested record exists"),
        expected,
    );
}

fn assert_list(node: &StateValue<Db>, expected: &[Record]) {
    let StateValue::Array(node) = node else {
        panic!("expected native List array")
    };
    assert_eq!(node.len(), 3);
    let StateValue::Cell(length) = node.get(2).unwrap() else {
        panic!("expected List length cell")
    };
    assert_eq!(**length, AlignedValue::from(expected.len() as u64));
    if let Some((head, tail)) = expected.split_first() {
        assert_record_cell(node.get(0).unwrap(), head);
        assert_list(node.get(1).unwrap(), tail);
    } else {
        assert!(matches!(node.get(0), Some(StateValue::Null)));
        assert!(matches!(node.get(1), Some(StateValue::Null)));
    }
}

fn assert_history(state: &ChargedState<Db>, expected: &[Record]) {
    let StateValue::Array(slots) = state.get_ref() else {
        panic!("expected contract state array")
    };
    assert_list(slots.get(2).unwrap(), expected);
}

fn replace_nested_record(
    state: &ChargedState<Db>,
    owner: u8,
    account: u8,
    value: AlignedValue,
) -> ChargedState<Db> {
    let StateValue::Array(slots) = state.get_ref() else {
        panic!("expected contract state array")
    };
    let StateValue::Map(owners) = slots.get(1).unwrap() else {
        panic!("expected outer owner map")
    };
    let owner_key: AlignedValue = [owner; 32].into();
    let StateValue::Map(records) = &*owners.get(&owner_key).expect("owner path exists") else {
        panic!("expected nested records map")
    };
    let account_key: AlignedValue = [account; 32].into();
    let malformed_records = records.insert(account_key, StateValue::Cell(Sp::new(value)));
    let malformed_owner = StateValue::Map(malformed_records);
    ChargedState::new(StateValue::Array(
        slots
            .insert(
                1,
                StateValue::Map(owners.insert(owner_key, malformed_owner)),
            )
            .unwrap(),
    ))
}

fn assert_typed_schema(plan: &Plan) {
    let direct = &plan.state[0].kind["tree"]["map"][1]["composite"];
    let nested = &plan.state[1].kind["tree"]["map"][1]["map"][1]["composite"];
    let expected_schema = json!({
        "id":"MixedLedgerRecord.Record",
        "fields":[
            {"name":"amount", "type":"Native"},
            {"name":"payload", "type":"Bytes<32>"},
            {"name":"recipient", "type":"JubjubPoint"}
        ]
    });
    assert_eq!(*direct, expected_schema);
    assert_eq!(*nested, expected_schema);
    let components = plan
        .reads
        .iter()
        .find(|read| read.name == "direct")
        .expect("map read schema exists")
        .components
        .iter()
        .map(|component| (component.name.as_str(), component.ty.as_str()))
        .collect::<Vec<_>>();
    assert_eq!(
        components,
        [
            ("direct_amount", "Native"),
            ("direct_payload", "Bytes<32>"),
            ("direct_recipient", "JubjubPoint"),
        ]
    );
    let nested_components = plan
        .reads
        .iter()
        .find(|read| read.name == "nested")
        .expect("nested map read schema exists")
        .components
        .iter()
        .map(|component| (component.name.as_str(), component.ty.as_str()))
        .collect::<Vec<_>>();
    assert_eq!(
        nested_components,
        [
            ("nested_amount", "Native"),
            ("nested_payload", "Bytes<32>"),
            ("nested_recipient", "JubjubPoint"),
        ]
    );
}

#[test]
#[ignore = "requires fresh MixedLedgerRecord outputs in NOCTIUM_MIXED_LEDGER_RECORD_DIR"]
fn mixed_ledger_records_preserve_types_alignment_order_and_guarded_defaults() {
    let directory = artifacts();
    let (append, append_circuit) = fixture(&directory, "append");
    let (guarded, guarded_circuit) = fixture(&directory, "guarded");
    let (pop, pop_circuit) = fixture(&directory, "pop");
    assert_typed_schema(&append);
    let initial = create_state(
        &append,
        &BTreeMap::from([
            ("records".into(), json!([])),
            ("nestedRecords".into(), json!([])),
            ("history".into(), json!([])),
        ]),
    )
    .unwrap();
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let zero = Record {
        amount: 0,
        payload: [0; 32],
        recipient: identity(),
    };
    let inactive = prepare(
        &guarded,
        &inputs(4, 7, &zero, false),
        &initial,
        parameters,
        address,
    )
    .unwrap();
    check(&inactive, &guarded_circuit).unwrap();
    assert_eq!(inactive.returns_json(), expected_guarded(&zero, false));
    assert_eq!(inactive.after.state, initial);

    let first = prepare(
        &append,
        &inputs(4, 7, &zero, true),
        &initial,
        parameters,
        address,
    )
    .unwrap();
    check(&first, &append_circuit).unwrap();
    assert_eq!(first.returns_json(), expected_append(&zero));
    assert_direct_map_record(&first.after.state, 7, &zero);
    assert_nested_map_record(&first.after.state, 4, 7, &zero);
    assert_history(&first.after.state, std::slice::from_ref(&zero));

    let newest = Record {
        amount: 42,
        payload: [42; 32],
        recipient: generator(),
    };
    let second = prepare(
        &append,
        &inputs(4, 7, &newest, true),
        &first.after.state,
        parameters,
        address,
    )
    .unwrap();
    check(&second, &append_circuit).unwrap();
    assert_eq!(second.returns_json(), expected_append(&newest));
    assert_direct_map_record(&second.after.state, 7, &newest);
    assert_nested_map_record(&second.after.state, 4, 7, &newest);
    assert_history(&second.after.state, &[newest.clone(), zero.clone()]);

    let active = prepare(
        &guarded,
        &inputs(4, 7, &newest, true),
        &second.after.state,
        parameters,
        address,
    )
    .unwrap();
    check(&active, &guarded_circuit).unwrap();
    assert_eq!(active.returns_json(), expected_guarded(&newest, true));

    let popped = prepare(
        &pop,
        &inputs(4, 7, &newest, true),
        &second.after.state,
        parameters,
        address,
    )
    .unwrap();
    check(&popped, &pop_circuit).unwrap();
    assert_eq!(popped.returns_json(), expected_head(&zero, true));
    assert_history(&popped.after.state, std::slice::from_ref(&zero));

    let malformed_alignment =
        replace_nested_record(&second.after.state, 4, 7, wrong_record_alignment(&newest));
    let error = prepare(
        &guarded,
        &inputs(4, 7, &newest, true),
        &malformed_alignment,
        parameters,
        address,
    )
    .err()
    .expect("active read must reject a Bytes32 stored with Field alignment");
    assert!(
        format!("{error:#}").contains("record cell alignment mismatch"),
        "expected alignment rejection, got {error:#}"
    );

    let invalid_point = Record {
        amount: 43,
        payload: [43; 32],
        recipient: ("0".into(), "0".into()),
    };
    let malformed_point =
        replace_nested_record(&second.after.state, 4, 7, record_alignment(&invalid_point));
    assert!(
        prepare(
            &guarded,
            &inputs(4, 7, &newest, true),
            &malformed_point,
            parameters,
            address,
        )
        .is_err(),
        "an invalid stored Jubjub point must be rejected"
    );
}
