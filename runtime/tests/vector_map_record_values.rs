#![cfg(feature = "zkir-321")]

use base_crypto::fab::AlignedValue;
use noctium_runtime::{Db, Plan, check, create_state, field_value, prepare, zkir::IrSource};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
};
use transient_crypto::curve::Fr;

fn artifacts() -> PathBuf {
    std::env::var_os("NOCTIUM_VECTOR_MAP_RECORD_VALUES_DIR")
        .map(PathBuf::from)
        .expect("set NOCTIUM_VECTOR_MAP_RECORD_VALUES_DIR to fresh compiler outputs")
}

fn fixture(directory: &Path, entry: &str) -> (Plan, IrSource) {
    let stem = format!("VectorMapRecordValues.{entry}");
    let plan =
        serde_json::from_slice(&fs::read(directory.join(format!("{stem}.impact.json"))).unwrap())
            .unwrap();
    let circuit =
        IrSource::load(fs::File::open(directory.join(format!("{stem}.zkir"))).unwrap()).unwrap();
    (plan, circuit)
}

fn inputs() -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("first".into(), json!("11")),
        ("second".into(), json!("22")),
        ("third".into(), json!("23")),
    ])
}

fn run(
    plan: &Plan,
    circuit: &IrSource,
    inputs: &BTreeMap<String, Json>,
    state: &ChargedState<Db>,
) -> noctium_runtime::Execution {
    let execution = prepare(
        plan,
        inputs,
        state,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .unwrap();
    check(&execution, circuit).unwrap();
    execution
}

fn key(first: u64, second: u64) -> AlignedValue {
    let fields = [field_value(Fr::from(first)), field_value(Fr::from(second))];
    AlignedValue::concat(fields.iter())
}

fn assert_receipts(state: &ChargedState<Db>, plan: &Plan, expected: &[([u64; 2], u64, bool)]) {
    let StateValue::Array(slots) = state.get_ref() else {
        panic!("expected state slots")
    };
    let slot = plan
        .state
        .iter()
        .position(|declaration| declaration.name == "receipts")
        .expect("receipts state declaration");
    let StateValue::Map(receipts) = slots.get(slot).expect("receipts state slot") else {
        panic!("expected receipts Map")
    };
    assert_eq!(receipts.size(), expected.len());
    for ([first, second], amount, active) in expected {
        let record = receipts
            .get(&key(*first, *second))
            .expect("receipt at exact Vector key");
        let StateValue::Cell(value) = &*record else {
            panic!("expected Receipt in one native cell")
        };
        let fields = [
            field_value(Fr::from(*amount)),
            field_value(Fr::from(if *active { 1u64 } else { 0u64 })),
        ];
        assert_eq!(**value, AlignedValue::concat(fields.iter()));
    }
}

#[test]
#[ignore = "requires fresh VectorMapRecordValues artifacts in NOCTIUM_VECTOR_MAP_RECORD_VALUES_DIR"]
fn vector_keys_select_and_remove_record_values_without_touching_neighbors() {
    let directory = artifacts();
    let (update, update_circuit) = fixture(&directory, "update");
    let (lookup, lookup_circuit) = fixture(&directory, "lookup");
    let (size, size_circuit) = fixture(&directory, "size");
    let (remove, remove_circuit) = fixture(&directory, "remove");
    let empty = create_state(&update, &BTreeMap::from([("receipts".into(), json!([]))])).unwrap();
    let inputs = inputs();

    let inserted = run(&update, &update_circuit, &inputs, &empty);
    assert_eq!(
        inserted.returns_json(),
        BTreeMap::from([
            ("memberA".into(), json!(true)),
            ("memberB".into(), json!(true)),
            ("size".into(), json!("2")),
        ])
    );
    assert_receipts(
        &inserted.after.state,
        &update,
        &[([11, 22], 202, false), ([11, 23], 303, true)],
    );

    let viewed = run(&lookup, &lookup_circuit, &inputs, &inserted.after.state);
    assert_eq!(
        viewed.returns_json(),
        BTreeMap::from([
            ("amountA".into(), json!("202")),
            ("activeA".into(), json!(false)),
            ("amountB".into(), json!("303")),
            ("activeB".into(), json!(true)),
        ])
    );
    assert_eq!(viewed.after.state, inserted.after.state);

    let counted = run(
        &size,
        &size_circuit,
        &BTreeMap::new(),
        &inserted.after.state,
    );
    assert_eq!(
        counted.returns_json(),
        BTreeMap::from([("size".into(), json!("2"))])
    );
    assert_eq!(counted.after.state, inserted.after.state);

    let removed = run(&remove, &remove_circuit, &inputs, &inserted.after.state);
    assert_eq!(
        removed.returns_json(),
        BTreeMap::from([
            ("memberA".into(), json!(false)),
            ("memberB".into(), json!(true)),
            ("amountB".into(), json!("303")),
            ("activeB".into(), json!(true)),
            ("size".into(), json!("1")),
        ])
    );
    assert_receipts(&removed.after.state, &remove, &[([11, 23], 303, true)]);

    let counted = run(&size, &size_circuit, &BTreeMap::new(), &removed.after.state);
    assert_eq!(
        counted.returns_json(),
        BTreeMap::from([("size".into(), json!("1"))])
    );
    assert_eq!(counted.after.state, removed.after.state);
}
