#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use noctium_runtime::{Plan, check, construct_state, prepare, zkir::IrSource};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;

const PLAN: &str = include_str!(
    "fixtures/record-key-map-constructor/321/RecordKeyMapConstructor.inspect.impact.json"
);
const CIRCUIT: &[u8] =
    include_bytes!("fixtures/record-key-map-constructor/321/RecordKeyMapConstructor.inspect.zkir");
const VALUE_PLAN: &str = include_str!(
    "fixtures/record-key-map-constructor/321/RecordKeyMapConstructor.readValue.impact.json"
);
const VALUE_CIRCUIT: &[u8] = include_bytes!(
    "fixtures/record-key-map-constructor/321/RecordKeyMapConstructor.readValue.zkir"
);

fn constructor_arguments(enabled: bool, id: &[u8]) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("tag".into(), json!({"kind":"bytes","values":[7]})),
        ("id".into(), json!({"kind":"bytes","values":id})),
        ("amount".into(), json!("513")),
        ("enabled".into(), json!(enabled)),
    ])
}

#[test]
fn guarded_root_record_key_map_constructor_matches_native_state_and_rejects_bad_width() {
    let plan: Plan = serde_json::from_str(PLAN).unwrap();
    let relation = IrSource::load(CIRCUIT).unwrap();
    let value_plan: Plan = serde_json::from_str(VALUE_PLAN).unwrap();
    let value_relation = IrSource::load(VALUE_CIRCUIT).unwrap();
    let id: Vec<u8> = (0..33).map(|index| index * 5 + 2).collect();
    let inspection_inputs = BTreeMap::from([
        ("tag".into(), json!({"kind":"bytes","values":[7]})),
        ("id".into(), json!({"kind":"bytes","values":id})),
    ]);
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = ContractAddress::default();

    for enabled in [false, true] {
        let initial = construct_state(&plan, &constructor_arguments(enabled, &id)).unwrap();
        let inspection = prepare(&plan, &inspection_inputs, &initial, parameters, address).unwrap();
        check(&inspection, &relation).unwrap();
        assert_eq!(
            inspection.returns_json(),
            BTreeMap::from([("present".into(), json!(enabled))])
        );
        assert_eq!(inspection.after.state.get_ref(), initial.get_ref());
        if enabled {
            let value = prepare(
                &value_plan,
                &inspection_inputs,
                &initial,
                parameters,
                address,
            )
            .unwrap();
            check(&value, &value_relation).unwrap();
            assert_eq!(
                value.returns_json(),
                BTreeMap::from([("stored".into(), json!("513"))])
            );
        }
    }

    let wrong_width = vec![1u8; 32];
    assert!(construct_state(&plan, &constructor_arguments(true, &wrong_width)).is_err());
}
