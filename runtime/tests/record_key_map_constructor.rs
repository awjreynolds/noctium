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
const RECORD_PLAN: &str = include_str!(
    "fixtures/record-key-map-constructor/321/RecordKeyMapConstructor.inspectReceipt.impact.json"
);
const RECORD_CIRCUIT: &[u8] = include_bytes!(
    "fixtures/record-key-map-constructor/321/RecordKeyMapConstructor.inspectReceipt.zkir"
);
const RECORD_MEMBER_PLAN: &str = include_str!(
    "fixtures/record-key-map-constructor/321/RecordKeyMapConstructor.receiptMember.impact.json"
);
const RECORD_MEMBER_CIRCUIT: &[u8] = include_bytes!(
    "fixtures/record-key-map-constructor/321/RecordKeyMapConstructor.receiptMember.zkir"
);

fn constructor_arguments(enabled: bool, id: &[u8]) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("tag".into(), json!({"kind":"bytes","values":[7]})),
        ("id".into(), json!({"kind":"bytes","values":id})),
        ("amount".into(), json!("513")),
        ("accepted".into(), json!(true)),
        ("code".into(), json!("700")),
        ("enabled".into(), json!(enabled)),
    ])
}

#[test]
fn guarded_root_record_key_map_constructor_matches_native_state_and_rejects_bad_width() {
    let plan: Plan = serde_json::from_str(PLAN).unwrap();
    let relation = IrSource::load(CIRCUIT).unwrap();
    let value_plan: Plan = serde_json::from_str(VALUE_PLAN).unwrap();
    let value_relation = IrSource::load(VALUE_CIRCUIT).unwrap();
    let record_plan: Plan = serde_json::from_str(RECORD_PLAN).unwrap();
    let record_relation = IrSource::load(RECORD_CIRCUIT).unwrap();
    let record_member_plan: Plan = serde_json::from_str(RECORD_MEMBER_PLAN).unwrap();
    let record_member_relation = IrSource::load(RECORD_MEMBER_CIRCUIT).unwrap();
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

        let record_member = prepare(
            &record_member_plan,
            &inspection_inputs,
            &initial,
            parameters,
            address,
        )
        .unwrap();
        check(&record_member, &record_member_relation).unwrap();
        assert_eq!(
            record_member.returns_json(),
            BTreeMap::from([("present".into(), json!(enabled))])
        );

        let mut neighboring_id = id.clone();
        *neighboring_id.last_mut().unwrap() += 1;
        let neighboring_inputs = BTreeMap::from([
            ("tag".into(), json!({"kind":"bytes","values":[7]})),
            ("id".into(), json!({"kind":"bytes","values":neighboring_id})),
        ]);
        let neighboring = prepare(
            &plan,
            &neighboring_inputs,
            &initial,
            parameters,
            address,
        )
        .unwrap();
        check(&neighboring, &relation).unwrap();
        assert_eq!(
            neighboring.returns_json(),
            BTreeMap::from([("present".into(), json!(false))])
        );
        let neighboring_record = prepare(
            &record_member_plan,
            &neighboring_inputs,
            &initial,
            parameters,
            address,
        )
        .unwrap();
        check(&neighboring_record, &record_member_relation).unwrap();
        assert_eq!(
            neighboring_record.returns_json(),
            BTreeMap::from([("present".into(), json!(false))])
        );

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
            let record = prepare(&record_plan, &inspection_inputs, &initial, parameters, address)
                .unwrap();
            check(&record, &record_relation).unwrap();
            assert_eq!(
                record.returns_json(),
                BTreeMap::from([
                    ("present".into(), json!(true)),
                    ("accepted".into(), json!(true)),
                    ("code".into(), json!("700")),
                ])
            );
        }
    }

    let wrong_width = vec![1u8; 32];
    assert!(construct_state(&plan, &constructor_arguments(true, &wrong_width)).is_err());
    let wrong_value = constructor_arguments(true, &id);
    let mut wrong_value = wrong_value;
    wrong_value.insert("code".into(), json!("65536"));
    assert!(construct_state(&plan, &wrong_value).is_err());

    let mut bad_key_shape: Json = serde_json::from_str(PLAN).unwrap();
    bad_key_shape["constructor"]["actions"][1]["fields"]
        .as_array_mut()
        .unwrap()
        .pop();
    let bad_key_shape: Plan = serde_json::from_value(bad_key_shape).unwrap();
    assert!(construct_state(&bad_key_shape, &constructor_arguments(true, &id)).is_err());

    let mut bad_value_shape: Json = serde_json::from_str(PLAN).unwrap();
    bad_value_shape["constructor"]["actions"][1]["value"]["fields"]
        .as_array_mut()
        .unwrap()
        .pop();
    let bad_value_shape: Plan = serde_json::from_value(bad_value_shape).unwrap();
    assert!(construct_state(&bad_value_shape, &constructor_arguments(true, &id)).is_err());

    let mut bad_value_order: Json = serde_json::from_str(PLAN).unwrap();
    let fields = bad_value_order["constructor"]["actions"][1]["value"]["fields"]
        .as_array_mut()
        .unwrap();
    fields.swap(0, 1);
    let bad_value_order: Plan = serde_json::from_value(bad_value_order).unwrap();
    assert!(construct_state(&bad_value_order, &constructor_arguments(true, &id)).is_err());
}
