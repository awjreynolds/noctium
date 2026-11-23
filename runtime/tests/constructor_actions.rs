use noctium_runtime::{
    Db, Expr, Plan, construct_state,
    constructor::{ConstructorAction, InitialValue, Initializer, MapInsert},
    field_value,
};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use transient_crypto::curve::Fr;

fn plan(guard: Json, key: Json, value: Json) -> Plan {
    serde_json::from_value(json!({
        "schemaVersion": 1,
        "entrypoint": "inspect",
        "circuit": {"inputs": [], "outputs": []},
        "state": [
            {"kind": {"map": ["Native", "Native"]}, "name": "seeded", "sealed": true},
            {"kind": {"cell": "Bool"}, "name": "present", "sealed": true}
        ],
        "operations": [],
        "reads": [],
        "constructor": {
            "parameters": [],
            "initializers": [],
            "actions": [
                {
                    "kind": "mapInsert",
                    "state": "seeded",
                    "key": key,
                    "value": value,
                    "guard": guard
                },
                {
                    "kind": "initializeCellFromMapMember",
                    "state": "present",
                    "map": "seeded",
                    "key": {"tag": "constant", "value": "19"}
                }
            ]
        }
    }))
    .expect("valid constructor action plan")
}

fn map_and_presence(state: &ChargedState<Db>) -> (usize, bool) {
    let StateValue::Array(root) = state.get_ref() else {
        panic!("expected root state array")
    };
    let StateValue::Map(entries) = &*root.get(0).expect("seeded Map") else {
        panic!("expected seeded Map")
    };
    let present = root.get(1).expect("presence cell");
    let StateValue::Cell(present) = &*present else {
        panic!("expected Bool cell")
    };
    (entries.size(), &**present == &field_value(Fr::from(1u64)))
}

#[test]
fn ordered_map_insert_initializes_sealed_membership_cell() {
    let enabled = plan(
        json!({"tag": "bool", "value": true}),
        json!({"tag": "constant", "value": "19"}),
        json!({"tag": "constant", "value": "41"}),
    );
    let seeded = construct_state(&enabled, &BTreeMap::new()).unwrap();
    assert_eq!(map_and_presence(&seeded), (1, true));
    let StateValue::Array(root) = seeded.get_ref() else {
        panic!("expected root state array")
    };
    let StateValue::Map(entries) = &*root.get(0).expect("seeded Map") else {
        panic!("expected seeded Map")
    };
    let inserted = entries
        .get(&field_value(Fr::from(19u64)))
        .expect("inserted Map value");
    let StateValue::Cell(value) = &*inserted else {
        panic!("expected inserted scalar value")
    };
    assert_eq!(&**value, &field_value(Fr::from(41u64)));

    // A false guard skips both expression evaluations. These unknown references would
    // fail if the runtime evaluated either expression before checking the guard.
    let disabled = plan(
        json!({"tag": "bool", "value": false}),
        json!({"tag": "reference", "name": "missingKey"}),
        json!({"tag": "reference", "name": "missingValue"}),
    );
    let empty = construct_state(&disabled, &BTreeMap::new()).unwrap();
    assert_eq!(map_and_presence(&empty), (0, false));
}

#[test]
fn ordered_constructor_actions_reject_invalid_combinations_and_targets() {
    let valid = plan(
        json!({"tag": "bool", "value": true}),
        json!({"tag": "constant", "value": "19"}),
        json!({"tag": "constant", "value": "41"}),
    );

    let mut mixed_legacy = valid.clone();
    mixed_legacy
        .constructor
        .as_mut()
        .unwrap()
        .map_inserts
        .push(MapInsert {
            state: "seeded".into(),
            key: Expr::Constant { value: "20".into() },
            value: Expr::Constant { value: "42".into() },
        });
    let error = construct_state(&mixed_legacy, &BTreeMap::new())
        .err()
        .expect("legacy and ordered Map inserts must reject");
    assert!(error.to_string().contains("cannot be mixed"), "{error:#}");

    let mut duplicate_initializer = valid.clone();
    duplicate_initializer
        .constructor
        .as_mut()
        .unwrap()
        .initializers
        .push(Initializer {
            state: "present".into(),
            ty: "Bool".into(),
            value: InitialValue::ScalarExpression {
                expression: Expr::Bool { value: true },
            },
        });
    let error = construct_state(&duplicate_initializer, &BTreeMap::new())
        .err()
        .expect("duplicate initializers must reject");
    assert!(
        error
            .to_string()
            .contains("duplicate constructor initializer"),
        "{error:#}"
    );

    let mut invalid_reference = valid.clone();
    invalid_reference.constructor.as_mut().unwrap().actions[0] = ConstructorAction::MapInsert {
        state: "missing".into(),
        key: Expr::Constant { value: "19".into() },
        value: Expr::Constant { value: "41".into() },
        guard: Some(Expr::Bool { value: false }),
    };
    let error = construct_state(&invalid_reference, &BTreeMap::new())
        .err()
        .expect("unknown action targets must reject");
    assert!(error.to_string().contains("unknown constructor Map state"));

    let invalid_key_type = plan(
        json!({"tag": "bool", "value": true}),
        json!({"tag": "bool", "value": true}),
        json!({"tag": "constant", "value": "41"}),
    );
    let error = construct_state(&invalid_key_type, &BTreeMap::new())
        .err()
        .expect("Map insert key type mismatch must reject");
    assert!(
        error
            .to_string()
            .contains("constructor Map key type mismatch")
    );

    let mut too_many = valid;
    let insert = too_many.constructor.as_ref().unwrap().actions[0].clone();
    too_many.constructor.as_mut().unwrap().actions = vec![insert; 65];
    let error = construct_state(&too_many, &BTreeMap::new())
        .err()
        .expect("constructor action limit must reject");
    assert!(
        error
            .to_string()
            .contains("too many constructor collection actions")
    );
}
