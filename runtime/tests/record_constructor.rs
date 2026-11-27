#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use noctium_runtime::{
    Expr, Instruction, Plan, check, construct_state, constructor::ConstructorAction, field_value,
    prepare, zkir::IrSource,
};
use onchain_runtime::state::StateValue;
use serde_json::json;
use serialize::Serializable;
use std::{collections::BTreeMap, fs::File, path::PathBuf};
use transient_crypto::curve::Fr;

#[test]
#[ignore = "requires fresh SealedRecordCell artifacts in NOCTIUM_SEALED_RECORD_CELL_DIR"]
fn sealed_record_cell_preserves_seeded_fields_and_rejects_mutation() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_SEALED_RECORD_CELL_DIR").expect("artifact directory"),
    );
    let artifacts = |entry: &str| -> anyhow::Result<(Plan, IrSource)> {
        let stem = format!("SealedRecordCell.{entry}");
        Ok((
            serde_json::from_reader(File::open(directory.join(format!("{stem}.impact.json")))?)?,
            IrSource::load(File::open(directory.join(format!("{stem}.zkir")))?)?,
        ))
    };
    let (inspect, inspect_relation) = artifacts("inspect")?;
    let (touch, touch_relation) = artifacts("touch")?;
    let position = inspect
        .state
        .iter()
        .position(|slot| slot.name == "position")
        .unwrap();
    let marker = inspect
        .state
        .iter()
        .position(|slot| slot.name == "marker")
        .unwrap();
    assert!(inspect.state[position].sealed);
    assert!(matches!(
        inspect.constructor.as_ref().unwrap().actions.as_slice(),
        [ConstructorAction::InitializeRecordCell { state, .. }] if state == "position"
    ));
    let inputs = BTreeMap::new();
    let arguments = BTreeMap::from([
        ("amount".into(), json!("241")),
        ("count".into(), json!("513")),
        ("active".into(), json!(true)),
    ]);
    let initial = construct_state(&inspect, &arguments)?;
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = ContractAddress::default();
    let read = prepare(&inspect, &inputs, &initial, params, address)?;
    check(&read, &inspect_relation)?;
    assert_eq!(read.returns_json(), arguments);
    assert_eq!(read.after.state, initial);

    let changed = prepare(&touch, &inputs, &initial, params, address)?;
    check(&changed, &touch_relation)?;
    let (StateValue::Array(before), StateValue::Array(after)) =
        (initial.get_ref(), changed.after.state.get_ref())
    else {
        panic!("expected root state arrays");
    };
    let mut before_bytes = Vec::new();
    let mut after_bytes = Vec::new();
    before.get(position).unwrap().serialize(&mut before_bytes)?;
    after.get(position).unwrap().serialize(&mut after_bytes)?;
    assert_eq!(after_bytes, before_bytes);
    let StateValue::Cell(marker) = &*after.get(marker).unwrap() else {
        panic!("expected a marker Cell");
    };
    assert_eq!(&**marker, &field_value(Fr::from(37u64)));

    let schema = inspect
        .operations
        .iter()
        .find_map(|op| match op {
            Instruction::PopeqFields { schema, .. } => Some(schema.clone()),
            _ => None,
        })
        .expect("record schema from the checked read");
    let mut forged = touch;
    forged.operations = vec![
        Instruction::Push {
            storage: false,
            expression: Expr::Constant {
                value: position.to_string(),
            },
            alignment: "field".into(),
        },
        Instruction::PushFields {
            storage: true,
            schema,
            expressions: vec![
                Expr::Uint {
                    maximum: "255".into(),
                    value: "1".into(),
                },
                Expr::Uint {
                    maximum: "65535".into(),
                    value: "2".into(),
                },
                Expr::Bool { value: false },
            ],
        },
        Instruction::Insert { n: 1 },
    ];
    let error = prepare(&forged, &inputs, &initial, params, address)
        .err()
        .expect("forged sealed record write must reject");
    assert!(error.to_string().contains("sealed"), "{error:#}");
    forged.state[position].sealed = false;
    let ordinary_write = prepare(&forged, &inputs, &initial, params, address)?;
    assert_ne!(ordinary_write.after.state, initial);
    Ok(())
}

#[test]
#[ignore = "requires fresh GuardedRecordConstructor.inspect artifacts in NOCTIUM_RECORD_CONSTRUCTOR_DIR"]
fn record_constructor_initializes_cell_and_map_with_guard() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_RECORD_CONSTRUCTOR_DIR").expect("NOCTIUM_RECORD_CONSTRUCTOR_DIR"),
    );
    let stem = "GuardedRecordConstructor.inspect";
    let plan: Plan =
        serde_json::from_reader(File::open(directory.join(format!("{stem}.impact.json")))?)?;
    let relation = IrSource::load(File::open(directory.join(format!("{stem}.zkir")))?)?;
    let actions = &plan
        .constructor
        .as_ref()
        .expect("constructor metadata")
        .actions;
    assert_eq!(actions.len(), 2);
    assert!(matches!(
        &actions[0],
        ConstructorAction::InsertRecordMap { state, guard: None, .. } if state == "positions"
    ));
    assert!(matches!(
        &actions[1],
        ConstructorAction::InsertRecordMap { state, guard: Some(_), .. } if state == "positions"
    ));

    let owner = [19u8; 32];
    let other = [23u8; 32];
    let owner_json = json!({"kind": "bytes", "values": owner.as_slice()});
    let other_json = json!({"kind": "bytes", "values": other.as_slice()});
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = ContractAddress::default();

    for enabled in [false, true] {
        let arguments = BTreeMap::from([
            ("owner".into(), owner_json.clone()),
            ("amount".into(), json!("19")),
            ("count".into(), json!("7")),
            ("active".into(), json!(true)),
            ("enabled".into(), json!(enabled)),
        ]);
        let initial = construct_state(&plan, &arguments)?;
        let inputs = BTreeMap::from([("owner".into(), owner_json.clone())]);
        let execution = prepare(&plan, &inputs, &initial, parameters, address)?;
        assert_eq!(check(&execution, &relation)?, execution.activity_schedule);
        let returns = execution.returns_json();
        assert_eq!(
            returns.get("mapAmount"),
            Some(&json!(if enabled { "19" } else { "0" }))
        );
        assert_eq!(returns.get("mapCount"), Some(&json!("7")));
        assert_eq!(returns.get("mapActive"), Some(&json!(enabled)));
        assert_eq!(execution.after.state, initial);

        let missing = BTreeMap::from([("owner".into(), other_json.clone())]);
        assert!(prepare(&plan, &missing, &initial, parameters, address).is_err());
    }
    Ok(())
}
