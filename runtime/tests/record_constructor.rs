#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use noctium_runtime::{
    Plan, check, construct_state, constructor::ConstructorAction, prepare, zkir::IrSource,
};
use serde_json::json;
use std::{collections::BTreeMap, fs::File, path::PathBuf};

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
