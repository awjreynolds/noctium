#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use noctium_runtime::{check, construct_state, prepare, zkir::IrSource, Expr, Plan};
use serde_json::json;
use std::{collections::BTreeMap, fs::File, path::PathBuf};

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_GUARDED_CONSTRUCTOR_SET_DIR"]
fn guarded_constructor_set_matches_native_membership_read() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_GUARDED_CONSTRUCTOR_SET_DIR")
            .expect("NOCTIUM_GUARDED_CONSTRUCTOR_SET_DIR"),
    );
    let stem = "GuardedConstructorSet.inspect";
    let plan: Plan =
        serde_json::from_reader(File::open(directory.join(format!("{stem}.impact.json")))?)?;
    let relation = IrSource::load(File::open(directory.join(format!("{stem}.zkir")))?)?;
    let constructor = plan.constructor.as_ref().expect("constructor metadata");
    assert_eq!(constructor.set_inserts.len(), 1);
    assert!(constructor.set_inserts[0].guard.is_some());

    let owner = [7u8; 32];
    let owner_json = json!({"kind": "bytes", "values": owner.as_slice()});
    let inspection_inputs = BTreeMap::from([("owner".into(), owner_json.clone())]);
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = ContractAddress::default();

    for enabled in [false, true] {
        let constructor_arguments = BTreeMap::from([
            ("owner".into(), owner_json.clone()),
            ("enabled".into(), json!(enabled)),
        ]);
        let initial = construct_state(&plan, &constructor_arguments)?;
        let inspection = prepare(&plan, &inspection_inputs, &initial, parameters, address)?;
        assert_eq!(check(&inspection, &relation)?, inspection.activity_schedule);
        assert_eq!(
            inspection.returns_json(),
            BTreeMap::from([("present".into(), json!(enabled))])
        );
        assert_eq!(inspection.after.state.get_ref(), initial.get_ref());
    }

    // A false guard must skip key evaluation as well as insertion.
    let mut skipped_key_plan = plan.clone();
    skipped_key_plan.constructor.as_mut().unwrap().set_inserts[0].key = Expr::Reference {
        name: "missingKey".into(),
    };
    let disabled_arguments = BTreeMap::from([
        ("owner".into(), owner_json),
        ("enabled".into(), json!(false)),
    ]);
    let disabled_state = construct_state(&skipped_key_plan, &disabled_arguments)?;
    let disabled_inspection = prepare(
        &plan,
        &inspection_inputs,
        &disabled_state,
        parameters,
        address,
    )?;
    assert_eq!(
        check(&disabled_inspection, &relation)?,
        disabled_inspection.activity_schedule
    );
    assert_eq!(
        disabled_inspection.returns_json(),
        BTreeMap::from([("present".into(), json!(false))])
    );
    Ok(())
}
